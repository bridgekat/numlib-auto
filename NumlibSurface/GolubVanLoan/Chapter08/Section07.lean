import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Numlib.Eigen.Pencil
import Numlib.Eigen.SymmetricPencil
import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter04.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter06.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section03
import NumlibSurface.GolubVanLoan.Chapter08.Section01

/-!
# Golub–Van Loan §8.7: generalized eigenvalue problems with symmetry

Surface file for [golub2013matrix] §8.7: the symmetric-definite problem (congruence invariance,
Theorem 8.7.1, Corollary 8.7.2, the Crawford number (8.7.4) and a corrected Theorem 8.7.3), the
generalized Rayleigh quotient ((8.7.5)–(8.7.7)), the generalized singular value decomposition
(the column relations of §8.7.4, the subspace identity after Algorithm 8.7.2), the Kogbetliantz
`2 × 2` facts (§8.7.7), and the quadratic eigenvalue problem ((8.7.12)–(8.7.18)).

## Conventions

`λ(A, B)` is `Matrix.pencilSpectrum A B` (`{λ | det(A - λB) = 0}`), a symmetric-definite pencil
has `A` symmetric and `B` positive definite (`Matrix.PosDef`). The quadratic eigenvalue problem is
stated over `ℂ`, where `λ` and `x` live; a real symmetric (skew-symmetric, positive definite)
matrix is in particular a complex Hermitian (skew-Hermitian, positive definite) one.

Algorithms 8.7.1–8.7.2 call the programs of chapters 3–5 (Cholesky, forward and back
substitution, modified Gram–Schmidt) and take the two steps with no exact program — the symmetric
Schur decomposition and the CS decomposition — as monadic parameters whose specifications the spec
theorems assume (convention 5); the triangular solves with a matrix right-hand side run column by
column. `(8.7.8)` is stated against chapter 7's orthogonal iteration. Theorem 8.7.4 restates
chapter 6's Theorem 6.1.1, whose `p = max(r − m₂, 0)` vanishes for a tall `B`.

## Readings and errata

(1) Theorem 8.7.3 is false as printed (`theorem_8_7_3_counterexample`); the corrected bound is
`sin |arctan λ_i - arctan μ_i| ≤ ε / c(A, B)`, with `B + E_B` positive definite assumed, and
(8.7.4) needs the square root. (2) §8.7.7 should read `U₁ᵀ F = Σ (U₂ᵀ G)`. (3) §8.7.9: the
gyroscopic eigenvalues are purely imaginary only when `K` is positive semidefinite
(`gyroscopic_counterexample`).

## Not formalized

The overdamping theorem of §8.7.9 (quoted from Duffin/Veselić), the stationary-value
characterization of generalized singular values, §8.7.8's product and restricted SVDs, §8.7.6's
accuracy discussion.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### §8.7.1 Mathematical background -/

/-- **§8.7.1, congruence.** For nonsingular `X`, `A - λB` is singular iff `XᵀAX - λXᵀBX` is:
`λ(A, B) = λ(XᵀAX, XᵀBX)`. -/
theorem pencil_congruence (A B : Matrix (Fin n) (Fin n) ℝ) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsUnit X.det) : pencilSpectrum (Xᵀ * A * X) (Xᵀ * B * X) = pencilSpectrum A B := by
  have hXu : IsUnit X := (isUnit_iff_isUnit_det X).2 hX
  have hXt : IsUnit Xᵀ := (isUnit_iff_isUnit_det Xᵀ).2 (by rw [det_transpose]; exact hX)
  exact pencilSpectrum_mul_mul_of_isUnit A B hXt hXu

/-- **Theorem 8.7.1** with (8.7.3). For symmetric `A`, `B` and `C(μ) = μA + (1 - μ)B`, if some
`μ ∈ [0, 1]` has `C(μ)` positive semidefinite with `null(C(μ)) = null(A) ∩ null(B)`, there is a
nonsingular `X` with `XᵀAX` and `XᵀBX` both diagonal. -/
theorem theorem_8_7_1 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.IsSymm) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hC : (μ • A + (1 - μ) • B).PosSemidef)
    (hker : ∀ x, (μ • A + (1 - μ) • B) *ᵥ x = 0 ↔ A *ᵥ x = 0 ∧ B *ᵥ x = 0) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, IsUnit X ∧ ∃ a b : Fin n → ℝ,
      Xᵀ * A * X = diagonal a ∧ Xᵀ * B * X = diagonal b := by
  obtain ⟨X, hX, a, b, ha, hb⟩ := exists_isUnit_conj_diagonal_of_posSemidef_combination (𝕜 := ℝ)
    (isHermitian_iff_isSymm.2 hA) (isHermitian_iff_isSymm.2 hB) hμ (by simpa using hC)
    (by simpa using hker)
  refine ⟨X, hX, a, b, ?_, ?_⟩
  · simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using ha
  · simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hb

/-- **Corollary 8.7.2.** If `A - λB` is symmetric-definite, there is a nonsingular
`X = [x_1 | ⋯ | x_n]` with `XᵀAX = diag(a)`, `XᵀBX = diag(b)`, and `A x_i = λ_i B x_i` with
`λ_i = a_i / b_i`. -/
theorem corollary_8_7_2 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, IsUnit X ∧ ∃ a b : Fin n → ℝ,
      Xᵀ * A * X = diagonal a ∧ Xᵀ * B * X = diagonal b ∧
        ∀ i, A *ᵥ X.col i = (a i / b i) • (B *ᵥ X.col i) := by
  obtain ⟨M, d, hM, hMB, hMA, -⟩ := exists_simultaneous_diagonalization (𝕜 := ℝ)
    (isHermitian_iff_isSymm.2 hA) hB
  have hMA' : star M * A * M = diagonal d := by simpa using hMA
  refine ⟨M, hM, d, 1, ?_, ?_, fun i => ?_⟩
  · simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hMA'
  · simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hMB
  · have h := (hasPencilEigenvector_col_of_conj_eq_diagonal hM hMB hMA' i).2
    simpa using h

/-- **(8.7.4), the Crawford number** `c(A, B) = min_{‖x‖₂ = 1} √((xᵀAx)² + (xᵀBx)²)` (with the
square root the book's display omits). -/
noncomputable def crawfordNumber (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.crawfordNumber A B

/-- **Theorem 8.7.3, corrected.** For a symmetric-definite `A - λB` with eigenvalues
`λ_1 ≥ ⋯ ≥ λ_n`, symmetric `E_A`, `E_B` with `ε = √(‖E_A‖₂² + ‖E_B‖₂²) < c(A, B)` and `B + E_B`
positive definite, the eigenvalues `μ_1 ≥ ⋯ ≥ μ_n` of `(A + E_A) - λ(B + E_B)` satisfy
`sin |arctan λ_i - arctan μ_i| ≤ ε / c(A, B)`. -/
theorem theorem_8_7_3 {A B EA EB : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef)
    (hA' : (A + EA).IsSymm) (hB' : (B + EB).PosDef)
    (hε : Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) < crawfordNumber A B) (i : Fin n) :
    Real.sin |Real.arctan (pencilEigenvalues (isHermitian_iff_isSymm.2 hA) hB
          (Fin.cast (Fintype.card_fin n).symm i)) -
        Real.arctan (pencilEigenvalues (isHermitian_iff_isSymm.2 hA') hB'
          (Fin.cast (Fintype.card_fin n).symm i))| ≤
      Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) / crawfordNumber A B :=
  sin_abs_arctan_pencilEigenvalues_sub_le _ hB _ hB' hε _

/-- **Theorem 8.7.3 is false as printed.** For `n = 1`, `A = 0`, `B = 1`, `E_A = √3/4`,
`E_B = -1/4`: `ε² = ‖E_A‖₂² + ‖E_B‖₂² = 1/4 < 1 = c(A, B)`, `λ(A, B) = {0}`,
`λ(A + E_A, B + E_B) = {1/√3}`, and `|arctan 0 - arctan (1/√3)| = π/6 > arctan(ε / c(A, B))`. -/
theorem theorem_8_7_3_counterexample :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let B : Matrix (Fin 1) (Fin 1) ℝ := 1
    let EA : Matrix (Fin 1) (Fin 1) ℝ := !![Real.sqrt 3 / 4]
    let EB : Matrix (Fin 1) (Fin 1) ℝ := !![-1 / 4]
    lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2 = 1 / 4 ∧ crawfordNumber A B = 1 ∧
      pencilSpectrum A B = {0} ∧ pencilSpectrum (A + EA) (B + EB) = {(Real.sqrt 3)⁻¹} ∧
      ¬ |Real.arctan 0 - Real.arctan (Real.sqrt 3)⁻¹| ≤
        Real.arctan (Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) / crawfordNumber A B) := by
  intro A B EA EB
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := by positivity
  -- the norm of a `1 × 1` matrix
  have hnorm : ∀ t : ℝ, lpOpNorm 2 (!![t] : Matrix (Fin 1) (Fin 1) ℝ) = |t| := fun t => by
    have hd : (!![t] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => t := by
      ext i j; fin_cases i; fin_cases j; rfl
    rw [hd, lpOpNorm_diagonal, ciSup_const, Real.norm_eq_abs]
  have hε : lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2 = 1 / 4 := by
    simp only [EA, EB, hnorm, sq_abs, div_pow, hs3]
    norm_num
  have hc : crawfordNumber A B = 1 := by
    have hne : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
      (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
    have hterm : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
        Real.sqrt (reQuadForm A x ^ 2 + reQuadForm B x ^ 2) = 1 := fun x => by
      have hx : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 := by simp
      have h1 : reQuadForm B x = 1 := by
        simp only [reQuadForm, B, one_mulVec, star_trivial, RCLike.re_to_real]
        rw [dotProduct_self_eq_norm_sq, WithLp.toLp_ofLp, hx, one_pow]
      have h0 : reQuadForm A x = 0 := by simp [reQuadForm, A]
      rw [h0, h1]
      norm_num
    rw [crawfordNumber, Matrix.crawfordNumber, iInf_congr hterm, ciInf_const]
  have hspec1 : pencilSpectrum A B = {0} := by
    ext μ
    simp [mem_pencilSpectrum_iff_det, A, B]
  have hspec2 : pencilSpectrum (A + EA) (B + EB) = {(Real.sqrt 3)⁻¹} := by
    ext μ
    simp only [mem_pencilSpectrum_iff_det, A, B, EA, EB, det_fin_one, Set.mem_singleton_iff]
    simp only [zero_add, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, one_apply_eq,
      of_apply, cons_val', empty_val', cons_val_fin_one, smul_eq_mul]
    constructor
    · intro h
      field_simp
      nlinarith [hs3]
    · rintro rfl
      field_simp
      nlinarith [hs3]
  refine ⟨hε, hc, hspec1, hspec2, ?_⟩
  rw [hε, hc, div_one, show Real.sqrt (1 / 4) = 1 / 2 by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num,
    Real.arctan_zero, zero_sub, abs_neg, Real.arctan_inv_sqrt_three,
    abs_of_pos (by positivity), not_le, ← Real.arctan_inv_sqrt_three]
  refine Real.arctan_lt_arctan_iff.2 ?_
  rw [one_div, inv_lt_inv₀ (by norm_num) hs3p]
  nlinarith [hs3]

/-! ### §8.7.2 Methods for the symmetric-definite problem -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The triangular solves of Algorithms 8.7.1–8.7.2, one right-hand side at a time: column `j` of
`Y` is overwritten by `solve (Y(:, j))`. -/
private def solveCols (solve : (Fin n → ℝ) → M (Fin n → ℝ)) (Y : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (Z : Matrix (Fin n) (Fin n) ℝ) j => do
    let z ← solve (Y.col j)
    pure (Z.updateCol j z)) Y

/-- **Algorithm 8.7.1** (symmetric-definite `Ax = λBx`): "Given `A = Aᵀ` and `B = Bᵀ` positive
definite, the following algorithm computes a nonsingular `X` such that `XᵀAX = diag(a₁, …, a_n)`
and `XᵀBX = I_n`."
```
Compute the Cholesky factorization B = GGᵀ using Algorithm 4.2.1.
Compute C = G⁻¹AG⁻ᵀ.
Use the symmetric QR algorithm to compute the Schur decomposition QᵀCQ = diag(a₁, …, a_n).
Set X = G⁻ᵀQ.
```
(The book cites "Algorithm 4.2.2", a misprint.) `G` is the lower triangle of chapter 4's
Algorithm 4.2.1 (an exact copy); `C` is two column-by-column forward substitutions (chapter 3's
Algorithm 3.1.1), `Y = G⁻¹ A` and `C = G⁻¹ Yᵀ` (`A` symmetric); `X` is back substitution
(Algorithm 3.1.2) on `Gᵀ`, column by column. The symmetric Schur decomposition is the monadic
parameter `schur` (convention 5): Algorithm 8.3.3 returns a diagonal matrix only up to its
deflation perturbation. -/
noncomputable def algorithm_8_7_1
    (schur : Matrix (Fin n) (Fin n) ℝ → M (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)))
    (A B : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) := do
  let F ← Chapter04.algorithm_4_2_1 rnd B
  let G := F - F.strictUpper
  let Y ← solveCols (Chapter03.algorithm_3_1_1 rnd G) A
  let C ← solveCols (Chapter03.algorithm_3_1_1 rnd G) Yᵀ
  let Qa ← schur C
  let X ← solveCols (Chapter03.algorithm_3_1_2 rnd Gᵀ) Qa.1
  pure (X, Qa.2)

end Programs

/-- The column solves in exact arithmetic. -/
private theorem solveCols_id (solve : (Fin n → ℝ) → Id (Fin n → ℝ))
    (Y : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (solveCols solve Y) = of fun i j => Id.run (solve (Y.col j)) i := by
  have key : ∀ (l : List (Fin n)) (Z : Matrix (Fin n) (Fin n) ℝ), l.Nodup →
      l.foldl (fun Z j => Z.updateCol j (Id.run (solve (Y.col j)))) Z =
        of fun i j => if j ∈ l then Id.run (solve (Y.col j)) i else Z i j := by
    intro l
    induction l with
    | nil => intro Z _; ext i j; simp
    | cons a l ih =>
      intro Z hl
      rw [List.foldl_cons, ih _ (List.nodup_cons.1 hl).2]
      ext i j
      simp only [of_apply, updateCol_apply, List.mem_cons]
      by_cases hja : j = a
      · subst hja; simp [(List.nodup_cons.1 hl).1]
      · simp [hja]
  unfold solveCols
  rw [show (fun (Z : Matrix (Fin n) (Fin n) ℝ) j =>
      (do let z ← solve (Y.col j); pure (Z.updateCol j z) : Id _)) =
      fun Z j => pure (Z.updateCol j (Id.run (solve (Y.col j)))) from rfl, List.foldlM_pure,
    key _ _ (List.nodup_finRange n)]
  ext i j
  simp

/-- If every column solve inverts `G`, the column solves compute `G⁻¹ Y`: `G X = Y`. -/
private theorem mul_solveCols {G : Matrix (Fin n) (Fin n) ℝ}
    {solve : (Fin n → ℝ) → Id (Fin n → ℝ)} (h : ∀ b, G *ᵥ Id.run (solve b) = b)
    (Y : Matrix (Fin n) (Fin n) ℝ) : G * Id.run (solveCols solve Y) = Y := by
  ext i j
  have := congrFun (h (Y.col j)) i
  rw [solveCols_id]
  simpa [mul_apply, mulVec, dotProduct] using this

/-- **Algorithm 8.7.1, exact semantics**: if `schur` returns an orthogonal `Q` and `a` with
`QᵀCQ = diag(a)` for symmetric `C`, then for symmetric `A` and positive definite `B` the output
`(X, a)` has `XᵀAX = diag(a)` and `XᵀBX = I`. The Cholesky step is chapter 4's Algorithm 4.2.1
(`G = Matrix.cholesky B`, lower triangular with positive diagonal, `B = GGᵀ`), the solves are
chapter 3's Algorithms 3.1.1–3.1.2: `GY = A`, `GC = Yᵀ`, `GᵀX = Q`, so `A = GCGᵀ` and
`XᵀAX = QᵀCQ`, `XᵀBX = QᵀQ`. -/
theorem algorithm_8_7_1_spec
    (schur : Matrix (Fin n) (Fin n) ℝ → Id (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)))
    (hschur : ∀ C : Matrix (Fin n) (Fin n) ℝ, C.IsSymm →
      (Id.run (schur C)).1 ∈ orthogonalGroup (Fin n) ℝ ∧
        (Id.run (schur C)).1ᵀ * C * (Id.run (schur C)).1 = diagonal (Id.run (schur C)).2)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef) :
    (Id.run (algorithm_8_7_1 pure schur A B)).1ᵀ * A * (Id.run (algorithm_8_7_1 pure schur A B)).1 =
        diagonal (Id.run (algorithm_8_7_1 pure schur A B)).2 ∧
      (Id.run (algorithm_8_7_1 pure schur A B)).1ᵀ * B *
        (Id.run (algorithm_8_7_1 pure schur A B)).1 = 1 := by
  obtain ⟨hFG, hBG⟩ := Chapter04.algorithm_4_2_1_spec hB
  set F := Id.run (Chapter04.algorithm_4_2_1 pure B)
  set G := F - F.strictUpper with hGdef
  have hGl : G.IsLowerTriangular := by rw [hFG]; exact isLowerTriangular_cholesky B
  have hGd : ∀ i, G i i ≠ 0 := fun i => by
    have := (isCholesky_cholesky hB).diag_pos i
    rw [hFG]
    simpa using this.ne'
  have hGu : IsUnit G := by
    rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular G hGl]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hGd i)
  have hGtu : Gᵀ.IsUpperTriangular := hGl.transpose_isUpperTriangular
  set Y := Id.run (solveCols (Chapter03.algorithm_3_1_1 pure G) A)
  set C := Id.run (solveCols (Chapter03.algorithm_3_1_1 pure G) Yᵀ)
  set Qa := Id.run (schur C)
  set X := Id.run (solveCols (Chapter03.algorithm_3_1_2 pure Gᵀ) Qa.1)
  have hrun : Id.run (algorithm_8_7_1 pure schur A B) = (X, Qa.2) := rfl
  rw [hrun]
  have hY : G * Y = A := mul_solveCols (fun b => Chapter03.algorithm_3_1_1_spec hGl hGd b) A
  have hC : G * C = Yᵀ := mul_solveCols (fun b => Chapter03.algorithm_3_1_1_spec hGl hGd b) Yᵀ
  have hX : Gᵀ * X = Qa.1 := mul_solveCols (fun b => Chapter03.algorithm_3_1_2_spec hGtu
    (fun i => by simpa using hGd i) b) Qa.1
  have hAGC : A = G * C * Gᵀ := by
    rw [hC, ← transpose_mul, hY, hA.eq]
  have hCs : C.IsSymm := by
    have h1 : G * Cᵀ * Gᵀ = G * C * Gᵀ := by
      rw [← hAGC]
      conv_rhs => rw [← hA.eq, hAGC]
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    have h2 := hGu.mul_left_cancel (by simpa only [Matrix.mul_assoc] using h1)
    exact ((isUnit_transpose G).2 hGu).mul_right_cancel h2
  obtain ⟨hQ, hQC⟩ := hschur C hCs
  have hQQ : Qa.1ᵀ * Qa.1 = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  refine ⟨?_, ?_⟩
  · rw [hAGC, show Xᵀ * (G * C * Gᵀ) * X = (Gᵀ * X)ᵀ * C * (Gᵀ * X) by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc], hX, hQC]
  · rw [hBG, show Xᵀ * (G * Gᵀ) * X = (Gᵀ * X)ᵀ * (Gᵀ * X) by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc], hX, hQQ]

/-- **§8.7.2, after Algorithm 8.7.1**: `λ(A, B) = λ(A, GGᵀ) = λ(G⁻¹AG⁻ᵀ, I) = λ(C) =
{a₁, …, a_n}`: with `G = Matrix.cholesky B` (so `B = GGᵀ`), `λ(A, B)` is the spectrum of
`G⁻¹ A G⁻ᵀ` (`pencil_congruence` with `X = G⁻ᵀ`), and, for the output `(X, a)` of Algorithm 8.7.1
with a correct Schur step, the set of the `a_i`. -/
theorem pencil_eq_cholesky_spectrum
    (schur : Matrix (Fin n) (Fin n) ℝ → Id (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)))
    (hschur : ∀ C : Matrix (Fin n) (Fin n) ℝ, C.IsSymm →
      (Id.run (schur C)).1 ∈ orthogonalGroup (Fin n) ℝ ∧
        (Id.run (schur C)).1ᵀ * C * (Id.run (schur C)).1 = diagonal (Id.run (schur C)).2)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hB : B.PosDef) :
    pencilSpectrum A B = spectrum ℝ ((cholesky B)⁻¹ * A * ((cholesky B)⁻¹)ᵀ) ∧
      pencilSpectrum A B = Set.range (Id.run (algorithm_8_7_1 pure schur A B)).2 := by
  obtain ⟨hFG, hBG⟩ := Chapter04.algorithm_4_2_1_spec hB
  rw [hFG] at hBG
  set G := cholesky B
  have hGd : IsUnit G.det := by
    have h := congrArg det hBG
    rw [det_mul, det_transpose] at h
    exact isUnit_iff_ne_zero.2 fun h0 => hB.det_pos.ne' (by rw [h, h0, zero_mul])
  refine ⟨?_, ?_⟩
  · have hXd : IsUnit (G⁻¹)ᵀ.det := by
      rw [det_transpose]; exact isUnit_nonsing_inv_det G hGd
    rw [← pencil_congruence A B hXd, transpose_transpose, hBG,
      show G⁻¹ * (G * Gᵀ) * G⁻¹ᵀ = (G⁻¹ * G) * (G⁻¹ * G)ᵀ by
        simp only [transpose_mul, Matrix.mul_assoc],
      nonsing_inv_mul _ hGd, transpose_one, Matrix.mul_one, pencilSpectrum_one]
  · obtain ⟨h1, h2⟩ := algorithm_8_7_1_spec schur hschur hA hB
    set X := (Id.run (algorithm_8_7_1 pure schur A B)).1
    have hXd : IsUnit X.det := by
      have h := congrArg det h2
      rw [det_mul, det_mul, det_transpose, det_one] at h
      exact IsUnit.of_mul_eq_one (B.det * X.det) (by rw [← h]; ring)
    rw [← pencil_congruence A B hXd, h1, h2, pencilSpectrum_one, spectrum_diagonal]

/-! ### §8.7.2 The generalized Rayleigh quotient -/

/-- **(8.7.5), the generalized Rayleigh quotient iteration**: `x_0` given; `μ_k = x_kᵀAx_k /
x_kᵀBx_k`, `(A - μ_k B) z_{k+1} = B x_k`, `x_{k+1} = z_{k+1} / ‖z_{k+1}‖₂` (the solve is
`Matrix.inv`, total). -/
noncomputable def generalizedRayleighQuotientIteration (A B : Matrix (Fin n) (Fin n) ℝ)
    (x₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 =>
    let x := generalizedRayleighQuotientIteration A B x₀ k
    let z := (A - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) • B)⁻¹ *ᵥ (B *ᵥ x)
    ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))‖⁻¹ • z

/-- **(8.7.5) is Rayleigh quotient iteration on `B⁻¹A`**: for nonsingular `B`, each step solves
`(B⁻¹A - μ_k I) z_{k+1} = x_k` — inverse iteration (7.6.1) on `B⁻¹A` with the generalized Rayleigh
quotient `μ_k = x_kᵀAx_k / x_kᵀBx_k` as shift — and normalizes. -/
theorem generalizedRayleighQuotientIteration_succ {A B : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsUnit B.det) (x₀ : Fin n → ℝ) (k : ℕ) :
    let x := generalizedRayleighQuotientIteration A B x₀ k
    let z := (B⁻¹ * A - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) • 1)⁻¹ *ᵥ x
    generalizedRayleighQuotientIteration A B x₀ (k + 1) =
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))‖⁻¹ • z := by
  intro x z
  have key : ∀ μ : ℝ, (A - μ • B)⁻¹ *ᵥ (B *ᵥ x) = (B⁻¹ * A - μ • 1)⁻¹ *ᵥ x := fun μ => by
    have e : A - μ • B = B * (B⁻¹ * A - μ • 1) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, mul_nonsing_inv B hB, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one]
    rw [e, Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul B hB,
      Matrix.mul_one]
  change ‖(WithLp.toLp 2 ((A - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) • B)⁻¹ *ᵥ (B *ᵥ x)) :
      EuclideanSpace ℝ (Fin n))‖⁻¹ • ((A - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) • B)⁻¹ *ᵥ (B *ᵥ x)) = _
  rw [key]

/-- **(8.7.6)–(8.7.7).** For positive definite `B` and `x ≠ 0`, `λ = xᵀAx / xᵀBx` minimizes
`f(λ) = ‖Ax - λBx‖_B`, `‖z‖_B² = zᵀB⁻¹z` (`A` need not be symmetric). -/
theorem equation_8_7_7 (A : Matrix (Fin n) (Fin n) ℝ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) {x : Fin n → ℝ} (hx : x ≠ 0) :
    IsMinOn (fun μ : ℝ => Real.sqrt ((A *ᵥ x - μ • B *ᵥ x) ⬝ᵥ B⁻¹ *ᵥ (A *ᵥ x - μ • B *ᵥ x)))
      Set.univ ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) :=
  fun _ hμ => Real.sqrt_le_sqrt (isMinOn_pencil_residual (A := A) hB hx hμ)

/-- **(8.7.8), the generalized orthogonal iteration** (`Q₀ᵀQ₀ = I_p`; for `k ≥ 1`: solve
`B Z_k = A Q_{k-1}`, `Z_k = Q_k R_k` a thin QR factorization) "is mathematically equivalent to
(7.3.6) with `A` replaced by `B⁻¹A`": for nonsingular `B`, a sequence `Q_k` with triangular factors
`R_k` satisfies (8.7.8) for some `Z_k` iff each `(Q_k, R_k)` is a thin QR factorization of
`B⁻¹ A Q_{k-1}`, and then `Q_k` is an orthogonal iteration (chapter 7's (7.3.6)) of `B⁻¹ A`. -/
theorem equation_8_7_8 {p : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hB : IsUnit B.det)
    (Q : ℕ → Matrix (Fin n) (Fin p) ℝ) (R : ℕ → Matrix (Fin p) (Fin p) ℝ) :
    ((∃ Z : ℕ → Matrix (Fin n) (Fin p) ℝ, ∀ k,
        B * Z (k + 1) = A * Q k ∧ IsThinQR (Z (k + 1)) (Q (k + 1)) (R (k + 1))) ↔
      ∀ k, IsThinQR (B⁻¹ * A * Q k) (Q (k + 1)) (R (k + 1))) ∧
    ((Q 0)ᵀ * Q 0 = 1 → (∀ k, IsThinQR (B⁻¹ * A * Q k) (Q (k + 1)) (R (k + 1))) →
      Chapter07.orthogonalIteration (B⁻¹ * A) Q) := by
  refine ⟨⟨fun ⟨Z, hZ⟩ k => ?_, fun h => ⟨fun k => B⁻¹ * A * Q (k - 1), fun k => ⟨?_, ?_⟩⟩⟩,
    fun h0 h => ⟨by rwa [conjTranspose_eq_transpose_of_trivial], fun k => ⟨R (k + 1), h k⟩⟩⟩
  · obtain ⟨h1, h2⟩ := hZ k
    have hZk : Z (k + 1) = B⁻¹ * A * Q k := by
      rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hB, Matrix.one_mul]
    rwa [hZk] at h2
  · simp only [Nat.add_sub_cancel]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hB, Matrix.one_mul]
  · simpa only [Nat.add_sub_cancel] using h k

/-! ### §8.7.4 The generalized singular value problem -/

/-- **Theorem 8.7.4 (Tall Rectangular Version).** "If `A ∈ ℝ^{m₁×n}` and `B ∈ ℝ^{m₂×n}` have at
least as many rows as columns, then there exists an orthogonal matrix `U₁ ∈ ℝ^{m₁×m₁}`, an
orthogonal matrix `U₂ ∈ ℝ^{m₂×m₂}`, and a nonsingular matrix `X ∈ ℝ^{n×n}` such that
`U₁ᵀAX = diag(α₁, …, α_n)`, `U₂ᵀBX = diag(β₁, …, β_n)`." The diagonals are `rectDiagonal α` and
`rectDiagonal β`. Chapter 6's Theorem 6.1.1, where `p = max(r − m₂, 0) = 0` because
`r = rank [A; B] ≤ n ≤ m₂`. -/
theorem theorem_8_7_4 {m₁ m₂ : ℕ} (hm₁ : n ≤ m₁) (hm₂ : n ≤ m₂) (A : Matrix (Fin m₁) (Fin n) ℝ)
    (B : Matrix (Fin m₂) (Fin n) ℝ) :
    ∃ (U₁ : Matrix (Fin m₁) (Fin m₁) ℝ) (U₂ : Matrix (Fin m₂) (Fin m₂) ℝ)
      (X : Matrix (Fin n) (Fin n) ℝ) (α β : ℕ → ℝ),
      U₁ ∈ orthogonalGroup (Fin m₁) ℝ ∧ U₂ ∈ orthogonalGroup (Fin m₂) ℝ ∧ IsUnit X.det ∧
      U₁ᵀ * A * X = rectDiagonal α ∧ U₂ᵀ * B * X = rectDiagonal β := by
  obtain ⟨U₁, U₂, X, α, β, hU₁, hU₂, hX, hA, hB, -, -⟩ := Chapter06.theorem_6_1_1 hm₁ A B
  have hp : (fromRows A B).rank - m₂ = 0 :=
    Nat.sub_eq_zero_of_le (((rank_le_card_width _).trans_eq (Fintype.card_fin n)).trans hm₂)
  refine ⟨U₁, U₂, X, α, β, hU₁, hU₂, (isUnit_iff_isUnit_det X).1 hX, hA, ?_⟩
  rwa [hp, shiftedRectDiagonal_zero] at hB

/-- **§8.7.4, after Theorem 8.7.4.** From a GSVD `U₁ᵀ A X = D_A = diag(α)`,
`U₂ᵀ B X = D_B = diag(β)` (`U₁`, `U₂` orthogonal, `X` nonsingular, `m₁, m₂ ≥ n`):
`A x_k = α_k u_k`, `B x_k = β_k v_k`;
`Xᵀ (AᵀA - λ BᵀB) X = diag(α_k² - λ β_k²)`; every `x_k` with `β_k ≠ 0` is a generalized
eigenvector of `AᵀA - λ BᵀB` for `λ = (α_k/β_k)²`; and when all `β_k ≠ 0` the eigenvalues of the
pencil are exactly the squares of the generalized singular values `σ(A, B) = {α_k/β_k}`. -/
theorem gsvd_columns_and_pencil {m₁ m₂ : ℕ} {A : Matrix (Fin m₁) (Fin n) ℝ}
    {B : Matrix (Fin m₂) (Fin n) ℝ} (hm₁ : n ≤ m₁) (hm₂ : n ≤ m₂)
    {U₁ : Matrix (Fin m₁) (Fin m₁) ℝ} {U₂ : Matrix (Fin m₂) (Fin m₂) ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hU₁ : U₁ ∈ orthogonalGroup (Fin m₁) ℝ)
    (hU₂ : U₂ ∈ orthogonalGroup (Fin m₂) ℝ) (hX : IsUnit X.det) {α β : ℕ → ℝ}
    (hA : U₁ᵀ * A * X = rectDiagonal α) (hB : U₂ᵀ * B * X = rectDiagonal β) :
    (∀ k : Fin n, A *ᵥ X.col k = α k • U₁.col (Fin.castLE hm₁ k) ∧
      B *ᵥ X.col k = β k • U₂.col (Fin.castLE hm₂ k)) ∧
    (∀ l : ℝ, Xᵀ * (Aᵀ * A - l • (Bᵀ * B)) * X =
      diagonal fun k : Fin n => α k ^ 2 - l * β k ^ 2) ∧
    (∀ k : Fin n, β k ≠ 0 →
      HasPencilEigenvector (Aᵀ * A) (Bᵀ * B) ((α k / β k) ^ 2) (X.col k)) ∧
    ((∀ k : Fin n, β k ≠ 0) →
      pencilSpectrum (Aᵀ * A) (Bᵀ * B) = Set.range fun k : Fin n => (α k / β k) ^ 2) := by
  -- `A X = U₁ D_A`, `B X = U₂ D_B`
  have hAX : ∀ {m : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
      {γ : ℕ → ℝ}, U ∈ orthogonalGroup (Fin m) ℝ → Uᵀ * M * X = rectDiagonal γ →
      M * X = U * rectDiagonal γ := fun {m M U γ} hU h => by
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ ℝ).1 hU,
      Matrix.one_mul]
  have hcol : ∀ {m : ℕ} (hm : n ≤ m) {M : Matrix (Fin m) (Fin n) ℝ}
      {U : Matrix (Fin m) (Fin m) ℝ} {γ : ℕ → ℝ}, M * X = U * rectDiagonal γ →
      ∀ k : Fin n, M *ᵥ X.col k = γ k • U.col (Fin.castLE hm k) := fun {m} hm {M U γ} h k => by
    rw [← col_mul_eq_mulVec_col, h]
    ext i
    simp only [col_apply, mul_apply, rectDiagonal_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (Fin.castLE hm k)]
    · simp [mul_comm]
    · intro j _ hj
      have hj' : ¬ ((j : ℕ) = k) := fun h => hj (Fin.ext (by simp [h]))
      simp [hj']
    · simp
  -- the Gram matrices
  have hgram : ∀ {m : ℕ} (hm : n ≤ m) {M : Matrix (Fin m) (Fin n) ℝ}
      {U : Matrix (Fin m) (Fin m) ℝ} {γ : ℕ → ℝ}, U ∈ orthogonalGroup (Fin m) ℝ →
      M * X = U * rectDiagonal γ →
      Xᵀ * (Mᵀ * M) * X = diagonal fun k : Fin n => γ k ^ 2 := fun {m} hm {M U γ} hU h => by
    have e : Xᵀ * (Mᵀ * M) * X = (M * X)ᵀ * (M * X) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e, h, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ,
      (mem_orthogonalGroup_iff' _ ℝ).1 hU, Matrix.one_mul, ← conjTranspose_eq_transpose_of_trivial,
      conjTranspose_rectDiagonal_mul_self]
    congr 1
    funext k
    simp [show (k : ℕ) < m by omega, sq]
  have hAX' := hAX hU₁ hA
  have hBX' := hAX hU₂ hB
  have hpen : ∀ l : ℝ, Xᵀ * (Aᵀ * A - l • (Bᵀ * B)) * X =
      diagonal fun k : Fin n => α k ^ 2 - l * β k ^ 2 := fun l => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hgram hm₁ hU₁ hAX',
      hgram hm₂ hU₂ hBX']
    ext i j
    by_cases h : i = j <;> simp [h]
  have hXu : IsUnit X := (isUnit_iff_isUnit_det X).2 hX
  have hXt : IsUnit Xᵀ.det := by rw [det_transpose]; exact hX
  refine ⟨fun k => ⟨hcol hm₁ hAX' k, hcol hm₂ hBX' k⟩, hpen, fun k hk => ?_, fun hβ => ?_⟩
  · refine ⟨(linearIndependent_cols_iff_isUnit.2 hXu).ne_zero k, ?_⟩
    set l := (α k / β k) ^ 2
    have hzero : Xᵀ *ᵥ ((Aᵀ * A - l • (Bᵀ * B)) *ᵥ X.col k) = 0 := by
      rw [← col_mul_eq_mulVec_col, ← col_mul_eq_mulVec_col, ← Matrix.mul_assoc, hpen l]
      ext i
      simp only [col_apply, diagonal_apply, Pi.zero_apply]
      split_ifs with h
      · subst h
        simp only [l]
        field_simp
        ring
      · rfl
    have hinj := (Matrix.mulVec_injective_iff_isUnit).2 ((isUnit_iff_isUnit_det _).2 hXt)
    have h0 := hinj (hzero.trans (mulVec_zero _).symm)
    rw [sub_mulVec, smul_mulVec, sub_eq_zero] at h0
    exact h0
  · ext l
    simp only [mem_pencilSpectrum_iff_det, Set.mem_range]
    have hdet : (Aᵀ * A - l • (Bᵀ * B)).det * (X.det * X.det) =
        ∏ k : Fin n, (α k ^ 2 - l * β k ^ 2) := by
      have := congrArg det (hpen l)
      rw [det_mul, det_mul, det_transpose, det_diagonal] at this
      rw [← this]
      ring
    have hXX : X.det * X.det ≠ 0 := mul_ne_zero hX.ne_zero hX.ne_zero
    constructor
    · intro h
      rw [h, zero_mul, eq_comm, Finset.prod_eq_zero_iff] at hdet
      obtain ⟨k, -, hk⟩ := hdet
      refine ⟨k, ?_⟩
      have := hβ k
      field_simp
      linarith
    · rintro ⟨k, rfl⟩
      have hk : ∏ j : Fin n, (α j ^ 2 - (α k / β k) ^ 2 * β j ^ 2) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) (by have := hβ k; field_simp; ring)
      rw [hk] at hdet
      exact (mul_eq_zero.1 hdet).resolve_right hXX

/-! ### §8.7.5 Computing the GSVD -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 8.7.2 (GSVD, tall full-rank version).** For `A ∈ ℝ^{m₁×n}`, `B ∈ ℝ^{m₂×n}` with
`null(A) ∩ null(B) = {0}`: "compute the QR factorization `[A; B] = [Q₁; Q₂] R`; compute the CS
decomposition `U₁ᵀ Q₁ V = D_A = diag(α₁, …, α_n)`, `U₂ᵀ Q₂ V = D_B = diag(β₁, …, β_n)`; solve
`R X = V` for `X`." The QR factorization is chapter 5's modified Gram–Schmidt (Algorithm 5.2.6) on
the stacked `(m₁ + m₂) × n` matrix, `R X = V` is back substitution (chapter 3's Algorithm 3.1.2)
column by column, and the CS decomposition is the monadic parameter `cs` (convention 5: the book
gives no algorithm for it), returning `(U₁, U₂, V, α, β)`. -/
noncomputable def algorithm_8_7_2 {m₁ m₂ : ℕ}
    (cs : Matrix (Fin m₁) (Fin n) ℝ → Matrix (Fin m₂) (Fin n) ℝ →
      M (Matrix (Fin m₁) (Fin m₁) ℝ × Matrix (Fin m₂) (Fin m₂) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        (ℕ → ℝ) × (ℕ → ℝ)))
    (A : Matrix (Fin m₁) (Fin n) ℝ) (B : Matrix (Fin m₂) (Fin n) ℝ) :
    M (Matrix (Fin m₁) (Fin m₁) ℝ × Matrix (Fin m₂) (Fin m₂) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      (ℕ → ℝ) × (ℕ → ℝ)) := do
  let QR ← Chapter05.algorithm_5_2_6 rnd ((fromRows A B).submatrix finSumFinEquiv.symm id)
  let out ← cs (QR.1.submatrix (Fin.castAdd m₂) id) (QR.1.submatrix (Fin.natAdd m₁) id)
  let X ← solveCols (Chapter03.algorithm_3_1_2 rnd QR.2) out.2.2.1
  pure (out.1, out.2.1, X, out.2.2.2.1, out.2.2.2.2)

end Programs

/-- **Algorithm 8.7.2, exact semantics**: if `cs` returns a thin CS decomposition — for `Q₁`, `Q₂`
with `Q₁ᵀQ₁ + Q₂ᵀQ₂ = I`, orthogonal `U₁`, `U₂`, `V` with `U₁ᵀ Q₁ V = D_A`, `U₂ᵀ Q₂ V = D_B`
(chapter 2's Theorem 2.5.2 gives one when `m₁, m₂ ≥ n`) — then for `A`, `B` with
`null(A) ∩ null(B) = {0}` (the book writes `= ∅`) the output `(U₁, U₂, X, α, β)` satisfies
`U₁ᵀ A X = D_A`, `U₂ᵀ B X = D_B` with `U₁`, `U₂` orthogonal and `X` nonsingular — a GSVD as in
Theorem 8.7.4. The stacked matrix has full column rank, so chapter 5's Algorithm 5.2.6 computes a
thin QR factorization with positive diagonal; `A X = Q₁ R X = Q₁ V`. -/
theorem algorithm_8_7_2_spec {m₁ m₂ : ℕ}
    (cs : Matrix (Fin m₁) (Fin n) ℝ → Matrix (Fin m₂) (Fin n) ℝ →
      Id (Matrix (Fin m₁) (Fin m₁) ℝ × Matrix (Fin m₂) (Fin m₂) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        (ℕ → ℝ) × (ℕ → ℝ)))
    (hcs : ∀ (Q₁ : Matrix (Fin m₁) (Fin n) ℝ) (Q₂ : Matrix (Fin m₂) (Fin n) ℝ),
      Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 →
        (Id.run (cs Q₁ Q₂)).1 ∈ orthogonalGroup (Fin m₁) ℝ ∧
        (Id.run (cs Q₁ Q₂)).2.1 ∈ orthogonalGroup (Fin m₂) ℝ ∧
        (Id.run (cs Q₁ Q₂)).2.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧
        (Id.run (cs Q₁ Q₂)).1ᵀ * Q₁ * (Id.run (cs Q₁ Q₂)).2.2.1 =
          rectDiagonal (Id.run (cs Q₁ Q₂)).2.2.2.1 ∧
        (Id.run (cs Q₁ Q₂)).2.1ᵀ * Q₂ * (Id.run (cs Q₁ Q₂)).2.2.1 =
          rectDiagonal (Id.run (cs Q₁ Q₂)).2.2.2.2)
    {A : Matrix (Fin m₁) (Fin n) ℝ} {B : Matrix (Fin m₂) (Fin n) ℝ}
    (hAB : ∀ x, A *ᵥ x = 0 → B *ᵥ x = 0 → x = 0) :
    (Id.run (algorithm_8_7_2 pure cs A B)).1 ∈ orthogonalGroup (Fin m₁) ℝ ∧
      (Id.run (algorithm_8_7_2 pure cs A B)).2.1 ∈ orthogonalGroup (Fin m₂) ℝ ∧
      IsUnit (Id.run (algorithm_8_7_2 pure cs A B)).2.2.1 ∧
      (Id.run (algorithm_8_7_2 pure cs A B)).1ᵀ * A *
          (Id.run (algorithm_8_7_2 pure cs A B)).2.2.1 =
        rectDiagonal (Id.run (algorithm_8_7_2 pure cs A B)).2.2.2.1 ∧
      (Id.run (algorithm_8_7_2 pure cs A B)).2.1ᵀ * B *
          (Id.run (algorithm_8_7_2 pure cs A B)).2.2.1 =
        rectDiagonal (Id.run (algorithm_8_7_2 pure cs A B)).2.2.2.2 := by
  set S := (fromRows A B).submatrix finSumFinEquiv.symm id with hS
  have hSA : ∀ x i, (S *ᵥ x) (Fin.castAdd m₂ i) = (A *ᵥ x) i := fun x i => by
    simp [S, mulVec, dotProduct]
  have hSB : ∀ x i, (S *ᵥ x) (Fin.natAdd m₁ i) = (B *ᵥ x) i := fun x i => by
    simp [S, mulVec, dotProduct]
  have hind : LinearIndependent ℝ Sᵀ := by
    refine mulVec_injective_iff.1 fun x y hxy => ?_
    rw [← sub_eq_zero] at hxy ⊢
    rw [← mulVec_sub] at hxy
    refine hAB _ (funext fun i => ?_) (funext fun i => ?_)
    · rw [← hSA, hxy, Pi.zero_apply, Pi.zero_apply]
    · rw [← hSB, hxy, Pi.zero_apply, Pi.zero_apply]
  obtain ⟨hQR, hRd⟩ := Chapter05.algorithm_5_2_6_spec S hind
  set QR := Id.run (Chapter05.algorithm_5_2_6 pure S)
  set Q₁ := QR.1.submatrix (Fin.castAdd m₂) id
  set Q₂ := QR.1.submatrix (Fin.natAdd m₁) id
  set out := Id.run (cs Q₁ Q₂)
  set X := Id.run (solveCols (Chapter03.algorithm_3_1_2 pure QR.2) out.2.2.1)
  have hrun : Id.run (algorithm_8_7_2 pure cs A B) =
      (out.1, out.2.1, X, out.2.2.2.1, out.2.2.2.2) := rfl
  rw [hrun]
  have hA1 : A = Q₁ * QR.2 := by
    ext i j
    have := congrFun (congrFun hQR.mul_eq (Fin.castAdd m₂ i)) j
    simp only [S, submatrix_apply, id, finSumFinEquiv_symm_apply_castAdd, fromRows_apply_inl,
      mul_apply] at this
    simp only [Q₁, mul_apply, submatrix_apply, id]
    exact this.symm
  have hB1 : B = Q₂ * QR.2 := by
    ext i j
    have := congrFun (congrFun hQR.mul_eq (Fin.natAdd m₁ i)) j
    simp only [S, submatrix_apply, id, finSumFinEquiv_symm_apply_natAdd, fromRows_apply_inr,
      mul_apply] at this
    simp only [Q₂, mul_apply, submatrix_apply, id]
    exact this.symm
  have hQQ : Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 := by
    ext i j
    have := congrFun (congrFun hQR.conjTranspose_mul_self i) j
    simp only [mul_apply, conjTranspose_apply, star_trivial, Fin.sum_univ_add] at this
    simpa [Q₁, Q₂, mul_apply] using this
  obtain ⟨hU1, hU2, hV, hDA, hDB⟩ := hcs Q₁ Q₂ hQQ
  have hRX : QR.2 * X = out.2.2.1 := mul_solveCols (fun b =>
    Chapter03.algorithm_3_1_2_spec hQR.isUpperTriangular (fun i => (hRd i).ne') b) _
  have hVd : IsUnit out.2.2.1.det :=
    isUnit_det_of_left_inverse ((mem_orthogonalGroup_iff' _ ℝ).1 hV)
  refine ⟨hU1, hU2, (isUnit_iff_isUnit_det X).2 (isUnit_of_mul_isUnit_right
    (by rw [← det_mul, hRX]; exact hVd)), ?_, ?_⟩
  · rw [hA1, show out.1ᵀ * (Q₁ * QR.2) * X = out.1ᵀ * Q₁ * (QR.2 * X) by
      simp only [Matrix.mul_assoc], hRX, hDA]
  · rw [hB1, show out.2.1ᵀ * (Q₂ * QR.2) * X = out.2.1ᵀ * Q₂ * (QR.2 * X) by
      simp only [Matrix.mul_assoc], hRX, hDB]

/-- **§8.7.5, after Algorithm 8.7.2.** If `X = R⁻¹ V` (`V` orthogonal; the book's `R` is
nonsingular, which the identity does not need) and
`T Zᵀ = Vᵀ R` with `Z` orthogonal and `T` upper triangular and nonsingular, then `Z T⁻¹ = R⁻¹ V = X`
and, for every `k`, `span{x_1, …, x_k} = span{z_1, …, z_k}`. -/
theorem gsvd_subspace_via_rq {R V Z T : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (hT : T.IsUpperTriangular) (hTu : IsUnit T.det) (hTZ : T * Zᵀ = Vᵀ * R) :
    Z * T⁻¹ = R⁻¹ * V ∧ ∀ (k : ℕ) (hk : k ≤ n),
      Submodule.span ℝ (Set.range fun i : Fin k => (R⁻¹ * V).col (Fin.castLE hk i)) =
        Submodule.span ℝ (Set.range fun i : Fin k => Z.col (Fin.castLE hk i)) := by
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hZ
  have hVV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hX : Z * T⁻¹ = R⁻¹ * V := by
    have h1 : (T * Zᵀ)⁻¹ = Z * T⁻¹ := by
      rw [Matrix.mul_inv_rev, inv_eq_left_inv (show Z * Zᵀ = 1 from hZZ)]
    have h2 : (Vᵀ * R)⁻¹ = R⁻¹ * V := by
      rw [Matrix.mul_inv_rev, inv_eq_right_inv (show Vᵀ * V = 1 from
        (mem_orthogonalGroup_iff' _ ℝ).1 hV)]
    rw [← h1, hTZ, h2]
  refine ⟨hX, fun k hk => ?_⟩
  rw [← hX]
  have hTi : T⁻¹.IsUpperTriangular := by
    have : Invertible T := invertibleOfIsUnitDet T hTu
    exact blockTriangular_inv_of_blockTriangular hT
  have hZe : Z = Z * T⁻¹ * T := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hTu, Matrix.mul_one]
  -- a column of `M * U` with `U` upper triangular is a combination of the first columns of `M`
  have key : ∀ (M U : Matrix (Fin n) (Fin n) ℝ), U.IsUpperTriangular → ∀ i : Fin k,
      (M * U).col (Fin.castLE hk i) ∈
        Submodule.span ℝ (Set.range fun i : Fin k => M.col (Fin.castLE hk i)) := by
    intro M U hU i
    have hcol : (M * U).col (Fin.castLE hk i) = ∑ j : Fin n, U j (Fin.castLE hk i) • M.col j := by
      ext r
      simp [col_apply, mul_apply, Finset.sum_apply, mul_comm]
    rw [hcol]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · have h0 : U j (Fin.castLE hk i) = 0 := hU (Fin.lt_def.2 (by simp; omega))
      rw [h0, zero_smul]
      exact zero_mem _
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact key Z T⁻¹ hTi i
  · rintro _ ⟨i, rfl⟩
    have := key (Z * T⁻¹) T hT i
    rwa [← hZe] at this

/-! ### §8.7.7 The Kogbetliantz approach -/

/-- **§8.7.7, the `2 × 2` GSVD step.** For `F`, `G` with `G` nonsingular and an SVD
`U₁ᵀ (F G⁻¹) U₂ = Σ = diag(σ₁, σ₂)` (only `U₂`'s orthogonality is used): `U₁ᵀ F = Σ (U₂ᵀ G)`
(the book prints `(U₂ᵀ G) Σ`); if `Z` is
orthogonal with `U₂ᵀ G Z` upper triangular, then `U₁ᵀ F Z = Σ (U₂ᵀ G Z)` is upper triangular; and
`X = G⁻¹ U₂` gives the GSVD `U₁ᵀ F X = Σ`, `U₂ᵀ G X = I`, so `σ(F, G) = {σ₁, σ₂}`. -/
theorem kogbetliantz_twoByTwo {F G U₁ U₂ : Matrix (Fin 2) (Fin 2) ℝ} (hG : IsUnit G.det)
    (hU₂ : U₂ ∈ orthogonalGroup (Fin 2) ℝ)
    {σ : Fin 2 → ℝ} (hSig : U₁ᵀ * (F * G⁻¹) * U₂ = diagonal σ) :
    U₁ᵀ * F = diagonal σ * (U₂ᵀ * G) ∧
      (∀ Z ∈ orthogonalGroup (Fin 2) ℝ, (U₂ᵀ * G * Z).IsUpperTriangular →
        U₁ᵀ * F * Z = diagonal σ * (U₂ᵀ * G * Z) ∧ (U₁ᵀ * F * Z).IsUpperTriangular) ∧
      U₁ᵀ * F * (G⁻¹ * U₂) = diagonal σ ∧ U₂ᵀ * G * (G⁻¹ * U₂) = 1 := by
  have hU₂' : U₂ * U₂ᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU₂
  have hU₂'' : U₂ᵀ * U₂ = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU₂
  have h1 : U₁ᵀ * F = diagonal σ * (U₂ᵀ * G) := by
    rw [← hSig]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₂, hU₂', Matrix.one_mul, nonsing_inv_mul _ hG, Matrix.mul_one]
  refine ⟨h1, fun Z _ hZ => ?_, ?_, ?_⟩
  · have h2 : U₁ᵀ * F * Z = diagonal σ * (U₂ᵀ * G * Z) := by
      rw [h1]
      simp only [Matrix.mul_assoc]
    exact ⟨h2, h2 ▸ (blockTriangular_diagonal σ).mul hZ⟩
  · rw [← hSig]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, hU₂'']

/-! ### §8.7.9 The quadratic eigenvalue problem -/

/-- **(8.7.13)–(8.7.14).** If `(λ² M + λ C + K) x = 0`, then with `m = xᴴMx`, `c = xᴴCx`,
`k = xᴴKx`: `m λ² + c λ + k = 0`, hence `(2mλ + c)² = c² - 4mk` — the quadratic formula (8.7.14)
for `m ≠ 0`. -/
theorem equation_8_7_13 (M C K : Matrix (Fin n) (Fin n) ℂ) {l : ℂ} {x : Fin n → ℂ}
    (h : (l ^ 2 • M + l • C + K) *ᵥ x = 0) :
    (star x ⬝ᵥ M *ᵥ x) * l ^ 2 + (star x ⬝ᵥ C *ᵥ x) * l + star x ⬝ᵥ K *ᵥ x = 0 ∧
      (2 * (star x ⬝ᵥ M *ᵥ x) * l + star x ⬝ᵥ C *ᵥ x) ^ 2 =
        (star x ⬝ᵥ C *ᵥ x) ^ 2 - 4 * (star x ⬝ᵥ M *ᵥ x) * (star x ⬝ᵥ K *ᵥ x) := by
  have h1 : (star x ⬝ᵥ M *ᵥ x) * l ^ 2 + (star x ⬝ᵥ C *ᵥ x) * l + star x ⬝ᵥ K *ᵥ x = 0 := by
    have := congrArg (star x ⬝ᵥ ·) h
    simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
      dotProduct_zero] at this
    linear_combination this
  exact ⟨h1, by linear_combination 4 * (star x ⬝ᵥ M *ᵥ x) * h1⟩

/-- A `2 × 2` block equation `[A₁ B₁; C₁ D₁] [x; u] = λ [A₂ B₂; C₂ D₂] [x; u]` is its two rows. -/
private theorem fromBlocks_eq_smul_iff {m : ℕ}
    (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Matrix (Fin m) (Fin m) ℂ) (l : ℂ) (x u : Fin m → ℂ) :
    fromBlocks A₁ B₁ C₁ D₁ *ᵥ Sum.elim x u = l • (fromBlocks A₂ B₂ C₂ D₂ *ᵥ Sum.elim x u) ↔
      A₁ *ᵥ x + B₁ *ᵥ u = l • (A₂ *ᵥ x + B₂ *ᵥ u) ∧
        C₁ *ᵥ x + D₁ *ᵥ u = l • (C₂ *ᵥ x + D₂ *ᵥ u) := by
  simp only [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, funext_iff, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, Pi.smul_apply]

/-- **(8.7.15)–(8.7.16), linearizations.** For nonsingular `N`, `(λ, x)` solves (8.7.12) iff
`(λ, (x, λx))` solves `[0 N; K C][x; u] = λ[N 0; 0 -M][x; u]` (8.7.15), iff it solves
`[-K 0; 0 N][x; u] = λ[C M; N 0][x; u]` (8.7.16); and every solution `(x, u)` of either
linearization has `u = λx` (so `x ≠ 0` for an eigenvector). -/
theorem equation_8_7_15 (M C K : Matrix (Fin n) (Fin n) ℂ) {N : Matrix (Fin n) (Fin n) ℂ}
    (hN : IsUnit N) (l : ℂ) :
    (∀ x : Fin n → ℂ, (l ^ 2 • M + l • C + K) *ᵥ x = 0 ↔
      fromBlocks 0 N K C *ᵥ Sum.elim x (l • x) =
        l • (fromBlocks N 0 0 (-M) *ᵥ Sum.elim x (l • x))) ∧
    (∀ x : Fin n → ℂ, (l ^ 2 • M + l • C + K) *ᵥ x = 0 ↔
      fromBlocks (-K) 0 0 N *ᵥ Sum.elim x (l • x) =
        l • (fromBlocks C M N 0 *ᵥ Sum.elim x (l • x))) ∧
    (∀ x u : Fin n → ℂ, fromBlocks 0 N K C *ᵥ Sum.elim x u =
      l • (fromBlocks N 0 0 (-M) *ᵥ Sum.elim x u) → u = l • x) ∧
    (∀ x u : Fin n → ℂ, fromBlocks (-K) 0 0 N *ᵥ Sum.elim x u =
      l • (fromBlocks C M N 0 *ᵥ Sum.elim x u) → u = l • x) := by
  have hinj := (Matrix.mulVec_injective_iff_isUnit).2 hN
  have hNrow : ∀ x u : Fin n → ℂ, N *ᵥ u = l • (N *ᵥ x) → u = l • x := fun x u h =>
    hinj (by rw [h, mulVec_smul])
  have hQ : ∀ x : Fin n → ℂ,
      (l ^ 2 • M + l • C + K) *ᵥ x = l ^ 2 • (M *ᵥ x) + l • (C *ᵥ x) + K *ᵥ x := fun x => by
    rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec]
  refine ⟨fun x => ?_, fun x => ?_, fun x u h => ?_, fun x u h => ?_⟩
  · rw [fromBlocks_eq_smul_iff, hQ]
    simp only [zero_mulVec, zero_add, add_zero, mulVec_smul, neg_mulVec, funext_iff,
      Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      implies_true, true_and]
    exact forall_congr' fun i =>
      ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  · rw [fromBlocks_eq_smul_iff, hQ]
    simp only [zero_mulVec, zero_add, add_zero, mulVec_smul, neg_mulVec, funext_iff,
      Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
      implies_true, and_true]
    exact forall_congr' fun i =>
      ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  · rw [fromBlocks_eq_smul_iff] at h
    simp only [zero_mulVec, zero_add, add_zero] at h
    exact hNrow x u h.1
  · rw [fromBlocks_eq_smul_iff] at h
    simp only [zero_mulVec, zero_add, add_zero] at h
    exact hNrow x u h.2

open scoped ComplexOrder in
/-- **§8.7.9.** If `M`, `C` are symmetric positive definite and `K` symmetric positive
semidefinite (here in the complex Hermitian form), every eigenvalue `λ` of (8.7.12) has
nonpositive real part. -/
theorem qep_re_nonpos {M C K : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) (hC : C.PosDef)
    (hK : K.PosSemidef) {l : ℂ} {x : Fin n → ℂ} (hx : x ≠ 0)
    (h : (l ^ 2 • M + l • C + K) *ᵥ x = 0) : l.re ≤ 0 := by
  have h1 := (equation_8_7_13 M C K h).1
  have hm := hM.dotProduct_mulVec_pos hx
  have hc := hC.dotProduct_mulVec_pos hx
  have hk := hK.dotProduct_mulVec_nonneg x
  rw [Complex.lt_def] at hm hc
  rw [Complex.le_def] at hk
  simp only [Complex.zero_re, Complex.zero_im] at hm hc hk
  have hre := congrArg Complex.re h1
  have him := congrArg Complex.im h1
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sq,
    Complex.zero_re, Complex.zero_im, ← hm.2, ← hc.2, ← hk.2] at hre him
  by_contra hpos
  push Not at hpos
  have hb : l.im = 0 := by
    have : l.im * (2 * (star x ⬝ᵥ M *ᵥ x).re * l.re + (star x ⬝ᵥ C *ᵥ x).re) = 0 := by
      linear_combination him
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · nlinarith
  rw [hb] at hre
  nlinarith [mul_pos hm.1 (mul_pos hpos hpos), mul_pos hc.1 hpos]

open scoped ComplexOrder in
/-- **§8.7.9, the gyroscopic QEP**, corrected: if `M` is symmetric positive definite, `C` skew
(`Cᴴ = -C`) and `K` symmetric **positive semidefinite** (the hypothesis the book omits, see
`gyroscopic_counterexample`), every eigenvalue is purely imaginary; and (8.7.12) is equivalent to
the structured linearization `[0 -K; M 0][u; x] = λ[M C; 0 M][u; x]` with `u = λx`. -/
theorem gyroscopic_eigenvalues_imaginary {M C K : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef)
    (hC : Cᴴ = -C) (hK : K.PosSemidef) :
    (∀ {l : ℂ} {x : Fin n → ℂ}, x ≠ 0 → (l ^ 2 • M + l • C + K) *ᵥ x = 0 → l.re = 0) ∧
      ∀ (l : ℂ) (u x : Fin n → ℂ), fromBlocks 0 (-K) M 0 *ᵥ Sum.elim u x =
          l • (fromBlocks M C 0 M *ᵥ Sum.elim u x) ↔
        u = l • x ∧ (l ^ 2 • M + l • C + K) *ᵥ x = 0 := by
  refine ⟨fun {l x} hx h => ?_, fun l u x => ?_⟩
  · have h1 := (equation_8_7_13 M C K h).1
    have hm := hM.dotProduct_mulVec_pos hx
    have hk := hK.dotProduct_mulVec_nonneg x
    -- `xᴴ C x` is purely imaginary
    have hc : (star x ⬝ᵥ C *ᵥ x).re = 0 := by
      have hIC : (Complex.I • C)ᴴ = Complex.I • C := by
        rw [conjTranspose_smul, hC, Complex.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]
      have := star_dotProduct_mulVec_self_of_conjTranspose_eq hIC x
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, star_mul', Complex.star_def,
        Complex.conj_I] at this
      have him := congrArg Complex.im this
      simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im] at him
      linarith
    rw [Complex.lt_def] at hm
    rw [Complex.le_def] at hk
    simp only [Complex.zero_re, Complex.zero_im] at hm hk
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sq,
      Complex.zero_re, Complex.zero_im, ← hm.2, ← hk.2, hc] at hre him
    by_contra ha
    have hb : (star x ⬝ᵥ C *ᵥ x).im = -(2 * (star x ⬝ᵥ M *ᵥ x).re * l.im) := by
      have : l.re * (2 * (star x ⬝ᵥ M *ᵥ x).re * l.im + (star x ⬝ᵥ C *ᵥ x).im) = 0 := by
        linear_combination him
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 ha
      · linarith
    rw [hb] at hre
    have hsq : 0 < l.re * l.re := mul_self_pos.2 ha
    nlinarith [mul_pos hm.1 hsq, mul_nonneg hm.1.le (mul_self_nonneg l.im)]
  · have hinj := (Matrix.mulVec_injective_iff_isUnit).2 hM.isUnit
    rw [fromBlocks_eq_smul_iff]
    simp only [zero_mulVec, zero_add, add_zero, neg_mulVec]
    constructor
    · rintro ⟨h1, h2⟩
      have hu : u = l • x := hinj (by rw [h2, mulVec_smul])
      refine ⟨hu, ?_⟩
      rw [hu, mulVec_smul] at h1
      rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec]
      ext i
      have := congrFun h1 i
      simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      linear_combination -this
    · rintro ⟨rfl, h⟩
      refine ⟨?_, by rw [mulVec_smul]⟩
      rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec] at h
      rw [mulVec_smul]
      ext i
      have := congrFun h i
      simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      linear_combination -this

open scoped ComplexOrder in
/-- **The book's gyroscopic claim needs `K ⪰ 0`**: for `n = 1`, `M = 1`, `C = 0` (skew) and
`K = -1` (symmetric), `λ = 1` is an eigenvalue of (8.7.12), not purely imaginary. -/
theorem gyroscopic_counterexample :
    let M : Matrix (Fin 1) (Fin 1) ℂ := 1
    let C : Matrix (Fin 1) (Fin 1) ℂ := 0
    let K : Matrix (Fin 1) (Fin 1) ℂ := -1
    M.PosDef ∧ Cᴴ = -C ∧ K.IsHermitian ∧
      ∃ (l : ℂ) (x : Fin 1 → ℂ), x ≠ 0 ∧ (l ^ 2 • M + l • C + K) *ᵥ x = 0 ∧ l.re ≠ 0 := by
  intro M C K
  refine ⟨PosDef.one, by simp [C], by simp [K, IsHermitian], 1, 1, one_ne_zero, ?_, by simp⟩
  simp [M, C, K]

/-- **§8.7.9, the palindromic QEP** `Q(λ) = λ²M + λC + Mᵀ` with `Cᵀ = C`: for `λ ≠ 0`, `Q(λ)` is
singular iff `Q(1/λ)` is. -/
theorem palindromic_reciprocal {M C : Matrix (Fin n) (Fin n) ℂ} (hC : Cᵀ = C) {l : ℂ}
    (hl : l ≠ 0) :
    (l ^ 2 • M + l • C + Mᵀ).det = 0 ↔ (l⁻¹ ^ 2 • M + l⁻¹ • C + Mᵀ).det = 0 := by
  have key : l⁻¹ ^ 2 • M + l⁻¹ • C + Mᵀ = l⁻¹ ^ 2 • (l ^ 2 • M + l • C + Mᵀ)ᵀ := by
    rw [transpose_add, transpose_add, transpose_smul, transpose_smul, transpose_transpose, hC,
      smul_add, smul_add, smul_smul, smul_smul]
    have h1 : l⁻¹ ^ 2 * l ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl, one_pow]
    have h2 : l⁻¹ ^ 2 * l = l⁻¹ := by field_simp
    rw [h1, h2, one_smul]
    abel
  rw [key, det_smul, det_transpose, mul_eq_zero, or_iff_right (pow_ne_zero _ (pow_ne_zero _
    (inv_ne_zero hl)))]

/-- **(8.7.17) ⇒ (8.7.18).** If
`[Mᵀ Mᵀ; C - M Mᵀ][y; z] = λ[-M Mᵀ - C; -M -M][y; z]` then `(λ²M + λC + Mᵀ)(y + z) = 0`. -/
theorem equation_8_7_18 {M C : Matrix (Fin n) (Fin n) ℂ} {l : ℂ} {y z : Fin n → ℂ}
    (h : fromBlocks Mᵀ Mᵀ (C - M) Mᵀ *ᵥ Sum.elim y z =
      l • (fromBlocks (-M) (Mᵀ - C) (-M) (-M) *ᵥ Sum.elim y z)) :
    (l ^ 2 • M + l • C + Mᵀ) *ᵥ (y + z) = 0 := by
  rw [fromBlocks_eq_smul_iff] at h
  obtain ⟨h1, h2⟩ := h
  ext i
  have e1 := congrFun h1 i
  have e2 := congrFun h2 i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_mulVec, neg_mulVec, Pi.sub_apply,
    Pi.neg_apply] at e1 e2
  simp only [add_mulVec, smul_mulVec, mulVec_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  linear_combination e1 + l * e2

end GolubVanLoan.Chapter08
