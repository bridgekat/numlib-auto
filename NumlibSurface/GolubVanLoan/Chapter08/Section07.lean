import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Numlib.Eigen.Pencil
import Numlib.Eigen.SymmetricPencil
import Numlib.LinearAlgebra.Matrix.SVD
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

Algorithms 8.7.1–8.7.2, `(8.7.8)` and Theorem 8.7.4 call chapter 3–6 programs and restatements; they
are planned in this group and wait for those chapters' surfaces.

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

/-- **(8.7.6)–(8.7.7).** For positive definite `B` and `x ≠ 0`, `λ = xᵀAx / xᵀBx` minimizes
`f(λ) = ‖Ax - λBx‖_B`, `‖z‖_B² = zᵀB⁻¹z` (`A` need not be symmetric). -/
theorem equation_8_7_7 (A : Matrix (Fin n) (Fin n) ℝ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) {x : Fin n → ℝ} (hx : x ≠ 0) :
    IsMinOn (fun μ : ℝ => Real.sqrt ((A *ᵥ x - μ • B *ᵥ x) ⬝ᵥ B⁻¹ *ᵥ (A *ᵥ x - μ • B *ᵥ x)))
      Set.univ ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) :=
  fun _ hμ => Real.sqrt_le_sqrt (isMinOn_pencil_residual (A := A) hB hx hμ)

/-! ### §8.7.4 The generalized singular value problem -/

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
