/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside a future SVD.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.LinearAlgebra.Matrix.CSDecomposition

/-!
# The generalized singular value decomposition

The *generalized singular value decomposition* (GSVD) of a pair `A : Matrix (Fin m₁) (Fin n) 𝕜`,
`B : Matrix (Fin m₂) (Fin n) 𝕜` ([golub2013matrix] Theorem 6.1.1, after Van Loan 1976 and
Paige–Saunders 1981) diagonalizes both at once: unitary `U₁`, `U₂` and an invertible `X` with
`U₁ᴴ A X = D_A` rectangular diagonal and `U₂ᴴ B X = D_B` rectangular diagonal shifted by
`p = r − m₂` columns, where `r` is the rank of the stacked matrix `[A; B]` and the pairs
`(α_i, β_i)` are cosine–sine pairs.

## Main definitions

* `Matrix.IsGSVD A B U₁ U₂ X α β`: the specification, with `D_A = rectDiagonal α` and
  `D_B = shiftedRectDiagonal p β`; read 0-based, `α_i = 1, β_i = 0` for `i < p`,
  `α_i² + β_i² = 1` with `α_i, β_i ≥ 0` for `p ≤ i < r`, and `α_i = β_i = 0` for `i ≥ r`.

## Main results

* `Matrix.exists_isGSVD`: [golub2013matrix] Theorem 6.1.1, for `n ≤ m₁`. The book's proof: an SVD
  `[A; B] = Q diag(Σ_r, 0) Zᴴ`, the thin CS decomposition of the first `r` columns of `Q`
  (`Matrix.exists_isThinCSD`, in the general form without `m₂ ≥ r`), and
  `X = Z · blockDiag(V₁ᴴ Σ_r, I)⁻¹`.
* `Matrix.IsGSVD.conjTranspose_mul_gram_add_smul_gram_mul`: `Xᴴ (AᴴA + λ BᴴB) X =
  diag(α² + λ β²)`, and `Matrix.IsGSVD.gram_mulVec_col`: the columns of `X` are generalized
  eigenvectors of the pencil `AᴴA − μ² BᴴB`.
* `Matrix.IsGSVD.ker_inf_ker`: the common kernel of `A` and `B` is spanned by the columns
  `x_i`, `i ≥ r`.
* `Matrix.IsGSVD.svd_of_eq_one`: the GSVD of `(A, I)` is an SVD of `A`.

## Implementation notes

The consequences that read `α_i` off `D_A` assume the book's standing hypothesis `n ≤ m₁`: without
it the entries `α_i` with `m₁ ≤ i < n` are not seen by the `m₁ × n` matrix `D_A`.

## References

* [golub2013matrix] §6.1.6; C. F. Van Loan, *Generalizing the singular value decomposition*,
  SIAM J. Numer. Anal. 13 (1976); C. C. Paige, M. A. Saunders, SIAM J. Numer. Anal. 18 (1981).
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Def

variable {m₁ m₂ n : ℕ}

/-- **The generalized singular value decomposition, as a specification** ([golub2013matrix]
Theorem 6.1.1, (6.1.22)–(6.1.23)): with `r` the rank of `[A; B]` and `p = r − m₂` (truncated),
`U₁`, `U₂` are unitary, `X` is invertible, `U₁ᴴ A X = rectDiagonal α` and
`U₂ᴴ B X = shiftedRectDiagonal p β`, where `α_i = 1, β_i = 0` for `i < p`, `α_i² + β_i² = 1` for
`p ≤ i < r`, `α_i = β_i = 0` for `i ≥ r`, and all are nonnegative. The columns of `X` are the
book's `x_1, …, x_n`. -/
structure IsGSVD (A : Matrix (Fin m₁) (Fin n) 𝕜) (B : Matrix (Fin m₂) (Fin n) 𝕜)
    (U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜) (U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜)
    (X : Matrix (Fin n) (Fin n) 𝕜) (α β : ℕ → ℝ) : Prop where
  /-- The first left factor is unitary. -/
  mem_unitaryGroup_left : U₁ ∈ unitaryGroup (Fin m₁) 𝕜
  /-- The second left factor is unitary. -/
  mem_unitaryGroup_right : U₂ ∈ unitaryGroup (Fin m₂) 𝕜
  /-- The right factor is invertible. -/
  isUnit : IsUnit X
  /-- The first `p` pairs are `(1, 0)`. -/
  of_lt_p : ∀ i < (fromRows A B).rank - m₂, α i = 1 ∧ β i = 0
  /-- The middle pairs are cosine–sine pairs. -/
  sq_add_sq : ∀ i, (fromRows A B).rank - m₂ ≤ i → i < (fromRows A B).rank →
    α i ^ 2 + β i ^ 2 = 1
  /-- The pairs are nonnegative. -/
  nonneg : ∀ i, 0 ≤ α i ∧ 0 ≤ β i
  /-- The pairs past the rank vanish. -/
  of_le_r : ∀ i, (fromRows A B).rank ≤ i → α i = 0 ∧ β i = 0
  /-- The factorization of `A`. -/
  star_mul_mul_left : star U₁ * A * X = rectDiagonal fun i => ((α i : ℝ) : 𝕜)
  /-- The factorization of `B`. -/
  star_mul_mul_right : star U₂ * B * X =
    shiftedRectDiagonal ((fromRows A B).rank - m₂) fun i => ((β i : ℝ) : 𝕜)

end Def

section Exists

variable {m₁ m₂ n : ℕ}

/-- **Existence of the GSVD** ([golub2013matrix] Theorem 6.1.1): for `n ≤ m₁` every pair
`A : Matrix (Fin m₁) (Fin n) 𝕜`, `B : Matrix (Fin m₂) (Fin n) 𝕜` has a GSVD. Let
`[A; B] Z = Q Σ = Q₁ Σ_r [I 0]` be an SVD, `Q₁ = [Q₁₁; Q₂₁]` the first `r` columns of `Q`, and
`U₁ᴴ Q₁₁ V₁ = C`, `U₂ᴴ Q₂₁ V₁ = S` a thin CS decomposition (`Matrix.exists_isThinCSD`, with
`r ≤ n ≤ m₁`). With `Y = Rᵀ Σ_r⁻¹ V₁ R + (1 − Rᵀ R)`, `R = [I_r 0]`, and `X = Z Y` one gets
`A X = Q₁₁ V₁ R` and `B X = Q₂₁ V₁ R`, whence the two diagonal forms; `Y` is invertible, with
inverse `Rᵀ V₁ᴴ Σ_r R + (1 − Rᵀ R)`. -/
theorem exists_isGSVD (hnm : n ≤ m₁) (A : Matrix (Fin m₁) (Fin n) 𝕜)
    (B : Matrix (Fin m₂) (Fin n) 𝕜) : ∃ U₁ U₂ X α β, IsGSVD A B U₁ U₂ X α β := by
  classical
  set r := (fromRows A B).rank with hr
  set M : Matrix (Fin (m₁ + m₂)) (Fin n) 𝕜 :=
    (fromRows A B).submatrix finSumFinEquiv.symm (Equiv.refl _) with hM
  have hMr : M.rank = r := rank_submatrix _ _ _
  obtain ⟨Q, σ, Z, hs⟩ := exists_isSVD M
  have hrn : r ≤ n := by
    have := rank_le_card_width (fromRows A B); rwa [Fintype.card_fin] at this
  have hrm : r ≤ m₁ + m₂ := by
    have := rank_le_card_height (fromRows A B)
    rwa [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at this
  have hσpos : ∀ i < r, σ i ≠ 0 := fun i hi => by
    rw [hs.singularValues_eq (by omega) (by omega), Ne, sortedSingularValues_eq_zero_iff_rank_le,
      hMr]
    omega
  have hσzero : ∀ i, r ≤ i → i < m₁ + m₂ → i < n → σ i = 0 := fun i h1 h2 h3 => by
    rw [hs.singularValues_eq h2 h3, sortedSingularValues_eq_zero_iff_rank_le, hMr]
    exact h1
  -- the first `r` columns of `Q`, split into blocks
  set Q₁₁ : Matrix (Fin m₁) (Fin r) 𝕜 := Q.submatrix (Fin.castAdd m₂) (Fin.castLE hrm)
  set Q₂₁ : Matrix (Fin m₂) (Fin r) 𝕜 := Q.submatrix (Fin.natAdd m₁) (Fin.castLE hrm)
  have hQQ : Qᴴ * Q = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hs.mem_unitaryGroup_left
  have hQo : Q₁₁ᴴ * Q₁₁ + Q₂₁ᴴ * Q₂₁ = 1 := by
    ext i j
    have h := congrFun (congrFun hQQ (Fin.castLE hrm i)) (Fin.castLE hrm j)
    rw [mul_apply, Fin.sum_univ_add, one_apply] at h
    simp only [(Fin.castLE_injective hrm).eq_iff] at h
    rw [add_apply, mul_apply, mul_apply, one_apply]
    simpa [Q₁₁, Q₂₁, conjTranspose_apply, submatrix_apply] using h
  obtain ⟨U₁, U₂, V₁, θ, hc⟩ := exists_isThinCSD Q₁₁ Q₂₁ hQo (hrn.trans hnm)
  -- the selector `R = [I_r 0]` and the diagonal `Σ_r`
  set R : Matrix (Fin r) (Fin n) 𝕜 := rectDiagonal fun _ => 1 with hR
  set D : Matrix (Fin r) (Fin r) 𝕜 := diagonal fun i => ((σ i : ℝ) : 𝕜) with hD
  set Dinv : Matrix (Fin r) (Fin r) 𝕜 := diagonal fun i => ((σ i : ℝ) : 𝕜)⁻¹ with hDinv
  have hσ' : ∀ i : Fin r, ((σ i : ℝ) : 𝕜) ≠ 0 := fun i =>
    RCLike.ofReal_ne_zero.2 (hσpos i i.isLt)
  have hDX : ∀ Y : Matrix (Fin r) (Fin n) 𝕜, D * (Dinv * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hD, hDinv, diagonal_mul_diagonal,
      show (fun i : Fin r => ((σ i : ℝ) : 𝕜) * ((σ i : ℝ) : 𝕜)⁻¹) = fun _ => 1 from
        funext fun i => mul_inv_cancel₀ (hσ' i), diagonal_one, Matrix.one_mul]
  have hDX' : ∀ Y : Matrix (Fin r) (Fin n) 𝕜, Dinv * (D * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hD, hDinv, diagonal_mul_diagonal,
      show (fun i : Fin r => ((σ i : ℝ) : 𝕜)⁻¹ * ((σ i : ℝ) : 𝕜)) = fun _ => 1 from
        funext fun i => inv_mul_cancel₀ (hσ' i), diagonal_one, Matrix.one_mul]
  have hRRt : R * Rᵀ = 1 := by
    rw [hR, rectDiagonal_transpose, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    rw [ite_eq_left (lt_of_lt_of_le i.isLt hrn), mul_one]
  have hRX : ∀ Y : Matrix (Fin r) (Fin n) 𝕜, R * (Rᵀ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hRRt, Matrix.one_mul]
  have hVV : V₁ * V₁ᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 hc.mem_unitaryGroup_right
  have hVX : ∀ Y : Matrix (Fin r) (Fin n) 𝕜, V₁ * (V₁ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
  -- the right factor `X = Z Y`
  set Y : Matrix (Fin n) (Fin n) 𝕜 := Rᵀ * (Dinv * (V₁ * R)) + (1 - Rᵀ * R) with hY
  have hYinv : Y * (Rᵀ * (V₁ᴴ * (D * R)) + (1 - Rᵀ * R)) = 1 := by
    simp only [hY, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hRX, hVX, hDX']
    abel
  have hRY : R * Y = Dinv * (V₁ * R) := by
    simp only [hY, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hRX, sub_self, add_zero]
  -- `[A; B] Z = Q₁ Σ_r R`
  have hMZ : ∀ i j, (M * Z) i j
      = if h : (j : ℕ) < r then Q i (Fin.castLE hrm ⟨j, h⟩) * ((σ j : ℝ) : 𝕜) else 0 := by
    have h1 : M * Z = Q * rectDiagonal fun i => ((σ i : ℝ) : 𝕜) := by
      rw [← hs.star_mul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        mem_unitaryGroup_iff.1 hs.mem_unitaryGroup_left, Matrix.one_mul]
    intro i j
    rw [h1, mul_rectDiagonal_apply]
    by_cases hj : (j : ℕ) < r
    · rw [dite_eq_left_of_eq_true (eq_true (lt_of_lt_of_le hj hrm)),
        dite_eq_left_of_eq_true (eq_true hj)]
      rfl
    · rw [dite_eq_right_of_eq_false (eq_false hj)]
      split_ifs with hj'
      · rw [hσzero j (not_lt.1 hj) hj' j.isLt, RCLike.ofReal_zero, mul_zero]
      · rfl
  have hAZ : A * Z = Q₁₁ * D * R := by
    ext i j
    rw [mul_rectDiagonal_apply,
      show (A * Z) i j = (M * Z) (Fin.castAdd m₂ i) j by simp [mul_apply, hM], hMZ]
    split_ifs
    · simp [Q₁₁, hD, mul_diagonal]
    · rfl
  have hBZ : B * Z = Q₂₁ * D * R := by
    ext i j
    rw [mul_rectDiagonal_apply,
      show (B * Z) i j = (M * Z) (Fin.natAdd m₁ i) j by simp [mul_apply, hM], hMZ]
    split_ifs
    · simp [Q₂₁, hD, mul_diagonal]
    · rfl
  have hAX : A * (Z * Y) = Q₁₁ * (V₁ * R) := by
    rw [← Matrix.mul_assoc, hAZ]
    simp only [Matrix.mul_assoc, hRY, hDX]
  have hBX : B * (Z * Y) = Q₂₁ * (V₁ * R) := by
    rw [← Matrix.mul_assoc, hBZ]
    simp only [Matrix.mul_assoc, hRY, hDX]
  -- the generalized singular values
  set α : ℕ → ℝ := fun i => if i < r then Real.cos (θ i) else 0 with hα
  set β : ℕ → ℝ := fun i => if i < r then Real.sin (θ i) else 0 with hβ
  have hp : r - min r m₂ = r - m₂ := by omega
  refine ⟨U₁, U₂, Z * Y, α, β, hc.mem_unitaryGroup_left₁, hc.mem_unitaryGroup_left₂,
    (isUnit_of_mem_unitaryGroup hs.mem_unitaryGroup_right).mul
      ((isUnit_iff_isUnit_det Y).2 (isUnit_det_of_right_inverse hYinv)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < r := by omega
    have hθ := hc.eq_zero_of_lt i (by omega)
    simp only [hα, hβ, hi', ↓reduceIte, hθ, Real.cos_zero, Real.sin_zero, and_self]
  · intro i _ hi
    have hi' : i < r := hi
    simp only [hα, hβ, hi', ↓reduceIte]
    exact Real.cos_sq_add_sin_sq _
  · intro i
    simp only [hα, hβ]
    split_ifs
    · exact ⟨hc.cos_nonneg i, hc.sin_nonneg i⟩
    · exact ⟨le_rfl, le_rfl⟩
  · intro i hi
    have hi' : ¬ i < r := not_lt.2 hi
    simp only [hα, hβ, hi', ↓reduceIte, and_self]
  · rw [Matrix.mul_assoc, hAX]
    simp only [← Matrix.mul_assoc]
    rw [hc.star_mul_mul_left]
    ext i j
    rw [mul_rectDiagonal_apply]
    by_cases hj : (j : ℕ) < r <;> by_cases hij : (i : ℕ) = j <;>
      simp [rectDiagonal_apply, hα, hj, hij]
  · rw [Matrix.mul_assoc, hBX]
    simp only [← Matrix.mul_assoc]
    rw [hc.star_mul_mul_right, hp]
    ext i j
    rw [mul_rectDiagonal_apply]
    by_cases hij : (j : ℕ) = i + (r - m₂)
    · by_cases hj : (i : ℕ) + (r - m₂) < r <;>
        simp [shiftedRectDiagonal_apply, hβ, hj, hij, ← hr]
    · by_cases hj : (j : ℕ) < r <;> simp [shiftedRectDiagonal_apply, hβ, hj, hij, ← hr]

end Exists

/-! ### Consequences of a GSVD -/

section Consequences

variable {m₁ m₂ n : ℕ} {A : Matrix (Fin m₁) (Fin n) 𝕜} {B : Matrix (Fin m₂) (Fin n) 𝕜}
  {U₁ : Matrix (Fin m₁) (Fin m₁) 𝕜} {U₂ : Matrix (Fin m₂) (Fin m₂) 𝕜}
  {X : Matrix (Fin n) (Fin n) 𝕜} {α β : ℕ → ℝ}

/-- `Xᴴ Mᴴ M X = (Uᴴ M X)ᴴ (Uᴴ M X)` for unitary `U`. -/
private theorem conjTranspose_mul_gram_mul_eq {m : ℕ} {M : Matrix (Fin m) (Fin n) 𝕜}
    {U : Matrix (Fin m) (Fin m) 𝕜} (hU : U ∈ unitaryGroup (Fin m) 𝕜) :
    Xᴴ * (Mᴴ * M) * X = (star U * M * X)ᴴ * (star U * M * X) := by
  have hU' : U * Uᴴ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 hU
  simp only [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U, hU', Matrix.one_mul]

/-- **The GSVD diagonalizes `AᴴA`**: `Xᴴ AᴴA X = diag(α²)`, for `n ≤ m₁`. -/
theorem IsGSVD.conjTranspose_mul_gram_left_mul (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) :
    Xᴴ * (Aᴴ * A) * X = diagonal fun i : Fin n => ((α i ^ 2 : ℝ) : 𝕜) := by
  rw [conjTranspose_mul_gram_mul_eq h.mem_unitaryGroup_left, h.star_mul_mul_left,
    conjTranspose_rectDiagonal_mul_self]
  congr 1
  funext j
  rw [ite_eq_left (lt_of_lt_of_le j.isLt hnm), RCLike.star_def, RCLike.conj_ofReal]
  push_cast
  ring

/-- **The GSVD diagonalizes `BᴴB`**: `Xᴴ BᴴB X = diag(β²)`. The shift of `D_B` disappears, and the
`β_j` it does not see vanish. -/
theorem IsGSVD.conjTranspose_mul_gram_right_mul (h : IsGSVD A B U₁ U₂ X α β) :
    Xᴴ * (Bᴴ * B) * X = diagonal fun i : Fin n => ((β i ^ 2 : ℝ) : 𝕜) := by
  rw [conjTranspose_mul_gram_mul_eq h.mem_unitaryGroup_right, h.star_mul_mul_right,
    conjTranspose_shiftedRectDiagonal_mul_self]
  congr 1
  funext j
  split_ifs with hj
  · rw [RCLike.star_def, RCLike.conj_ofReal]
    push_cast
    ring
  · have hβ : β j = 0 := by
      rcases not_and_or.1 hj with hj | hj
      · exact (h.of_lt_p j (not_le.1 hj)).2
      · exact (h.of_le_r j (by omega)).2
    rw [hβ]
    simp

/-- **The GSVD diagonalizes `AᴴA + λ BᴴB`** ([golub2013matrix] §6.1.6, the display before
(6.1.26), and §6.2.6): `Xᴴ (AᴴA + λ BᴴB) X = diag(α_i² + λ β_i²)`, for `n ≤ m₁`. -/
theorem IsGSVD.conjTranspose_mul_gram_add_smul_gram_mul (h : IsGSVD A B U₁ U₂ X α β)
    (hnm : n ≤ m₁) (μ : ℝ) :
    Xᴴ * (Aᴴ * A + (μ : 𝕜) • (Bᴴ * B)) * X
      = diagonal fun i : Fin n => ((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    h.conjTranspose_mul_gram_left_mul hnm, h.conjTranspose_mul_gram_right_mul, ← diagonal_smul,
    diagonal_add]
  congr 1
  funext i
  push_cast
  rw [Pi.smul_apply, smul_eq_mul]

/-- **The inverse of `AᴴA + λ BᴴB` in GSVD coordinates**: when every `α_i² + λβ_i²` is nonzero,
`(AᴴA + λ BᴴB)⁻¹ = X diag(α² + λβ²)⁻¹ Xᴴ`, for `n ≤ m₁`. -/
theorem IsGSVD.inv_gram_add_smul_gram_eq (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) (μ : ℝ)
    (hd : ∀ i : Fin n, α i ^ 2 + μ * β i ^ 2 ≠ 0) :
    (Aᴴ * A + (μ : 𝕜) • (Bᴴ * B))⁻¹
      = X * diagonal (fun i : Fin n => (((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜))⁻¹) * Xᴴ := by
  have hG := h.conjTranspose_mul_gram_add_smul_gram_mul hnm μ
  have hXd : IsUnit X.det := (isUnit_iff_isUnit_det X).1 h.isUnit
  have hXG : Xᴴ * (Aᴴ * A + (μ : 𝕜) • (Bᴴ * B))
      = diagonal (fun i : Fin n => ((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜)) * X⁻¹ := by
    rw [← hG, Matrix.mul_assoc _ X, mul_nonsing_inv _ hXd, Matrix.mul_one]
  refine inv_eq_left_inv ?_
  rw [Matrix.mul_assoc, hXG, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal,
    show (fun i : Fin n => (((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜))⁻¹ *
        ((α i ^ 2 + μ * β i ^ 2 : ℝ) : 𝕜)) = fun _ => 1 from
      funext fun i => inv_mul_cancel₀ (RCLike.ofReal_ne_zero.2 (hd i)),
    diagonal_one, Matrix.one_mul, mul_nonsing_inv _ hXd]

/-- A matrix times a column of `X` is the column of the product. -/
private theorem mulVec_col_eq {m : Type*} (M : Matrix m (Fin n) 𝕜) (i : Fin n) :
    M *ᵥ X.col i = (M * X).col i := by
  ext k
  simp [mulVec, dotProduct, mul_apply, col_apply]

/-- If `Xᴴ M X = diag a` and `Xᴴ N X = diag b` with `X` invertible, then `b_i M x_i = a_i N x_i`
for every column `x_i` of `X`. -/
private theorem smul_mulVec_col_eq_of_conj_diagonal {M N : Matrix (Fin n) (Fin n) 𝕜}
    (hX : IsUnit X) {a b : Fin n → 𝕜} (hM : Xᴴ * M * X = diagonal a)
    (hN : Xᴴ * N * X = diagonal b) (i : Fin n) :
    b i • (M *ᵥ X.col i) = a i • (N *ᵥ X.col i) := by
  have hXh : IsUnit Xᴴ.det := by
    rw [det_conjTranspose]; exact ((isUnit_iff_isUnit_det X).1 hX).star
  have hMX : M * X = (Xᴴ)⁻¹ * diagonal a := by
    rw [← hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hXh, Matrix.one_mul]
  have hNX : N * X = (Xᴴ)⁻¹ * diagonal b := by
    rw [← hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hXh, Matrix.one_mul]
  have hmat : M * X * diagonal b = N * X * diagonal a := by
    rw [hMX, hNX, Matrix.mul_assoc, Matrix.mul_assoc, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 2
    funext j
    ring
  rw [mulVec_col_eq, mulVec_col_eq]
  ext k
  have := congrFun (congrFun hmat k) i
  simp only [mul_diagonal] at this
  simp only [Pi.smul_apply, smul_eq_mul, col_apply]
  rw [mul_comm, this, mul_comm]

/-- **The GSVD diagonalizes the pencil `AᴴA − μ² BᴴB`** ([golub2013matrix] §6.1.6, the remark
relating the GSVD to `AᵀA x = μ² BᵀB x`, taken up in §8.7.4): for `n ≤ m₁` and every column
`x_i` of `X`, `β_i² AᴴA x_i = α_i² BᴴB x_i`. -/
theorem IsGSVD.gram_mulVec_col (h : IsGSVD A B U₁ U₂ X α β) (hnm : n ≤ m₁) (i : Fin n) :
    ((β i ^ 2 : ℝ) : 𝕜) • ((Aᴴ * A) *ᵥ X.col i)
      = ((α i ^ 2 : ℝ) : 𝕜) • ((Bᴴ * B) *ᵥ X.col i) :=
  smul_mulVec_col_eq_of_conj_diagonal h.isUnit (h.conjTranspose_mul_gram_left_mul hnm)
    h.conjTranspose_mul_gram_right_mul i

/-- The common kernel of `A` and `B` is the kernel of the stacked matrix `[A; B]`. -/
theorem ker_inf_ker_eq_ker_fromRows {m₁ m₂ n : Type*} [Fintype n] (A : Matrix m₁ n 𝕜)
    (B : Matrix m₂ n 𝕜) :
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin
      = LinearMap.ker (fromRows A B).mulVecLin := by
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, mulVecLin_apply, fromRows_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    ext (_ | _) <;> rfl
  · intro h0
    exact ⟨funext fun k => congrFun h0 (Sum.inl k), funext fun k => congrFun h0 (Sum.inr k)⟩

/-- **The common kernel in GSVD coordinates**: `ker A ∩ ker B` is spanned by the columns `x_i` of
`X` with `i ≥ r = rank [A; B]`. They are killed by both (`α_i = β_i = 0`), they are independent,
and `ker A ∩ ker B = ker [A; B]` has dimension `n − r`. Used for (6.1.21) and (6.2.12):
`null(A) ∩ null(B) = {0}` iff `r = n`. -/
theorem IsGSVD.ker_inf_ker (h : IsGSVD A B U₁ U₂ X α β) :
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin
      = Submodule.span 𝕜 (X.col '' {i | (fromRows A B).rank ≤ (i : ℕ)}) := by
  classical
  set r := (fromRows A B).rank with hr
  have hAX : A * X = U₁ * rectDiagonal fun i => ((α i : ℝ) : 𝕜) := by
    rw [← h.star_mul_mul_left, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      mem_unitaryGroup_iff.1 h.mem_unitaryGroup_left, Matrix.one_mul]
  have hBX : B * X = U₂ * shiftedRectDiagonal (r - m₂) fun i => ((β i : ℝ) : 𝕜) := by
    rw [← h.star_mul_mul_right, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right, Matrix.one_mul]
  have hle : Submodule.span 𝕜 (X.col '' {i | r ≤ (i : ℕ)})
      ≤ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨hα, hβ⟩ := h.of_le_r i hi
    refine ⟨?_, ?_⟩
    · change A *ᵥ X.col i = 0
      rw [mulVec_col_eq, hAX]
      ext k
      rw [col_apply, mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [rectDiagonal_apply]
      split_ifs with hli
      · rw [hli, hα, RCLike.ofReal_zero, mul_zero]
      · rw [mul_zero]
    · change B *ᵥ X.col i = 0
      rw [mulVec_col_eq, hBX]
      ext k
      rw [col_apply, mul_apply]
      exact Finset.sum_eq_zero fun l _ => by simp [shiftedRectDiagonal_apply, hβ]
  have hcard : Fintype.card {i : Fin n // r ≤ (i : ℕ)} = n - r := by
    rw [← Fintype.card_fin (n - r)]
    exact Fintype.card_congr
      { toFun := fun i => ⟨i.1 - r, by have := i.1.isLt; have := i.2; omega⟩
        invFun := fun k => ⟨⟨k + r, by have := k.isLt; omega⟩, by
          change r ≤ (k : ℕ) + r; omega⟩
        left_inv := fun i => by
          apply Subtype.ext; apply Fin.ext
          simp only
          have := i.2
          omega
        right_inv := fun k => by
          apply Fin.ext
          simp }
  have hspan : Submodule.span 𝕜 (X.col '' {i | r ≤ (i : ℕ)})
      = Submodule.span 𝕜 (Set.range fun k : {i : Fin n // r ≤ (i : ℕ)} => X.col k) := by
    congr 1
    ext v
    simp
  have hfin : Module.finrank 𝕜 (Submodule.span 𝕜 (X.col '' {i | r ≤ (i : ℕ)})) = n - r := by
    rw [hspan]
    exact (finrank_span_eq_card (b := fun k : {i : Fin n // r ≤ (i : ℕ)} => X.col k)
      ((linearIndependent_cols_of_isUnit h.isUnit).comp _ Subtype.val_injective)).trans hcard
  have hker : Module.finrank 𝕜 (LinearMap.ker (fromRows A B).mulVecLin) = n - r := by
    have := LinearMap.finrank_range_add_finrank_ker (fromRows A B).mulVecLin
    rw [Module.finrank_fin_fun] at this
    change r + _ = n at this
    omega
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [hfin, ker_inf_ker_eq_ker_fromRows, hker]

/-- **The GSVD of `(A, I)` is an SVD of `A`** ([golub2013matrix] §6.1.6, "if `B = I_{n₁}` … we
obtain the SVD of `A`", made precise): then `p = 0`, `r = n`, `β_i > 0` for `i < n`, and
`U₁ᴴ A U₂ = diag(α_i / β_i)` — an SVD of `A` with singular values `α_i / β_i` (unsorted). The
book's "set `X = U₂`" is loose: `X` itself is `U₂ D_B`. -/
theorem IsGSVD.svd_of_eq_one {A : Matrix (Fin m₁) (Fin n) 𝕜} {U₂ : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsGSVD A (1 : Matrix (Fin n) (Fin n) 𝕜) U₁ U₂ X α β) :
    (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).rank - n = 0 ∧
      (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).rank = n ∧ (∀ i < n, 0 < β i) ∧
      star U₁ * A * U₂ = rectDiagonal fun i => ((α i / β i : ℝ) : 𝕜) := by
  classical
  set r := (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).rank with hr
  have hrn : r = n := by
    have hker : LinearMap.ker (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).mulVecLin = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      rw [mulVecLin_apply, fromRows_mulVec] at hv
      have := congrFun hv
      funext k
      simpa using this (Sum.inr k)
    have := LinearMap.finrank_range_add_finrank_ker
      (fromRows A (1 : Matrix (Fin n) (Fin n) 𝕜)).mulVecLin
    rw [Module.finrank_fin_fun, hker, finrank_bot] at this
    change r + 0 = n at this
    omega
  have hp : r - n = 0 := by omega
  have hD : star U₂ * X = diagonal fun i : Fin n => ((β i : ℝ) : 𝕜) := by
    have := h.star_mul_mul_right
    rw [Matrix.mul_one, ← hr, hp, shiftedRectDiagonal_zero, rectDiagonal_eq_diagonal] at this
    exact this
  have hX : X = U₂ * diagonal fun i : Fin n => ((β i : ℝ) : 𝕜) := by
    rw [← hD, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right,
      Matrix.one_mul]
  have hβ0 : ∀ i : Fin n, β i ≠ 0 := by
    have hdet := (isUnit_iff_isUnit_det X).1 h.isUnit
    rw [hX, det_mul, det_diagonal] at hdet
    have hprod := (isUnit_of_mul_isUnit_right hdet).ne_zero
    intro i hi
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, RCLike.ofReal_zero]))
  refine ⟨hp, hrn, fun i hi => lt_of_le_of_ne (h.nonneg i).2 (hβ0 ⟨i, hi⟩).symm, ?_⟩
  have hU₂ : U₂ = X * diagonal fun i : Fin n => (((β i : ℝ) : 𝕜))⁻¹ := by
    rw [hX, Matrix.mul_assoc, diagonal_mul_diagonal]
    conv_lhs => rw [← Matrix.mul_one U₂]
    congr 1
    rw [← diagonal_one]
    congr 1
    funext i
    rw [mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 (hβ0 i))]
  rw [hU₂, ← Matrix.mul_assoc, h.star_mul_mul_left]
  ext i j
  rw [mul_diagonal, rectDiagonal_apply, rectDiagonal_apply]
  split_ifs with hij
  · rw [hij]
    push_cast
    rw [div_eq_mul_inv]
  · rw [zero_mul]

end Consequences

end Matrix
