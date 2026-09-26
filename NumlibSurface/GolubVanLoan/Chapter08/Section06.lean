import Numlib.Analysis.InnerProductSpace.SingularValues
import Numlib.Eigen.Jacobi
import Numlib.LinearAlgebra.Matrix.Bidiagonal
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.PlaneRotation
import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.GolubVanLoan.Chapter05.Section04
import NumlibSurface.GolubVanLoan.Chapter08.Section03
import NumlibSurface.GolubVanLoan.Chapter08.Section05

/-!
# Golub–Van Loan §8.6: computing the SVD

Surface file for [golub2013matrix] §8.6: the connection (8.6.1)–(8.6.2) with the symmetric
eigenproblems of `AᵀA` and `AAᵀ`, the min–max characterization of singular values (Theorem
8.6.1), their perturbation (Corollary 8.6.2) and interlacing (Corollary 8.6.3), singular subspace
pairs, the tridiagonal matrix `BᵀB` of a bidiagonal `B` and its decoupling (§8.6.3), the
counterexample after Theorem 8.6.5, and the Jacobi SVD pieces of §8.6.4 (the `2 × 2` SVD by two
rotations, and the orthogonality of the one-sided Jacobi iterate).

## Conventions

`σ_k(A)` for `A : Matrix (Fin m) (Fin n) ℝ` is `A.sortedSingularValues (k - 1)` (Mathlib's sorted
`LinearMap.singularValues` of `toEuclideanLin A`, 0-based). Bidiagonal matrices are
`Matrix.IsUpperBidiagonal`.

The Jordan–Wielandt matrix is the backbone's `Matrix.hermitianDilation` (`[0 Aᵀ; A 0]`, domain
block first). Theorem 8.6.5 waits for its backbone node
`Matrix.exists_singularSubspacePair_perturbation`.

Algorithms 8.6.1–8.6.2 follow the conventions of `NumlibSurface/GolubVanLoan`: chapter 5's
`givens` and Givens updates on index lists, Algorithm 8.6.1 on a window of consecutive indices of
the `m × n` array with the accumulators `U`, `V`, Algorithm 8.6.2 on chapter 5's
bidiagonalization (Algorithm 5.4.2) with a `fuel`-bounded loop and a `done` flag.

## Readings

Algorithm 8.6.1 says "`B ∈ ℝ^{m×n}`" for what is square; Theorem 8.6.5 swaps `P` and `Q` and is
false for `m > n` as printed. The book's proof of Corollary 8.6.3 cites "Corollary 8.1.7" for
Theorem 8.1.7.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {m n : ℕ}

/-! ### §8.6.1 Connections to the symmetric eigenvalue problem -/

/-- **(8.6.1)–(8.6.2).** If `Uᵀ A V = Σ = diag(σ_1, …, σ_n)` is an SVD of
`A ∈ ℝ^{m×n}` (`m ≥ n`), then `Vᵀ (AᵀA) V = diag(σ_1², …, σ_n²)` and
`Uᵀ (AAᵀ) U = diag(σ_1², …, σ_n², 0, …, 0)`. -/
theorem equation_8_6_1 {A : Matrix (Fin m) (Fin n) ℝ} (hmn : n ≤ m) {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {σ : ℕ → ℝ} (hA : Uᵀ * A * V = rectDiagonal σ) :
    Vᵀ * (Aᵀ * A) * V = diagonal (fun j : Fin n => σ j ^ 2) ∧
      Uᵀ * (A * Aᵀ) * U = diagonal (fun i : Fin m => if (i : ℕ) < n then σ i ^ 2 else 0) := by
  have hUU : U * Uᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hVV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hUU' : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU
  have hVV' : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hV
  have hAV : A * V = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) := by
    rw [← hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hUA : Uᵀ * A = (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
    rw [← hA, Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hT : (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ)ᵀ = rectDiagonal σ := by
    rw [← conjTranspose_eq_transpose_of_trivial, conjTranspose_rectDiagonal]
    rfl
  constructor
  · have e : Vᵀ * (Aᵀ * A) * V =
        (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ)ᵀ * rectDiagonal σ := by
      calc Vᵀ * (Aᵀ * A) * V = (A * V)ᵀ * (A * V) := by
            simp only [transpose_mul, Matrix.mul_assoc]
        _ = _ := by
          rw [hAV, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU', Matrix.one_mul]
    rw [e, hT, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    congr 1
    funext j
    simp [show (j : ℕ) < m by omega, sq]
  · have e : Uᵀ * (A * Aᵀ) * U =
        rectDiagonal σ * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ)ᵀ := by
      calc Uᵀ * (A * Aᵀ) * U = (Uᵀ * A) * (Uᵀ * A)ᵀ := by
            simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
        _ = _ := by
          rw [hUA, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ,
            hVV', Matrix.one_mul]
    rw [e, hT, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    congr 1
    funext i
    split_ifs <;> simp [sq]

/-- The constant block matrix `M = [I I 0; I -I 0; 0 0 √2 I]` of (8.6.3), before the scaling:
`Mᵀ M = M Mᵀ = 2 I`. -/
private theorem jw_mul_self {n p : ℕ} :
    let M : Matrix (Fin n ⊕ (Fin n ⊕ Fin p)) (Fin n ⊕ (Fin n ⊕ Fin p)) ℝ :=
      fromBlocks 1 (fromCols 1 0) (fromRows 1 0) (fromBlocks (-1) 0 0 (√2 • 1))
    Mᵀ * M = (2 : ℝ) • 1 ∧ M * Mᵀ = (2 : ℝ) • 1 := by
  intro M
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  constructor <;>
  · ext (i | i | i) (j | j | j) <;>
      first
      | (simp [M, mul_apply, Fintype.sum_sum_type, one_apply, h2]; done)
      | (rcases eq_or_ne i j with rfl | h <;>
          [simp [M, mul_apply, Fintype.sum_sum_type, one_apply, h2];
           simp [M, mul_apply, Fintype.sum_sum_type, one_apply, h2, h, h.symm]]) <;> norm_num

/-- The Jordan–Wielandt sandwich of (8.6.3): `Mᵀ [0 [Σ 0]; [Σ; 0] 0] M = 2 diag(Σ, -Σ, 0)`. -/
private theorem jw_conj {n p : ℕ} (σ : Fin n → ℝ) :
    let M : Matrix (Fin n ⊕ (Fin n ⊕ Fin p)) (Fin n ⊕ (Fin n ⊕ Fin p)) ℝ :=
      fromBlocks 1 (fromCols 1 0) (fromRows 1 0) (fromBlocks (-1) 0 0 (√2 • 1))
    Mᵀ * fromBlocks 0 (fromCols (diagonal σ) 0) (fromRows (diagonal σ) 0) 0 * M =
      (2 : ℝ) • diagonal (Sum.elim σ (Sum.elim (-σ) 0)) := by
  intro M
  ext (i | i | i) (j | j | j) <;>
    first
    | (simp [M, mul_apply, Fintype.sum_sum_type, one_apply, diagonal_apply]; done)
    | (rcases eq_or_ne i j with rfl | h <;>
        [simp [M, mul_apply, Fintype.sum_sum_type, one_apply, diagonal_apply, two_mul];
         simp [M, mul_apply, Fintype.sum_sum_type, one_apply, diagonal_apply, h]])

/-- **(8.6.3).** Let `Uᵀ A V = [Σ; 0]`, `Σ = diag(σ₁, …, σ_n)`, be an SVD of `A ∈ ℝ^{m×n}` with
`U = [U₁ U₂]` (`n` and `m - n` columns) and `V` orthogonal. Then
`Q = (1/√2) [V V 0; U₁ -U₁ √2 U₂]` (block rows `n`, `m`; block columns `n`, `n`, `m - n`) is
orthogonal (`QᵀQ = QQᵀ = I`) and `Qᵀ [0 Aᵀ; A 0] Q = diag(σ₁, …, σ_n, -σ₁, …, -σ_n, 0, …, 0)`:
the eigenvalues of the Jordan–Wielandt matrix `Matrix.hermitianDilation A` are the `±σ_i` and
`m - n` zeros. -/
theorem equation_8_6_3 {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin n) ℝ}
    {U₂ : Matrix (Fin m) (Fin (m - n)) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hU : (fromCols U₁ U₂)ᵀ * fromCols U₁ U₂ = 1) (hU' : fromCols U₁ U₂ * (fromCols U₁ U₂)ᵀ = 1)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {σ : Fin n → ℝ}
    (hA : (fromCols U₁ U₂)ᵀ * A * V = fromRows (diagonal σ) 0) :
    let Q : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ (Fin n ⊕ Fin (m - n))) ℝ :=
      (√2)⁻¹ • fromBlocks V (fromCols V 0) U₁ (fromCols (-U₁) (√2 • U₂))
    Qᵀ * Q = 1 ∧ Q * Qᵀ = 1 ∧
      Qᵀ * hermitianDilation A * Q = diagonal (Sum.elim σ (Sum.elim (-σ) 0)) := by
  intro Q
  set U := fromCols U₁ U₂ with hUdef
  set M : Matrix (Fin n ⊕ (Fin n ⊕ Fin (m - n))) (Fin n ⊕ (Fin n ⊕ Fin (m - n))) ℝ :=
    fromBlocks 1 (fromCols 1 0) (fromRows 1 0) (fromBlocks (-1) 0 0 (√2 • 1)) with hM
  set W : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ (Fin n ⊕ Fin (m - n))) ℝ := fromBlocks V 0 0 U
    with hW
  have hVV : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hV
  have hVV' : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hQ : Q = (√2)⁻¹ • (W * M) := by
    simp only [Q, W, M, U, fromBlocks_multiply, mul_fromCols, fromCols_mul_fromRows,
      fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.mul_neg, Matrix.mul_smul]
  have hWW : Wᵀ * W = 1 := by
    rw [hW, fromBlocks_transpose, fromBlocks_multiply, hVV, hU]
    simp
  have hWW' : W * Wᵀ = 1 := by
    rw [hW, fromBlocks_transpose, fromBlocks_multiply, hVV', hU']
    simp
  have hD : Wᵀ * hermitianDilation A * W =
      fromBlocks 0 (fromCols (diagonal σ) 0) (fromRows (diagonal σ) 0) 0 := by
    have hA' : Vᵀ * Aᵀ * U = fromCols (diagonal σ) 0 := by
      have := congrArg transpose hA
      simpa [transpose_mul, Matrix.mul_assoc, transpose_fromRows] using this
    rw [hW, hermitianDilation, conjTranspose_eq_transpose_of_trivial, fromBlocks_transpose,
      fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, transpose_zero]
    rw [hA', hA]
  obtain ⟨hMM, hMM'⟩ := jw_mul_self (n := n) (p := m - n)
  have h2 : (√2)⁻¹ * (√2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2, transpose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hWW, Matrix.one_mul, hMM, smul_smul]
    norm_num
  · rw [hQ, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2, transpose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc M, hMM', Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, hWW', smul_smul]
    norm_num
  · rw [hQ, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2,
      transpose_mul, show Mᵀ * Wᵀ * hermitianDilation A * (W * M) =
        Mᵀ * (Wᵀ * hermitianDilation A * W) * M by simp only [Matrix.mul_assoc], hD,
      jw_conj σ, smul_smul]
    norm_num

/-- The linear equivalence between `ℝⁿ` as `EuclideanSpace` and as functions. -/
private abbrev euclideanEquiv' (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin n → ℝ)

/-! ### §8.6.1 Perturbation theory -/

/-- **Theorem 8.6.1 (min–max for singular values).** For `A ∈ ℝ^{m×n}` and `k < min(m, n)`
(0-based), `σ_k(A) = max_{dim S = k+1} min_{x ∈ S} ‖Ax‖₂/‖x‖₂` and
`σ_k(A) = min_{dim S = n-k} max_{x ∈ S, y ∈ ℝᵐ} yᵀAx / (‖x‖₂‖y‖₂)`, over subspaces `S ⊆ ℝⁿ`. -/
theorem theorem_8_6_1 (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ} (hkm : k < m) (hkn : k < n) :
    IsGreatest {c : ℝ | ∃ S : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ S = k + 1 ∧
      ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖} (A.sortedSingularValues k) ∧
    IsLeast {c : ℝ | ∃ S : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ S = n - k ∧
      ∀ x ∈ S, ∀ y : Fin m → ℝ, y ⬝ᵥ A *ᵥ x ≤ c * (‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖)}
      (A.sortedSingularValues k) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hk : k < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by rw [hfin]; exact hkn
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) := by
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    infer_instance
  set e := euclideanEquiv' n
  set T := toEuclideanLin A
  obtain ⟨hG1, hG2⟩ := T.isGreatest_singularValues hk
  obtain ⟨hL1, hL2⟩ := T.isLeast_singularValues_bilinear hk
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨S, hS, h⟩ := hG1
    refine ⟨S.map e.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hS], fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact h y hy
  · rintro c ⟨S, hS, h⟩
    refine hG2 ⟨S.map e.symm.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hS], fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact h y hy
  · obtain ⟨S, hS, h⟩ := hL1
    refine ⟨S.map e.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hS, hfin],
      fun x hx y => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    have := h z hz (WithLp.toLp 2 y)
    simpa [T, e, toEuclideanLin_apply, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using this
  · rintro c ⟨S, hS, h⟩
    refine hL2 ⟨S.map e.symm.toLinearMap, by rw [LinearEquiv.finrank_map_eq, hS, hfin],
      fun x hx y => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    have := h z hz (WithLp.ofLp y)
    simpa [T, e, toEuclideanLin_toLp, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm] using this

open scoped Matrix.Norms.L2Operator in
/-- **Corollary 8.6.2.** For `A, E ∈ ℝ^{m×n}` and every `k`,
`|σ_k(A + E) - σ_k(A)| ≤ σ_1(E) = ‖E‖₂`. -/
theorem corollary_8_6_2 (A E : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    |(A + E).sortedSingularValues k - A.sortedSingularValues k| ≤ E.sortedSingularValues 0 ∧
      E.sortedSingularValues 0 = lpOpNorm 2 E := by
  have hE : E.sortedSingularValues 0 = lpOpNorm 2 E := by
    rw [lpOpNorm_two, sortedSingularValues_zero_eq_l2_opNorm]
  refine ⟨?_, hE⟩
  rw [hE, lpOpNorm_two]
  refine LinearMap.abs_singularValues_sub_le (norm_nonneg E) (fun x => ?_) k
  rw [map_add, add_sub_cancel_left]
  exact norm_toEuclideanLin_apply_le E x

open scoped Matrix.Norms.L2Operator in
/-- The Jordan–Wielandt matrix `[0 Eᵀ; E 0]` has the `2`-norm of `E`: at most by the block bound
`Matrix.l2_opNorm_fromBlocks_le` (zero diagonal blocks), at least because `E` is a submatrix. -/
private theorem lpOpNorm_hermitianDilation (E : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 (hermitianDilation E) = lpOpNorm 2 E := by
  apply le_antisymm
  · rw [lpOpNorm_two, lpOpNorm_two]
    have h := l2_opNorm_fromBlocks_le (E := (0 : Matrix (Fin n) (Fin n) ℝ)) (C := Eᴴ) (C' := E)
      (D := (0 : Matrix (Fin m) (Fin m) ℝ)) (μ := 0) (γ := ‖E‖) (δ := 0) (by simp)
      (by rw [l2_opNorm_conjTranspose]) le_rfl (by simp)
    have hs : √((0 - 0) ^ 2 + 4 * ‖E‖ ^ 2) = 2 * ‖E‖ := by
      rw [show ((0 : ℝ) - 0) ^ 2 + 4 * ‖E‖ ^ 2 = (2 * ‖E‖) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [hs, zero_add, zero_add, mul_div_cancel_left₀ _ two_ne_zero] at h
    exact h
  · have h := lpOpNorm_submatrix_le (p := 2) (hermitianDilation E) Sum.inr_injective
      Sum.inl_injective
    have he : (hermitianDilation E).submatrix Sum.inr Sum.inl = E := by
      ext i j; simp [hermitianDilation]
    rwa [he] at h

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **(8.6.4)**: the Jordan–Wielandt matrices `Ã = [0 Aᵀ; A 0]` and
`Ã + Ẽ = [0 (A + E)ᵀ; A + E 0]` differ by `Ẽ = [0 Eᵀ; E 0]` (`Matrix.hermitianDilation`), and
`‖Ẽ‖_F² = 2 ‖E‖_F²`, `‖Ẽ‖₂ = ‖E‖₂` — the norms that turn Theorem 8.1.4 and Corollary 8.1.6 for
`Ã` into Theorem 8.6.4 and Corollary 8.6.2. -/
theorem equation_8_6_4 (A E : Matrix (Fin m) (Fin n) ℝ) :
    hermitianDilation E = fromBlocks 0 Eᵀ E 0 ∧
      hermitianDilation (A + E) = hermitianDilation A + hermitianDilation E ∧
      ‖hermitianDilation E‖ ^ 2 = 2 * ‖E‖ ^ 2 ∧
      lpOpNorm 2 (hermitianDilation E) = lpOpNorm 2 E :=
  ⟨by rw [hermitianDilation, conjTranspose_eq_transpose_of_trivial], hermitianDilation_add A E,
    frobenius_norm_hermitianDilation_sq E, lpOpNorm_hermitianDilation E⟩

/-- **Theorem 8.6.4 (Wielandt–Hoffman for singular values).** For `A, E ∈ ℝ^{m×n}` with `m ≥ n`,
`∑_{k=1}^n (σ_k(A + E) - σ_k(A))² ≤ ‖E‖_F²`. The backbone's
`Matrix.sum_sq_sortedSingularValues_sub_le`, whose proof is the book's (Theorem 8.1.4 for the
matrices (8.6.4)). -/
theorem theorem_8_6_4 (hmn : n ≤ m) (A E : Matrix (Fin m) (Fin n) ℝ) :
    ∑ k : Fin n, ((A + E).sortedSingularValues k - A.sortedSingularValues k) ^ 2 ≤ ‖E‖ ^ 2 := by
  have h := sum_sq_sortedSingularValues_sub_le A E
  rwa [Fintype.card_fin, Fintype.card_fin, min_eq_right hmn,
    ← Fin.sum_univ_eq_sum_range (fun k => ((A + E).sortedSingularValues k -
      A.sortedSingularValues k) ^ 2)] at h

end Frobenius

/-- **Corollary 8.6.3 (interlacing).** For `A = [a_1 | ⋯ | a_n] ∈ ℝ^{m×n}` and `A_r` its first `r`
columns: `σ_k(A_{r+1}) ≥ σ_k(A_r) ≥ σ_{k+1}(A_{r+1})` for `k < r` (0-based), i.e. the chain
`σ_1(A_{r+1}) ≥ σ_1(A_r) ≥ σ_2(A_{r+1}) ≥ ⋯ ≥ σ_r(A_r) ≥ σ_{r+1}(A_{r+1})`. -/
theorem corollary_8_6_3 (A : Matrix (Fin m) (Fin n) ℝ) {r : ℕ} (hr : r + 1 ≤ n) (k : ℕ) :
    (A.submatrix id (Fin.castLE (by omega : r ≤ n))).sortedSingularValues k ≤
        (A.submatrix id (Fin.castLE hr)).sortedSingularValues k ∧
      (A.submatrix id (Fin.castLE hr)).sortedSingularValues (k + 1) ≤
        (A.submatrix id (Fin.castLE (by omega : r ≤ n))).sortedSingularValues k := by
  -- the first `r` columns of `A_{r+1}` through the zero-extension isometry
  set P : Matrix (Fin (r + 1)) (Fin r) ℝ := (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ).submatrix id
    Fin.castSucc
  have hP : Pᴴ * P = 1 := by
    ext i j
    simp [P, mul_apply, one_apply, Fin.castSucc_inj]
  let ι : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r + 1)) :=
    { toLinearMap := toEuclideanLin P
      norm_map' := norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hP }
  have hcomp : toEuclideanLin (A.submatrix id (Fin.castLE hr)) ∘ₗ ι.toLinearMap =
      toEuclideanLin (A.submatrix id (Fin.castLE (by omega : r ≤ n))) := by
    change toEuclideanLin _ ∘ₗ toEuclideanLin P = _
    rw [← toEuclideanLin_mul]
    congr 1
    ext i j
    simp only [P, mul_apply, submatrix_apply, id, one_apply]
    rw [Finset.sum_eq_single (Fin.castSucc j)]
    · simp [Fin.castLE_castSucc]
    · intro b _ hb; simp [hb]
    · simp
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) + 1 =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (r + 1))) := by simp
  refine ⟨?_, ?_⟩
  · have := LinearMap.singularValues_comp_linearIsometry_le
      (toEuclideanLin (A.submatrix id (Fin.castLE hr))) ι k
    rwa [hcomp] at this
  · have := LinearMap.singularValues_add_le_singularValues_comp_linearIsometry
      (toEuclideanLin (A.submatrix id (Fin.castLE hr))) ι hdim k
    rwa [hcomp] at this

/-- **§8.6.2, singular subspace pairs**: subspaces `S ⊆ ℝⁿ`, `T ⊆ ℝᵐ` of equal dimension form a
singular subspace pair for `A` if `x ∈ S ⟹ Ax ∈ T` and `y ∈ T ⟹ Aᵀy ∈ S`. -/
def IsSingularSubspacePair (A : Matrix (Fin m) (Fin n) ℝ)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
  Module.finrank ℝ S = Module.finrank ℝ T ∧ S.map (toEuclideanLin A) ≤ T ∧
    T.map (toEuclideanLin Aᵀ) ≤ S

/-! ### §8.6.3 The SVD algorithm -/

/-- **§8.6.3, `BᵀB` of a bidiagonal `B`.** For upper bidiagonal `B` with diagonal `d` and
superdiagonal `f`, `T = BᵀB` is symmetric tridiagonal with `t_ii = d_i² + f_{i-1}²` and
`t_{i,i+1} = d_i f_i`, and `T` is unreduced iff every `d_i f_i ≠ 0`. Moreover a bidiagonalization
`Uᵀ A V = B` (square case) gives the tridiagonal decomposition `Vᵀ (AᵀA) V = BᵀB`. -/
theorem gram_bidiagonal {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsUpperBidiagonal) :
    (Bᵀ * B).IsSymm ∧ (Bᵀ * B).IsTridiagonal ∧
      (∀ i : Fin n, (Bᵀ * B) i i =
        B i i ^ 2 + ∑ j : Fin n, if (j : ℕ) + 1 = i then B j i ^ 2 else 0) ∧
      (∀ (i j : Fin n), (j : ℕ) = i + 1 → (Bᵀ * B) i j = B i i * B i j) ∧
      (IsUnreducedTridiagonal (Bᵀ * B) ↔
        ∀ (i j : Fin n), (j : ℕ) = i + 1 → B i i * B i j ≠ 0) := by
  -- the support of a bidiagonal matrix
  have hsupp : ∀ i j : Fin n, B i j ≠ 0 → (j : ℕ) = i ∨ (j : ℕ) = i + 1 := fun i j h => by
    by_contra hc
    push Not at hc
    refine h (hB i j ?_)
    rcases lt_or_ge (j : ℕ) i with hji | hji
    · exact Or.inl (Fin.lt_def.2 hji)
    · exact Or.inr ⟨⟨i + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩
  have hsymm : (Bᵀ * B).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_transpose]
  have hentry : ∀ i j : Fin n, (Bᵀ * B) i j = ∑ k, B k i * B k j := fun i j => by
    simp [mul_apply]
  have htri : (Bᵀ * B).IsTridiagonal := fun i j hij => by
    rw [hentry]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_contra h0
    have h1 := hsupp k i (left_ne_zero_of_mul h0)
    have h2 := hsupp k j (right_ne_zero_of_mul h0)
    rcases hij with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩ <;>
      simp only [Fin.lt_def] at hc1 hc2 <;> omega
  have hsuper : ∀ (i j : Fin n), (j : ℕ) = i + 1 → (Bᵀ * B) i j = B i i * B i j := by
    intro i j hij
    rw [hentry, Finset.sum_eq_single i]
    · intro k _ hki
      by_contra h0
      have h1 := hsupp k i (left_ne_zero_of_mul h0)
      have h2 := hsupp k j (right_ne_zero_of_mul h0)
      have : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
      omega
    · simp
  refine ⟨hsymm, htri, fun i => ?_, hsuper, ?_⟩
  · have hterm : ∀ k : Fin n, B k i * B k i =
        (if k = i then B i i ^ 2 else 0) + (if (k : ℕ) + 1 = i then B k i ^ 2 else 0) := by
      intro k
      by_cases hk : k = i
      · subst hk; simp [sq]
      · by_cases hk' : (k : ℕ) + 1 = i
        · simp [hk, hk', sq]
        · have h0 : B k i = 0 := by
            by_contra h0
            rcases hsupp k i h0 with h | h
            · exact hk (Fin.ext h.symm)
            · exact hk' h.symm
          simp [hk, hk', h0]
    rw [hentry, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp
  · rw [IsUnreducedTridiagonal, isUnreducedUpperHessenberg_iff_fin]
    constructor
    · rintro ⟨-, -, h⟩ i j hij
      have h1 := h i (by have := j.isLt; omega)
      have e : (⟨(i : ℕ) + 1, by have := j.isLt; omega⟩ : Fin n) = j := Fin.ext hij.symm
      rw [e, Fin.eta] at h1
      rw [← hsuper i j hij, ← hsymm.apply i j]
      exact h1
    · intro h
      refine ⟨htri, htri.isUpperHessenberg, fun k hk => ?_⟩
      rw [← hsymm.apply]
      rw [hsuper ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl]
      exact h _ _ rfl

/-! ### §8.6.4 Jacobi SVD procedures -/

/-- The book's `2 × 2` rotation `[c s; -s c]` is the plane rotation `planeRotation 0 1 c (-s)`. -/
private theorem planeRotation_fin_two (c s : ℝ) :
    planeRotation (0 : Fin 2) 1 c (-s) = !![c, s; -s, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeRotation_apply]

/-- A `2 × 2` matrix with vanishing off-diagonal entries is diagonal. -/
private theorem eq_diagonal_of_fin_two {N : Matrix (Fin 2) (Fin 2) ℝ} (h01 : N 0 1 = 0)
    (h10 : N 1 0 = 0) : N = diagonal fun i => N i i := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

/-- **§8.6.4, the two-sided Jacobi SVD subproblem** (P8.6.5). For every real `2 × 2`
`M = [a_pp a_pq; a_qp a_qq]` there are rotations `(c₁, s₁)`, `(c₂, s₂)` with
`[c₁ s₁; -s₁ c₁]ᵀ M [c₂ s₂; -s₂ c₂] = diag(d_p, d_q)`: a rotation that makes `M` symmetric
(P8.6.5(a)), then the symmetric Schur rotation of Algorithm 8.5.1 (the backbone's
`Matrix.jacobiRotation`). And the two-sided update `B = J(p,q,θ₁)ᵀ A J(p,q,θ₂)` of an `n × n` `A`
by these rotations of its `(p, q)` block zeroes `b_pq`, `b_qp` with
`off(B)² = off(A)² - a_pq² - a_qp²` (P8.6.5(c)). -/
theorem jacobiSVD_twoByTwo :
    (∀ M : Matrix (Fin 2) (Fin 2) ℝ, ∃ c₁ s₁ c₂ s₂ : ℝ, c₁ ^ 2 + s₁ ^ 2 = 1 ∧
      c₂ ^ 2 + s₂ ^ 2 = 1 ∧ ∃ d : Fin 2 → ℝ,
        (!![c₁, s₁; -s₁, c₁])ᵀ * M * !![c₂, s₂; -s₂, c₂] = diagonal d) ∧
    ∀ (A : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n}, p ≠ q → ∃ c₁ s₁ c₂ s₂ : ℝ,
      c₁ ^ 2 + s₁ ^ 2 = 1 ∧ c₂ ^ 2 + s₂ ^ 2 = 1 ∧
        ((planeRotation p q c₁ (-s₁))ᵀ * A * planeRotation p q c₂ (-s₂)) p q = 0 ∧
        ((planeRotation p q c₁ (-s₁))ᵀ * A * planeRotation p q c₂ (-s₂)) q p = 0 ∧
        off ((planeRotation p q c₁ (-s₁))ᵀ * A * planeRotation p q c₂ (-s₂)) ^ 2 =
          off A ^ 2 - A p q ^ 2 - A q p ^ 2 := by
  -- the `2 × 2` problem
  have h2 : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, ∃ c₁ s₁ c₂ s₂ : ℝ, c₁ ^ 2 + s₁ ^ 2 = 1 ∧
      c₂ ^ 2 + s₂ ^ 2 = 1 ∧ ∃ d : Fin 2 → ℝ,
        (!![c₁, s₁; -s₁, c₁])ᵀ * M * !![c₂, s₂; -s₂, c₂] = diagonal d := by
    intro M
    -- a rotation `R₀ = [c s; -s c]` making `R₀ M` symmetric: `c (m₀₁ - m₁₀) + s (m₁₁ + m₀₀) = 0`
    set c := (givensPair (M 1 1 + M 0 0) (M 1 0 - M 0 1)).1
    set s := (givensPair (M 1 1 + M 0 0) (M 1 0 - M 0 1)).2
    have hcs : c ^ 2 + s ^ 2 = 1 := givensPair_sq_add_sq _ _
    have hsym0 : c * (M 0 1 - M 1 0) + s * (M 1 1 + M 0 0) = 0 := by
      have := (givensPair_fst_mul_add_snd_mul (M 1 1 + M 0 0) (M 1 0 - M 0 1)).2
      linear_combination -this
    set S := !![c, s; -s, c] * M
    have hS : S.IsSymm := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [S, Fin.sum_univ_two, vecMul, dotProduct] <;> linarith [hsym0]
    -- the symmetric Schur rotation of `S`
    set cJ := jacobiCos S 0 1
    set sJ := jacobiSin S 0 1
    have hJ : jacobiRotation S 0 1 = !![cJ, -sJ; sJ, cJ] := by
      have h := planeRotation_fin_two cJ (-sJ)
      simp only [neg_neg] at h
      rw [jacobiRotation]
      exact h
    have hcsJ : cJ ^ 2 + sJ ^ 2 = 1 := jacobiCos_sq_add_jacobiSin_sq S 0 1
    have hzero : jacobiStep S 0 1 0 1 = 0 := jacobiStep_apply_eq_zero S hS (by decide)
    have hzero' : jacobiStep S 0 1 1 0 = 0 :=
      ((isSymm_jacobiStep hS 0 1).apply 0 1).trans hzero
    refine ⟨c * cJ - s * sJ, -(c * sJ + s * cJ), cJ, -sJ, ?_, by rw [neg_sq]; exact hcsJ,
      fun i => jacobiStep S 0 1 i i, ?_⟩
    · linear_combination (cJ ^ 2 + sJ ^ 2) * hcs + hcsJ
    · have hL : (!![c * cJ - s * sJ, -(c * sJ + s * cJ); -(-(c * sJ + s * cJ)), c * cJ - s * sJ])ᵀ =
          (jacobiRotation S 0 1)ᵀ * !![c, s; -s, c] := by
        rw [hJ]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> ring
      have hR : !![cJ, -sJ; -(-sJ), cJ] = jacobiRotation S 0 1 := by rw [hJ, neg_neg]
      rw [hL, hR, Matrix.mul_assoc (jacobiRotation S 0 1)ᵀ !![c, s; -s, c] M]
      exact eq_diagonal_of_fin_two hzero hzero'
  refine ⟨h2, fun A p q hpq => ?_⟩
  obtain ⟨c₁, s₁, c₂, s₂, h1, h2', d, hd⟩ := h2 !![A p p, A p q; A q p, A q q]
  refine ⟨c₁, s₁, c₂, s₂, h1, h2', ?_⟩
  set G₁ := planeRotation p q c₁ (-s₁)
  set G₂ := planeRotation p q c₂ (-s₂)
  set B := G₁ᵀ * A * G₂
  -- the entries of `B`
  have hB : ∀ i j, B i j =
      if i = p then c₁ * (A * G₂) p j + -s₁ * (A * G₂) q j
      else if i = q then -(-s₁) * (A * G₂) p j + c₁ * (A * G₂) q j
      else (A * G₂) i j := fun i j => by
    simp only [B, G₁, Matrix.mul_assoc]
    exact transpose_planeRotation_mul_apply hpq _ i j
  have hAG : ∀ i j, (A * G₂) i j =
      if j = p then c₂ * A i p + -s₂ * A i q
      else if j = q then -(-s₂) * A i p + c₂ * A i q
      else A i j := fun i j => mul_planeRotation_apply hpq A i j
  -- the `(p, q)` block of `B` is the `2 × 2` product
  have hblock : ∀ a b : Fin 2, B (![p, q] a) (![p, q] b) =
      ((!![c₁, s₁; -s₁, c₁])ᵀ * !![A p p, A p q; A q p, A q q] * !![c₂, s₂; -s₂, c₂]) a b := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [hB, hAG, hpq.symm, mul_apply, Fin.sum_univ_two] <;> ring
  have hpq0 : B p q = 0 := by
    have := hblock 0 1; rw [hd] at this; simpa using this
  have hqp0 : B q p = 0 := by
    have := hblock 1 0; rw [hd] at this; simpa using this
  refine ⟨hpq0, hqp0, ?_⟩
  -- the diagonal outside the plane is unchanged, the Frobenius mass of the block is preserved
  have hdiag : ∀ i, i ≠ p → i ≠ q → B i i = A i i := fun i hip hiq => by
    simp only [hB, hAG]; simp [hip, hiq]
  have hbpp : B p p = c₁ * (c₂ * A p p + -s₂ * A p q) + -s₁ * (c₂ * A q p + -s₂ * A q q) := by
    simp [hB, hAG]
  have hbqq : B q q = -(-s₁) * (-(-s₂) * A p p + c₂ * A p q) +
      c₁ * (-(-s₂) * A q p + c₂ * A q q) := by
    simp [hB, hAG, hpq.symm]
  have hbpq : B p q =
      c₁ * (-(-s₂) * A p p + c₂ * A p q) + -s₁ * (-(-s₂) * A q p + c₂ * A q q) := by
    simp [hB, hAG, hpq.symm]
  have hbqp : B q p =
      -(-s₁) * (c₂ * A p p + -s₂ * A p q) + c₁ * (c₂ * A q p + -s₂ * A q q) := by
    simp [hB, hAG, hpq.symm]
  have hmass : B p p ^ 2 + B q q ^ 2 = A p p ^ 2 + A q q ^ 2 + A p q ^ 2 + A q p ^ 2 := by
    have e : B p p ^ 2 + B q q ^ 2 + B p q ^ 2 + B q p ^ 2 =
        A p p ^ 2 + A q q ^ 2 + A p q ^ 2 + A q p ^ 2 := by
      rw [hbpp, hbqq, hbpq, hbqp]
      linear_combination (A p p ^ 2 + A q q ^ 2 + A p q ^ 2 + A q p ^ 2) *
        ((c₂ ^ 2 + s₂ ^ 2) * h1 + h2')
    rw [hpq0, hqp0] at e
    linarith
  have hsumdiag : ∑ i, B i i ^ 2 = ∑ i, A i i ^ 2 + A p q ^ 2 + A q p ^ 2 := by
    have e := Fintype.sum_eq_add p q hpq (f := fun i => B i i ^ 2 - A i i ^ 2) fun i hi => by
      simp [hdiag i hi.1 hi.2]
    rw [Finset.sum_sub_distrib] at e
    linarith
  -- the Frobenius mass of `B` is that of `A`
  have hG₁ : G₁ᵀ ∈ unitaryGroup (Fin n) ℝ := by
    rw [planeRotation_transpose hpq]
    exact planeRotation_mem_orthogonalGroup hpq (by rw [neg_neg]; linarith [neg_sq s₁])
  have hG₂ : G₂ ∈ unitaryGroup (Fin n) ℝ :=
    planeRotation_mem_orthogonalGroup hpq (by rw [neg_sq]; exact h2')
  have hfro : ∑ i, ∑ j, B i j ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
    have h := congrArg (· ^ 2) (frobenius_norm_unitary_mul_mul_unitary hG₁ A hG₂)
    simp only [frobenius_norm_sq_eq_sum_sq, Real.norm_eq_abs, sq_abs] at h
    exact h
  rw [off_sq, off_sq]
  have eB := offDiagNormSq_add_sum_diag_sq_real B
  have eA := offDiagNormSq_add_sum_diag_sq_real A
  linarith

/-- **§8.6.4, one-sided Jacobi.** For `A ∈ ℝ^{m×n}`, `p ≠ q` and a rotation `J = J(p,q,θ)`, the
inner product of columns `p` and `q` of `A J` is `(Jᵀ(AᵀA)J)_{pq}`, so they are orthogonal iff that
entry vanishes, and the rotation of Algorithm 8.5.1 for `AᵀA` achieves it. And if `A V` has
orthogonal columns, then `A V = U Σ` with `Σ = diag(‖(AV)(:, j)‖₂)` and `U` with orthogonal
columns, the nonzero ones of unit length (the column scaling that finishes the SVD). -/
theorem oneSidedJacobi_orthogonal (A : Matrix (Fin m) (Fin n) ℝ) {p q : Fin n} (hpq : p ≠ q) :
    (∀ c s : ℝ, (A * planeRotation p q c (-s)).col p ⬝ᵥ (A * planeRotation p q c (-s)).col q =
      ((planeRotation p q c (-s))ᵀ * (Aᵀ * A) * planeRotation p q c (-s)) p q) ∧
    (A * planeRotation p q (jacobiCosSmall (Aᵀ * A) p q) (-jacobiSinSmall (Aᵀ * A) p q)).col p ⬝ᵥ
      (A * planeRotation p q (jacobiCosSmall (Aᵀ * A) p q) (-jacobiSinSmall (Aᵀ * A) p q)).col q =
        0 ∧
    ∀ V : Matrix (Fin n) (Fin n) ℝ, (∀ i j, i ≠ j → (A * V).col i ⬝ᵥ (A * V).col j = 0) →
      ∃ U : Matrix (Fin m) (Fin n) ℝ,
        A * V = U * diagonal (fun j => ‖WithLp.toLp 2 ((A * V).col j)‖) ∧
        (∀ i j, i ≠ j → U.col i ⬝ᵥ U.col j = 0) ∧
        ∀ j, (A * V).col j ≠ 0 → U.col j ⬝ᵥ U.col j = 1 := by
  have hdot : ∀ {k : ℕ} (M : Matrix (Fin m) (Fin k) ℝ) (i j : Fin k),
      M.col i ⬝ᵥ M.col j = (Mᵀ * M) i j := fun M i j => by
    simp [dotProduct, mul_apply, col_apply]
  have hconj : ∀ c s : ℝ, (A * planeRotation p q c (-s)).col p ⬝ᵥ
      (A * planeRotation p q c (-s)).col q =
        ((planeRotation p q c (-s))ᵀ * (Aᵀ * A) * planeRotation p q c (-s)) p q := fun c s => by
    rw [hdot, transpose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨hconj, ?_, fun V hV => ?_⟩
  · have hsym : (Aᵀ * A).IsSymm := by rw [IsSymm, transpose_mul, transpose_transpose]
    rw [hconj, ← jacobiRotation_eq_planeRotation_small]
    exact jacobiStep_apply_eq_zero (Aᵀ * A) hsym hpq
  · set σ : Fin n → ℝ := fun j => ‖WithLp.toLp 2 ((A * V).col j)‖
    have hσ0 : ∀ j, σ j = 0 → (A * V).col j = 0 := fun j h => by
      have : (WithLp.toLp 2 ((A * V).col j) : EuclideanSpace ℝ (Fin m)) = 0 := norm_eq_zero.1 h
      simpa using congrArg WithLp.ofLp this
    refine ⟨Matrix.of fun i j => (σ j)⁻¹ * (A * V) i j, ?_, fun i j hij => ?_, fun j hj => ?_⟩
    · ext i j
      rw [mul_diagonal, of_apply]
      by_cases h : σ j = 0
      · have := congrFun (hσ0 j h) i
        simp only [col_apply, Pi.zero_apply] at this
        simp [h, this]
      · field_simp
    · have := hV i j hij
      simp only [dotProduct, col_apply, of_apply] at this ⊢
      calc ∑ x, (σ i)⁻¹ * (A * V) x i * ((σ j)⁻¹ * (A * V) x j) =
            (σ i)⁻¹ * (σ j)⁻¹ * ∑ x, (A * V) x i * (A * V) x j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        _ = 0 := by rw [this, mul_zero]
    · have hne : σ j ≠ 0 := fun h => hj (hσ0 j h)
      have hsq : (A * V).col j ⬝ᵥ (A * V).col j = σ j ^ 2 := dotProduct_self_eq_norm_sq _
      simp only [dotProduct, col_apply, of_apply] at hsq ⊢
      calc ∑ x, (σ j)⁻¹ * (A * V) x j * ((σ j)⁻¹ * (A * V) x j) =
            (σ j)⁻¹ ^ 2 * ∑ x, (A * V) x j * (A * V) x j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        _ = 1 := by rw [hsq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hne)]

/-! ### §8.6.2 The failure of Theorem 8.6.5 for `m > n` -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Theorem 8.6.5 is false as printed for `m > n`.** For `m = 3`, `n = 2`, `r = 1`,
`A = [0 0; 0 1; 0 0]`, `U = I₃`, `V = I₂` (so `A₁₁ = [0]`, `A₂₂ = [1; 0]` and the printed gap is
`δ = 1`) and `E = ε e₃e₁ᵀ` with `0 < ε ≤ 1/5` (so `‖E‖_F = ε ≤ δ/5`), no `P`, `Q` make
`(ran(V₁ + V₂ P), ran(U₁ + U₂ Q))` a singular subspace pair for `A + E`, whatever their size. The
corrected hypothesis `δ ≤ σ_min(A₁₁) = 0` of `theorem_8_6_5` fails here. -/
theorem theorem_8_6_5_counterexample {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 5) :
    let A : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 1; 0, 0]
    let E : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 0, 0; ε, 0]
    let V₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    let V₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
    let U₁ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]
    let U₂ : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 1, 0; 0, 1]
    ‖E‖ = ε ∧ ‖E‖ ≤ 1 / 5 ∧
      ¬ ∃ (P : Matrix (Fin 1) (Fin 1) ℝ) (Q : Matrix (Fin 2) (Fin 1) ℝ),
        IsSingularSubspacePair (A + E) (LinearMap.range (toEuclideanLin (V₁ + V₂ * P)))
          (LinearMap.range (toEuclideanLin (U₁ + U₂ * Q))) := by
  intro A E V₁ V₂ U₁ U₂
  have hE : ‖E‖ = ε := by
    have h' : ‖E‖ ^ 2 = ε ^ 2 := by
      rw [frobenius_norm_sq_eq_sum_sq]
      simp [E, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    exact (pow_left_inj₀ (norm_nonneg _) hε.le two_ne_zero).1 h'
  refine ⟨hE, hE ▸ hε', ?_⟩
  rintro ⟨P, Q, -, hST, -⟩
  -- `(A + E) (1, p) = (0, p, ε)` must be a multiple of `(1, q₁, q₂)`
  have hmem : toEuclideanLin (A + E) (toEuclideanLin (V₁ + V₂ * P) (WithLp.toLp 2 ![1])) ∈
      LinearMap.range (toEuclideanLin (U₁ + U₂ * Q)) :=
    hST (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ _))
  obtain ⟨y, hy⟩ := hmem
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hy
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hy
  simp [A, E, V₁, V₂, U₁, U₂, toEuclideanLin_apply, dotProduct, Fin.sum_univ_succ, vecMul,
    vecHead, vecTail] at h0 h2
  simp only [h0, mul_zero] at h2
  linarith

end Frobenius


/-- The row chase of §8.6.3 (the bulge in row `k` moves one column right per rotation): if the
rows other than `k` have the bidiagonal pattern and row `k` is supported in column `j`, a rotation
in the plane `(j, k)` with the Givens pair of `(c_jj, c_kj)` keeps the pattern and moves the
support of row `k` to column `j + 1`. -/
private theorem rowChase_step {C : Matrix (Fin n) (Fin n) ℝ} {k j : Fin n} (hkj : k < j)
    (hrows : ∀ i l, i ≠ k → C i l ≠ 0 → l = i ∨ (l : ℕ) = i + 1)
    (hrow : ∀ l, C k l ≠ 0 → l = j) :
    let R := planeRotation j k (givensPair (C j j) (C k j)).1 (givensPair (C j j) (C k j)).2
    (∀ i l, i ≠ k → (Rᵀ * C) i l ≠ 0 → l = i ∨ (l : ℕ) = i + 1) ∧
      (∀ l, (Rᵀ * C) k l ≠ 0 → (l : ℕ) = j + 1) := by
  intro R
  have hjk : j ≠ k := (ne_of_lt hkj).symm
  have hkj' : k ≠ j := ne_of_lt hkj
  obtain ⟨-, h2⟩ := givensPair_fst_mul_add_snd_mul (C j j) (C k j)
  set c := (givensPair (C j j) (C k j)).1
  set s := (givensPair (C j j) (C k j)).2
  have happ : ∀ p q, (Rᵀ * C) p q =
      if p = j then c * C j q + s * C k q
      else if p = k then -s * C j q + c * C k q
      else C p q := fun p q => transpose_planeRotation_mul_apply hjk C p q
  refine ⟨fun i l hik h => ?_, fun l h => ?_⟩
  · rw [happ] at h
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl] at h
      by_cases h1 : C i l = 0
      · rw [h1, mul_zero, zero_add] at h
        have := hrow l (right_ne_zero_of_mul h)
        exact Or.inl this
      · exact hrows i l hik h1
    · rw [ite_eq_right hij, ite_eq_right hik] at h
      exact hrows i l hik h
  · rw [happ, ite_eq_right hkj', ite_eq_left rfl] at h
    by_cases hl : l = j
    · subst hl
      exact absurd h2 h
    · have h0 : C k l = 0 := by
        by_contra h0
        exact hl (hrow l h0)
      rw [h0, mul_zero, add_zero] at h
      rcases hrows j l hjk (right_ne_zero_of_mul h) with h3 | h3
      · exact absurd h3 hl
      · exact h3

/-- The support of an upper bidiagonal matrix: `b_il ≠ 0` only for `l = i` or `l = i + 1`. -/
private theorem support_of_isUpperBidiagonal {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : C.IsUpperBidiagonal) (i l : Fin n) (h : C i l ≠ 0) : l = i ∨ (l : ℕ) = i + 1 := by
  by_contra hc
  push Not at hc
  refine h (hC i l ?_)
  rcases lt_or_ge (l : ℕ) i with hli | hli
  · exact Or.inl (Fin.lt_def.2 hli)
  · have : (i : ℕ) ≠ l := fun h' => hc.1 (Fin.ext h'.symm)
    exact Or.inr ⟨⟨i + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩

/-- A matrix supported on the diagonal and the first superdiagonal is upper bidiagonal. -/
private theorem isUpperBidiagonal_of_support {C : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i l, C i l ≠ 0 → l = i ∨ (l : ℕ) = i + 1) : C.IsUpperBidiagonal := fun i l hil => by
  by_contra h0
  rcases h i l h0 with h1 | h1
  · subst h1
    rcases hil with h2 | ⟨m, h2, h3⟩
    · exact lt_irrefl _ h2
    · exact lt_asymm h2 h3
  · rcases hil with h2 | ⟨m, h2, h3⟩
    · rw [Fin.lt_def] at h2; omega
    · rw [Fin.lt_def] at h2 h3; omega

/-- **§8.6.3, the decoupling rules.** For upper bidiagonal `B` (`n × n`) with diagonal `d` and
superdiagonal `f`: (i) if `f_k = 0`, then `B = diag(B₁, B₂)` (here of orders `a + 1`, `b + 1`) and
the singular values of `B` are those of `B₁` and `B₂` together (`BᵀB` has the characteristic
polynomial of `diag(B₁ᵀB₁, B₂ᵀB₂)`); (ii) if `d_k = 0`, the row rotations in the planes
`(k, k+1), …, (k, n)` (each by the Givens pair of the current `(j, j)` and `(k, j)` entries,
chasing the bulge one column right) give an orthogonal `G` with `GᵀB` upper bidiagonal and zero
`k`-th row; (iii) if `d_n = 0`, column rotations in the planes `(n-1, n), …, (1, n)` give an
orthogonal `G` with `B G` upper bidiagonal and zero last column. So the SVD problem decouples
whenever `f_1 ⋯ f_{n-1} = 0` or `d_1 ⋯ d_n = 0`. -/
theorem bidiagonal_decouple :
    (∀ {a b : ℕ} {B : Matrix (Fin (a + 1 + (b + 1))) (Fin (a + 1 + (b + 1))) ℝ},
      B.IsUpperBidiagonal → B (Fin.castAdd (b + 1) (Fin.last a)) (Fin.natAdd (a + 1) 0) = 0 →
        B.submatrix finSumFinEquiv finSumFinEquiv =
            fromBlocks (B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))) 0 0
              (B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))) ∧
          (Bᵀ * B).charpoly =
            ((B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1)))ᵀ *
                B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))).charpoly *
              ((B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1)))ᵀ *
                B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))).charpoly) ∧
    (∀ {B : Matrix (Fin n) (Fin n) ℝ}, B.IsUpperBidiagonal → ∀ k : Fin n, B k k = 0 →
      ∃ G ∈ orthogonalGroup (Fin n) ℝ, (Gᵀ * B).IsUpperBidiagonal ∧ ∀ l, (Gᵀ * B) k l = 0) ∧
    (∀ {B : Matrix (Fin n) (Fin n) ℝ}, B.IsUpperBidiagonal → ∀ h : 0 < n,
      B ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 0 →
      ∃ G ∈ orthogonalGroup (Fin n) ℝ, (B * G).IsUpperBidiagonal ∧
        ∀ i, (B * G) i ⟨n - 1, by omega⟩ = 0) := by
  -- (ii), the row chase
  have hrowChase : ∀ {B : Matrix (Fin n) (Fin n) ℝ}, B.IsUpperBidiagonal → ∀ k : Fin n,
      B k k = 0 → ∃ G ∈ orthogonalGroup (Fin n) ℝ, (Gᵀ * B).IsUpperBidiagonal ∧
        ∀ l, (Gᵀ * B) k l = 0 := by
    intro B hB k hk
    have hsupp := support_of_isUpperBidiagonal hB
    have key : ∀ t, (k : ℕ) + 1 + t ≤ n → ∃ G ∈ orthogonalGroup (Fin n) ℝ,
        (∀ i l, i ≠ k → (Gᵀ * B) i l ≠ 0 → l = i ∨ (l : ℕ) = i + 1) ∧
          ∀ l, (Gᵀ * B) k l ≠ 0 → (l : ℕ) = k + 1 + t := by
      intro t
      induction t with
      | zero =>
        intro _
        refine ⟨1, one_mem _, fun i l _ h => ?_, fun l h => ?_⟩
        · rw [transpose_one, Matrix.one_mul] at h
          exact hsupp i l h
        · rw [transpose_one, Matrix.one_mul] at h
          rcases hsupp k l h with h1 | h1
          · subst h1; exact absurd hk h
          · simpa using h1
      | succ t ih =>
        intro ht
        obtain ⟨G, hG, hrows, hrow⟩ := ih (by omega)
        set j : Fin n := ⟨k + 1 + t, by omega⟩
        have hkj : k < j := Fin.lt_def.2 (show (k : ℕ) < k + 1 + t by omega)
        have hrow' : ∀ l, (Gᵀ * B) k l ≠ 0 → l = j := fun l h => Fin.ext (hrow l h)
        obtain ⟨h1, h2⟩ := rowChase_step hkj hrows hrow'
        set R := planeRotation j k (givensPair ((Gᵀ * B) j j) ((Gᵀ * B) k j)).1
          (givensPair ((Gᵀ * B) j j) ((Gᵀ * B) k j)).2
        have hR : R ∈ orthogonalGroup (Fin n) ℝ :=
          planeRotation_mem_orthogonalGroup (ne_of_lt hkj).symm (givensPair_sq_add_sq _ _)
        have e : (G * R)ᵀ * B = Rᵀ * (Gᵀ * B) := by
          rw [transpose_mul, Matrix.mul_assoc]
        refine ⟨G * R, Submonoid.mul_mem _ hG hR, fun i l hik h => ?_, fun l h => ?_⟩
        · rw [e] at h; exact h1 i l hik h
        · rw [e] at h
          have := h2 l h
          simp only [j] at this
          omega
    obtain ⟨G, hG, hrows, hrow⟩ := key (n - (k + 1)) (by omega)
    have hzero : ∀ l, (Gᵀ * B) k l = 0 := fun l => by
      by_contra h
      have := hrow l h
      omega
    refine ⟨G, hG, isUpperBidiagonal_of_support fun i l h => ?_, hzero⟩
    by_cases hik : i = k
    · subst hik; exact absurd (hzero l) h
    · exact hrows i l hik h
  refine ⟨fun {a b B} hB hf => ?_, hrowChase, fun {B} hB h hd => ?_⟩
  · -- (i), the splitting
    have hsupp := support_of_isUpperBidiagonal hB
    have hblock : B.submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks (B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))) 0 0
          (B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))) := by
      ext (i | i) (j | j)
      · rfl
      · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          fromBlocks_apply₁₂, Matrix.zero_apply]
        by_contra h0
        rcases hsupp _ _ h0 with h1 | h1
        · have := congrArg Fin.val h1; simp at this; omega
        · simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
          have hi : i = Fin.last a := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
          have hj : j = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
          subst hi hj
          exact h0 hf
      · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          fromBlocks_apply₂₁, Matrix.zero_apply]
        by_contra h0
        rcases hsupp _ _ h0 with h1 | h1
        · have := congrArg Fin.val h1; simp at this; omega
        · simp only [Fin.val_natAdd, Fin.val_castAdd] at h1; omega
      · rfl
    refine ⟨hblock, ?_⟩
    have hgram : (Bᵀ * B).submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks ((B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1)))ᵀ *
            B.submatrix (Fin.castAdd (b + 1)) (Fin.castAdd (b + 1))) 0 0
          ((B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1)))ᵀ *
            B.submatrix (Fin.natAdd (a + 1)) (Fin.natAdd (a + 1))) := by
      rw [← submatrix_mul_equiv _ _ _ finSumFinEquiv, ← transpose_submatrix, hblock,
        fromBlocks_transpose, fromBlocks_multiply]
      simp
    rw [← charpoly_fromBlocks_zero₁₂, ← hgram]
    exact (charpoly_reindex finSumFinEquiv.symm (Bᵀ * B)).symm
  · -- (iii), the column chase: the row chase of the reversed transpose
    set B' : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i l => B (Fin.rev l) (Fin.rev i)
    have hsupp := support_of_isUpperBidiagonal hB
    have hB' : B'.IsUpperBidiagonal := isUpperBidiagonal_of_support fun i l h0 => by
      rcases hsupp _ _ h0 with h1 | h1
      · exact Or.inl (Fin.rev_injective h1.symm)
      · simp only [Fin.val_rev] at h1
        right; omega
    have hd' : B' ⟨0, h⟩ ⟨0, h⟩ = 0 := by
      have e : Fin.rev (⟨0, h⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext (by simp)
      simp only [B', of_apply, e]
      exact hd
    obtain ⟨G', hG', hbid, hrow⟩ := hrowChase hB' ⟨0, h⟩ hd'
    have hentry : ∀ i l, (B * G'.submatrix Fin.rev Fin.rev) i l =
        (G'ᵀ * B') (Fin.rev l) (Fin.rev i) := fun i l => by
      simp only [mul_apply, submatrix_apply, transpose_apply, B', of_apply, Fin.rev_rev]
      exact (Fintype.sum_equiv Fin.revPerm _ _ fun m => by simp [mul_comm]).symm
    have hsuppX := support_of_isUpperBidiagonal hbid
    refine ⟨G'.submatrix Fin.rev Fin.rev, ?_, isUpperBidiagonal_of_support fun i l h0 => ?_,
      fun i => ?_⟩
    · have hGG := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hG'
      refine (mem_orthogonalGroup_iff' (Fin n) ℝ).2 ?_
      have e : (G'.submatrix Fin.rev Fin.rev)ᵀ * G'.submatrix Fin.rev Fin.rev =
          (G'ᵀ * G').submatrix Fin.rev Fin.rev := by
        ext i j
        simp only [mul_apply, submatrix_apply, transpose_apply]
        exact Fintype.sum_equiv Fin.revPerm _ _ fun m => by simp
      rw [e, hGG]
      ext i j
      simp [one_apply]
    · rw [hentry] at h0
      rcases hsuppX _ _ h0 with h1 | h1
      · exact Or.inl (Fin.rev_injective h1).symm
      · simp only [Fin.val_rev] at h1
        right; omega
    · have e : Fin.rev (⟨n - 1, by omega⟩ : Fin n) = ⟨0, h⟩ := Fin.ext (by simp; omega)
      rw [hentry, e]
      exact hrow _

/-! ### §8.6.3 The SVD algorithm: Algorithms 8.6.1–8.6.2 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One chasing pair of Algorithm 8.6.1 on `(B, U, V, prev)` at consecutive window indices
`(a, b)`: `y, z` are `t₁₁ - μ`, `t₁₂` for the first pair (`prev = none`) and `b_{prev,a}`,
`b_{prev,b}` afterwards (the book's `y = b_{k,k+1}`, `z = b_{k,k+2}`, copies);
`[c, s] = givens(y, z)` (`[y z] [c s; -s c] = [* 0]`, the same condition `s y + c z = 0`),
`B = B G(a,b,θ)` over the window's rows, `V = V G(a,b,θ)`; then `y = b_aa`, `z = b_ba`,
`[c, s] = givens(y, z)`, `B = G(a,b,θ)ᵀ B` over the window's columns, `U = U G(a,b,θ)`. -/
noncomputable def golubKahanRotate (hnm : n ≤ m) (w : List (Fin n)) (y₀ z₀ : ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Option (Fin n)) (ab : Fin n × Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Option (Fin n)) := do
  let yz : ℝ × ℝ := st.2.2.2.elim (y₀, z₀) fun pr =>
    (st.1 (Fin.castLE hnm pr) ab.1, st.1 (Fin.castLE hnm pr) ab.2)
  let cs ← Chapter05.algorithm_5_1_3 rnd yz.1 yz.2
  let B₁ ← Chapter05.givensApplyRight rnd ab.1 ab.2 cs.1 cs.2 (w.map (Fin.castLE hnm)) st.1
  let V₁ ← Chapter05.givensApplyRight rnd ab.1 ab.2 cs.1 cs.2 (List.finRange n) st.2.2.1
  let cs' ← Chapter05.algorithm_5_1_3 rnd (B₁ (Fin.castLE hnm ab.1) ab.1)
    (B₁ (Fin.castLE hnm ab.2) ab.1)
  let B₂ ← Chapter05.givensApplyLeft rnd (Fin.castLE hnm ab.1) (Fin.castLE hnm ab.2) cs'.1 cs'.2
    w B₁
  let U₁ ← Chapter05.givensApplyRight rnd (Fin.castLE hnm ab.1) (Fin.castLE hnm ab.2) cs'.1
    cs'.2 (List.finRange m) st.2.1
  pure (B₂, U₁, V₁, some ab.1)

/-- **Algorithm 8.6.1 (Golub–Kahan SVD step).** "Given a bidiagonal matrix `B` having no zeros on
its diagonal or superdiagonal, the following algorithm overwrites `B` with the bidiagonal matrix
`B̄ = ŪᵀBV̄` where `Ū` and `V̄` are orthogonal and `V̄` is essentially the orthogonal matrix that
would be obtained by applying Algorithm 8.3.2 to `T = BᵀB`."
```
Let μ be the eigenvalue of the trailing 2-by-2 submatrix of T = BᵀB that is closer to t_nn.
y = t₁₁ - μ;  z = t₁₂
for k = 1:n-1
    Determine c, s such that [y z] [c s; -s c] = [* 0];   B = B G(k, k+1, θ)
    y = b_kk;  z = b_{k+1,k}
    Determine c, s such that [c s; -s c]ᵀ [y; z] = [*; 0]; B = G(k, k+1, θ)ᵀ B
    if k < n-1:  y = b_{k,k+1};  z = b_{k,k+2}
end
```
On a window `w` of consecutive column indices of an `m × n` array (`n ≤ m`; the rows of the window
are the same indices; the book's step is `w = List.finRange n`, the book's "`B ∈ ℝ^{m×n}`" being a
slip for a square `B`), with the accumulations `U = U Ū`, `V = V V̄` that Algorithm 8.6.2 needs.
`μ` is computed by the formula of Algorithm 8.3.2 from
`t_{N-1,N-1} = fl(fl(d²_{N-1}) + fl(f²_{N-2}))`
(no `f_{N-2}` for `N = 2`), `t_NN = fl(fl(d²_N) + fl(f²_{N-1}))`, `t_{N,N-1} = fl(d_{N-1} f_{N-1})`,
and `y = fl(fl(d₁²) - μ)`, `z = fl(d₁ f₁)`. For `N ≤ 1` nothing is done. -/
noncomputable def algorithm_8_6_1 (hnm : n ≤ m) (w : List (Fin n)) (B : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  match w with
  | f₀ :: f₁ :: rest => do
    let b : Fin n → Fin n → ℝ := fun i j => B (Fin.castLE hnm i) j
    let l := (f₁ :: rest).getLast (List.cons_ne_nil _ _)
    let l' := (f₀ :: f₁ :: rest).dropLast.getLast (by simp)
    let f₂ : ℝ := match rest with
      | [] => 0
      | _ => b ((f₀ :: f₁ :: rest).dropLast.dropLast.getLast?.getD l') l'
    let tpp ← rnd ((← rnd (b l' l' * b l' l')) + (← rnd (f₂ * f₂)))
    let tnn ← rnd ((← rnd (b l l * b l l)) + (← rnd (b l' l * b l' l)))
    let tnp ← rnd (b l' l' * b l' l)
    let μ ← wilkinsonShiftComputed rnd tpp tnn tnp
    let y₀ ← rnd ((← rnd (b f₀ f₀ * b f₀ f₀)) - μ)
    let z₀ ← rnd (b f₀ f₀ * b f₀ f₁)
    let st ← ((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
      (golubKahanRotate rnd hnm (f₀ :: f₁ :: rest) y₀ z₀) (B, U, V, none)
    pure (st.1, st.2.1, st.2.2.1)
  | _ => pure (B, U, V)

/-- The deflation pass of Algorithm 8.6.2: for `i = 1:n-1`, set `b_{i,i+1} = 0` if
`|b_{i,i+1}| ≤ fl(ε · fl(|b_ii| + |b_{i+1,i+1}|))` (the right side rounded; `|·|` and the
comparison exact). -/
noncomputable def svdDeflate (hnm : n ≤ m) (ε : ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) => do
    if h : (i : ℕ) + 1 < n then do
      let e ← rnd (ε * (← rnd (|B (Fin.castLE hnm i) i| +
        |B (Fin.castLE hnm ⟨i + 1, h⟩) ⟨i + 1, h⟩|)))
      if |B (Fin.castLE hnm i) ⟨i + 1, h⟩| ≤ e then
        pure (of fun r s => if r = Fin.castLE hnm i ∧ s = ⟨i + 1, h⟩ then 0 else B r s)
      else pure B
    else pure B) B

open Classical in
/-- The block `B₂₂` of Algorithm 8.6.2 as a window of consecutive indices: with the largest `q`
such that `B₃₃` (the last `q` columns) is diagonal and decoupled and the smallest `p` such that
`B₂₂` has a nonzero superdiagonal, the window `[p, …, n-q-1]`; empty when `q = n`. -/
noncomputable def bidiagonalWindow (hnm : n ≤ m) (B : Matrix (Fin m) (Fin n) ℝ) : List (Fin n) :=
  lastRunWindow n fun i => ∃ h : i + 1 < n,
    B (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0

/-- The decoupling rotations of Algorithm 8.6.2 on a window `w` of `B` with a zero diagonal entry
`b_kk` (`k` the first one), `bidiagonal_decouple` (ii)–(iii): if `k` is not the last index of the
window, rotations of the rows `(j, k)`, `j = k+1, …` (`[c, s] = givens(b_jj, b_kj)`,
`B = G(j,k,θ)ᵀ B`, `U = U G(j,k,θ)`) zero row `k`; if it is the last, rotations of the columns
`(j, k)`, `j = k-1, …, p` (`[c, s] = givens(b_jj, b_jk)`, `B = B G(j,k,θ)`, `V = V G(j,k,θ)`) zero
column `k`. -/
noncomputable def zeroDiagonalChase (hnm : n ≤ m) (w : List (Fin n)) (k : Fin n)
    (B : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  if w.getLast? = some k then
    ((w.filter (· < k)).reverse).foldlM (fun (st : Matrix (Fin m) (Fin n) ℝ ×
        Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ) j => do
      let cs ← Chapter05.algorithm_5_1_3 rnd (st.1 (Fin.castLE hnm j) j)
        (st.1 (Fin.castLE hnm j) k)
      let B₁ ← Chapter05.givensApplyRight rnd j k cs.1 cs.2 (w.map (Fin.castLE hnm)) st.1
      let V₁ ← Chapter05.givensApplyRight rnd j k cs.1 cs.2 (List.finRange n) st.2.2
      pure (B₁, st.2.1, V₁)) (B, U, V)
  else
    (w.filter (k < ·)).foldlM (fun (st : Matrix (Fin m) (Fin n) ℝ ×
        Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ) j => do
      let cs ← Chapter05.algorithm_5_1_3 rnd (st.1 (Fin.castLE hnm j) j)
        (st.1 (Fin.castLE hnm k) j)
      let B₁ ← Chapter05.givensApplyLeft rnd (Fin.castLE hnm j) (Fin.castLE hnm k) cs.1 cs.2 w
        st.1
      let U₁ ← Chapter05.givensApplyRight rnd (Fin.castLE hnm j) (Fin.castLE hnm k) cs.1 cs.2
        (List.finRange m) st.2.1
      pure (B₁, U₁, st.2.2)) (B, U, V)

open Classical in
/-- One pass of the `until q = n` loop of Algorithm 8.6.2 on `(B, U, V, done)`: deflate, find the
window of `B₂₂`, stop if it is empty (`q = n`); if `B₂₂` has a zero diagonal entry, decouple by
`zeroDiagonalChase`, otherwise apply Algorithm 8.6.1 to the window with the accumulators. -/
noncomputable def svdPass (hnm : n ≤ m) (ε : ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :=
  if st.2.2.2 then pure st else do
    let B ← svdDeflate rnd hnm ε st.1
    match bidiagonalWindow hnm B with
    | [] => pure (B, st.2.1, st.2.2.1, true)
    | w => do
      let r ← match w.find? fun k => B (Fin.castLE hnm k) k = 0 with
        | some k => zeroDiagonalChase rnd hnm w k B st.2.1 st.2.2.1
        | none => algorithm_8_6_1 rnd hnm w B st.2.1 st.2.2.1
      pure (r.1, r.2.1, r.2.2, false)

/-- **Algorithm 8.6.2 (the SVD algorithm).** "Given `A ∈ ℝ^{m×n}` (`m ≥ n`) and `ε`, a small
multiple of the unit roundoff, the following algorithm overwrites `A` with `UᵀAV = D + E`, where
`U`, `V` are orthogonal, `D` is diagonal, and `E` satisfies `‖E‖₂ ≈ u‖A‖₂`."
```
Use Algorithm 5.4.2 to compute the bidiagonalization [B; 0] = (U₁ ⋯ U_n)ᵀ A (V₁ ⋯ V_{n-2})
until q = n
    For i = 1:n-1, set b_{i,i+1} to zero if |b_{i,i+1}| ≤ ε(|b_ii| + |b_{i+1,i+1}|)
    Find the largest q and the smallest p such that B = diag(B₁₁, B₂₂, B₃₃) with B₃₃
    diagonal (q × q) and B₂₂ with a nonzero superdiagonal
    if q < n
        if any diagonal entry in B₂₂ is zero, then zero the superdiagonal entry in the same row
        else apply Algorithm 8.6.1 to B₂₂:
            B = diag(I_p, U, I_{q+m-n})ᵀ B diag(I_p, V, I_q)
    end
end
```
`B` is the bidiagonal part of chapter 5's Algorithm 5.4.2's array, `U` and `V` the forward
accumulations (§5.1.6) of its stored reflectors with the returned `β`s (convention 13); the loop is
at most `fuel` passes with a `done` flag (convention 3). The result is `(B, U, V, done)`. -/
noncomputable def algorithm_8_6_2 (hnm : n ≤ m) (ε : ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (fuel : ℕ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) := do
  let r ← Chapter05.algorithm_5_4_2 rnd hnm A
  let U ← Chapter05.forwardAccumulation rnd (Chapter05.storedReflectors r.1 r.2.1)
  let V ← Chapter05.forwardAccumulation rnd
    (List.ofFn fun k => (Chapter05.storedRowVec hnm r.1 k, r.2.2 k))
  (List.range fuel).foldlM (fun st _ => svdPass rnd hnm ε st)
    (Chapter05.bidiagonalPart r.1, U, V, false)

end Programs

end GolubVanLoan.Chapter08
