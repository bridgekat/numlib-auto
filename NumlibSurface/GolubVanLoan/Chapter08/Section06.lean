import Numlib.Analysis.InnerProductSpace.SingularValues
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.Jacobi
import Numlib.LinearAlgebra.Matrix.Bidiagonal
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.PlaneRotation
import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.GolubVanLoan.Chapter05.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section07
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
block first). Theorem 8.6.5 is the backbone's Wedin theorem
`Matrix.exists_singularSubspacePair_perturbation` in the coordinates `V = [V₁ V₂]`, `U = [U₁ U₂]`
(`Matrix.fromCols`) of the pair.

Algorithms 8.6.1–8.6.2 follow the conventions of `NumlibSurface/GolubVanLoan`: chapter 5's
`givens` and Givens updates on index lists, Algorithm 8.6.1 on a window of consecutive indices of
the `m × n` array with the accumulators `U`, `V`, Algorithm 8.6.2 on chapter 5's
bidiagonalization (Algorithm 5.4.2) with a `fuel`-bounded loop and a `done` flag. The exact
semantics of Algorithm 8.6.1 (square `B`, full window) is the chase of one bulge, alternately
below the diagonal and right of the superdiagonal, with the implicit-shift argument of
`algorithm_8_3_2_spec` for `BᵀB`. The exact semantics of Algorithm 8.6.2 is backward, as for
Algorithm 8.3.3: every step of Algorithm 8.6.1 and every zero-diagonal chase on the window of
`B₂₂` is a two-sided rotation of an array decoupled along the window, so it is the full rotation
and changes only the block; the deflations, carried back to `A`, form the backward error.

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

/-! ### §8.6.2 Theorem 8.6.5, and its failure for `m > n` as printed -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- A basis `W [1; P]` of `W` orthogonal spans an `r`-dimensional subspace. -/
private theorem finrank_range_mul_fromRows_one {l r s : ℕ}
    {W : Matrix (Fin l) (Fin r ⊕ Fin s) ℝ} (hW : Wᵀ * W = 1) (P : Matrix (Fin s) (Fin r) ℝ) :
    Module.finrank ℝ (LinearMap.range
      (toEuclideanLin (W * fromRows (1 : Matrix (Fin r) (Fin r) ℝ) P))) = r := by
  have hinj : Function.Injective
      (toEuclideanLin (W * fromRows (1 : Matrix (Fin r) (Fin r) ℝ) P)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : (fromRows (1 : Matrix (Fin r) (Fin r) ℝ) P) *ᵥ WithLp.ofLp y = 0 := by
      have := congrArg (fun v => Wᵀ *ᵥ WithLp.ofLp v) hy
      simp only [toEuclideanLin_apply, WithLp.ofLp_toLp, mulVec_mulVec, ← Matrix.mul_assoc,
        hW, Matrix.one_mul, WithLp.ofLp_zero, mulVec_zero] at this
      exact this
    ext i
    have := congrFun h1 (Sum.inl i)
    rw [fromRows_mulVec, Sum.elim_inl, one_mulVec] at this
    exact this
  rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_fin]

/-- **Theorem 8.6.5**, corrected for `m > n` (Wedin's condition): let `V = [V₁ V₂]` (`n × n`) and
`U = [U₁ U₂]` (`m × m`) be orthogonal, the first `r` columns splitting off `A₁₁`:
`Uᵀ A V = [A₁₁ 0; 0 A₂₂]`, so that `(ran V₁, ran U₁)` is a singular subspace pair for `A`; let the
singular values of `A₁₁` and of `A₂₂` be `δ`-separated (`δ ≤ |σ_i(A₁₁) - σ_j(A₂₂)|`, the book's
`δ = min |σ - γ| > 0`), and, if `m > n`, `δ ≤ σ_min(A₁₁)` (Wedin's condition, see
`theorem_8_6_5_counterexample`). If `‖E‖_F ≤ δ/5`, there are `P` (`(n - r) × r`) and
`Q` (`(m - r) × r`) with `‖[Q; P]‖_F ≤ 4 ‖E‖_F / δ` such that `ran(V₁ + V₂ P)` and
`ran(U₁ + U₂ Q)` form a singular subspace pair for `A + E`. The book's `P`, `Q` are swapped
(its `Q` is `(n - r) × r`); the backbone's `Matrix.exists_singularSubspacePair_perturbation`
(Stewart 1973, Wedin 1972). -/
theorem theorem_8_6_5 (hmn : n ≤ m) {r : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {V₁ : Matrix (Fin n) (Fin r) ℝ} {V₂ : Matrix (Fin n) (Fin (n - r)) ℝ}
    {U₁ : Matrix (Fin m) (Fin r) ℝ} {U₂ : Matrix (Fin m) (Fin (m - r)) ℝ}
    (hV : (fromCols V₁ V₂)ᵀ * fromCols V₁ V₂ = 1) (hV' : fromCols V₁ V₂ * (fromCols V₁ V₂)ᵀ = 1)
    (hU : (fromCols U₁ U₂)ᵀ * fromCols U₁ U₂ = 1) (hU' : fromCols U₁ U₂ * (fromCols U₁ U₂)ᵀ = 1)
    {A₁₁ : Matrix (Fin r) (Fin r) ℝ} {A₂₂ : Matrix (Fin (m - r)) (Fin (n - r)) ℝ}
    (hA : (fromCols U₁ U₂)ᵀ * A * fromCols V₁ V₂ = fromBlocks A₁₁ 0 0 A₂₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i < r, ∀ j < n - r,
      δ ≤ |A₁₁.sortedSingularValues i - A₂₂.sortedSingularValues j|)
    (hw : n < m → ∀ i < r, δ ≤ A₁₁.sortedSingularValues i) (hE : ‖E‖ ≤ δ / 5) :
    ∃ (P : Matrix (Fin (n - r)) (Fin r) ℝ) (Q : Matrix (Fin (m - r)) (Fin r) ℝ),
      ‖fromRows Q P‖ ≤ 4 * ‖E‖ / δ ∧
      IsSingularSubspacePair (A + E) (LinearMap.range (toEuclideanLin (V₁ + V₂ * P)))
        (LinearMap.range (toEuclideanLin (U₁ + U₂ * Q))) := by
  have hct : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ), Xᴴ = Xᵀ :=
    fun X => conjTranspose_eq_transpose_of_trivial X
  have hA' : (fromCols U₁ U₂)ᴴ * A * fromCols V₁ V₂ = fromBlocks A₁₁ 0 0 A₂₂ := by
    rw [conjTranspose_eq_transpose_of_trivial]; exact hA
  obtain ⟨P, Q, hPQ, ⟨M, hM⟩, ⟨N, hN⟩⟩ := exists_singularSubspacePair_perturbation (k := Fin r)
    (p := Fin (n - r)) (q := Fin (m - r)) (A := A) (E := E)
    (by rw [conjTranspose_eq_transpose_of_trivial]; exact hU)
    (by rw [conjTranspose_eq_transpose_of_trivial]; exact hU')
    (by rw [conjTranspose_eq_transpose_of_trivial]; exact hV)
    (by rw [conjTranspose_eq_transpose_of_trivial]; exact hV')
    (by rw [hA', toBlocks_fromBlocks₁₂]) (by rw [hA', toBlocks_fromBlocks₂₁]) hδ
    (fun i hi j hj => by
      rw [hA', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]
      simp only [Fintype.card_fin] at hi hj
      exact hsep i hi j (by omega))
    (fun hpq i hi => by
      rw [hA', toBlocks_fromBlocks₁₁]
      simp only [Fintype.card_fin] at hpq hi
      exact hw (by omega) i hi) hE
  have hVP : fromCols V₁ V₂ * fromRows 1 P = V₁ + V₂ * P := by
    rw [fromCols_mul_fromRows, Matrix.mul_one]
  have hUQ : fromCols U₁ U₂ * fromRows 1 Q = U₁ + U₂ * Q := by
    rw [fromCols_mul_fromRows, Matrix.mul_one]
  rw [hVP] at hM hN
  rw [hUQ] at hM hN
  rw [conjTranspose_eq_transpose_of_trivial] at hN
  refine ⟨P, Q, hPQ, ?_, ?_, ?_⟩
  · rw [← hVP, ← hUQ, finrank_range_mul_fromRows_one hV, finrank_range_mul_fromRows_one hU]
  · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨WithLp.toLp 2 (M *ᵥ WithLp.ofLp y), ?_⟩
    simp only [toEuclideanLin_apply, mulVec_mulVec, ← hM]
  · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨WithLp.toLp 2 (N *ᵥ WithLp.ofLp y), ?_⟩
    simp only [toEuclideanLin_apply, mulVec_mulVec, ← hN]


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

/-! ### Algorithm 8.6.1: exact semantics -/

section GolubKahan

/-- **The zero pattern of the Golub–Kahan chase before the step on the pair `(j, j + 1)`**: upper
bidiagonal except for the bulge `(j - 1, j + 1)` (none for `j = 0`). -/
private def IsRowBulge (j : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i l : Fin n, ((l : ℕ) < i ∨ (i : ℕ) + 1 < l) →
    ¬ (1 ≤ j ∧ (i : ℕ) + 1 = j ∧ (l : ℕ) = j + 1) → B i l = 0

/-- **The zero pattern after the column rotation of the step on `(j, j + 1)`**: upper bidiagonal
except for the bulge `(j + 1, j)`. -/
private def IsColBulge (j : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i l : Fin n, ((l : ℕ) < i ∨ (i : ℕ) + 1 < l) → ¬ ((i : ℕ) = j + 1 ∧ (l : ℕ) = j) →
    B i l = 0

/-- The column rotation of the step on `(j, j + 1)`, annihilating the bulge `(j - 1, j + 1)`,
moves it to `(j + 1, j)`. -/
private theorem isColBulge_mul {j : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsRowBulge j B)
    {a b : Fin n} (ha : (a : ℕ) = j) (hb : (b : ℕ) = j + 1) {c s : ℝ}
    (hz : ∀ pr : Fin n, 1 ≤ j → (pr : ℕ) + 1 = j → s * B pr a + c * B pr b = 0) :
    IsColBulge j (B * Chapter05.givensRotation a b c s) := by
  have hab : a ≠ b := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  intro i l hil hnb
  rw [Chapter05.givensRotation, mul_planeRotation_apply hab]
  by_cases hla : l = a
  · rw [ite_eq_left hla]
    subst hla
    have hi : (i : ℕ) + 2 ≤ j ∨ j + 2 ≤ (i : ℕ) := by omega
    rw [hB i l (by omega) (by omega), hB i b (by omega) (by omega)]
    ring
  rw [ite_eq_right hla]
  by_cases hlb : l = b
  · rw [ite_eq_left hlb]
    subst hlb
    by_cases hi1 : (i : ℕ) + 1 = j
    · linear_combination hz i (by omega) hi1
    · rw [hB i a (by omega) (by omega), hB i l (by omega) (by omega)]
      ring
  rw [ite_eq_right hlb]
  exact hB i l hil (fun h => hlb (Fin.ext (by omega)))

/-- The row rotation of the step on `(j, j + 1)`, annihilating the bulge `(j + 1, j)`, moves it
to `(j, j + 2)`. -/
private theorem isRowBulge_mul {j : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsColBulge j B)
    {a b : Fin n} (ha : (a : ℕ) = j) (hb : (b : ℕ) = j + 1) {c s : ℝ}
    (hz : s * B a a + c * B b a = 0) :
    IsRowBulge (j + 1) ((Chapter05.givensRotation a b c s)ᵀ * B) := by
  have hab : a ≠ b := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  intro i l hil hnb
  rw [Chapter05.givensRotation, transpose_planeRotation_mul_apply hab]
  by_cases hia : i = a
  · rw [ite_eq_left hia]
    subst hia
    rw [hB i l (by omega) (by omega), hB b l (by omega) (by omega)]
    ring
  rw [ite_eq_right hia]
  by_cases hib : i = b
  · rw [ite_eq_left hib]
    subst hib
    by_cases hla : l = a
    · subst hla
      linear_combination hz
    · have hla' : (l : ℕ) ≠ j := fun h => hla (Fin.ext (by omega))
      rw [hB a l (by omega) (by omega), hB i l (by omega) (by omega)]
      ring
  rw [ite_eq_right hib]
  exact hB i l hil (fun h => hib (Fin.ext (by omega)))

/-- **One chasing pair of Algorithm 8.6.1 on the full square array, exactly**: with
`(c, s) = givens(y, z)` for `(y, z)` the first pair `(y₀, z₀)` or the entries
`(b_{prev,a}, b_{prev,b})`, and `(c', s') = givens` of the new `(b_aa, b_ba)`, the new state is
`(G'ᵀ B G, U G', V G, a)`. -/
private theorem golubKahanRotate_pure {a b : Fin n} (hab : a ≠ b) (y₀ z₀ : ℝ)
    (B U V : Matrix (Fin n) (Fin n) ℝ) (prev : Option (Fin n)) :
    let yz : ℝ × ℝ := prev.elim (y₀, z₀) fun pr => (B pr a, B pr b)
    let cs := Id.run (Chapter05.algorithm_5_1_3 pure yz.1 yz.2)
    let B₁ := B * Chapter05.givensRotation a b cs.1 cs.2
    let cs' := Id.run (Chapter05.algorithm_5_1_3 pure (B₁ a a) (B₁ b a))
    Id.run (golubKahanRotate pure le_rfl (List.finRange n) y₀ z₀ (B, U, V, prev) (a, b)) =
      ((Chapter05.givensRotation a b cs'.1 cs'.2)ᵀ * B₁,
        U * Chapter05.givensRotation a b cs'.1 cs'.2,
        V * Chapter05.givensRotation a b cs.1 cs.2, some a) := by
  intro yz cs B₁ cs'
  have hrows : ((List.finRange n).map (Fin.castLE (le_refl n))).Nodup :=
    (List.nodup_finRange n).map (Fin.castLE_injective _)
  have hall : ∀ r : Fin n, r ∈ (List.finRange n).map (Fin.castLE (le_refl n)) := fun r =>
    List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩
  simp only [golubKahanRotate, Id.run_bind, Id.run_pure, Fin.castLE_refl]
  rw [Chapter05.givensApplyRight_spec_of_forall_mem hab _ _ hrows hall,
    Chapter05.givensApplyLeft_spec_of_forall_mem hab _ _ (List.nodup_finRange n)
      List.mem_finRange,
    Chapter05.givensApplyRight_spec_of_forall_mem hab _ _ (List.nodup_finRange n)
      List.mem_finRange,
    Chapter05.givensApplyRight_spec_of_forall_mem hab _ _ (List.nodup_finRange n)
      List.mem_finRange]

/-- The loop invariant of Algorithm 8.6.1 on the full square array after `j` chasing pairs: the
state `(B', U', V', prev)` is `(Ūᵀ B V̄, U Ū, V V̄, j - 1)` for orthogonal `Ū`, `V̄`, `B'` has the
zero pattern of the chase, and for `j ≥ 1` the first column of `V̄` is that of the first
rotation `G(0, 1, θ₀)`, `(c₀, s₀) = givens(y₀, z₀)`. -/
private def GolubKahanInv (B U V : Matrix (Fin n) (Fin n) ℝ) (y₀ z₀ : ℝ) (f₀ f₁ : Fin n) (j : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Option (Fin n)) : Prop :=
  ∃ Ub Vb : Matrix (Fin n) (Fin n) ℝ, Ub ∈ orthogonalGroup (Fin n) ℝ ∧
    Vb ∈ orthogonalGroup (Fin n) ℝ ∧ st.1 = Ubᵀ * B * Vb ∧ st.2.1 = U * Ub ∧
    st.2.2.1 = V * Vb ∧ IsRowBulge j st.1 ∧
    st.2.2.2.elim (j = 0) (fun pr => 1 ≤ j ∧ (pr : ℕ) + 1 = j) ∧ (j = 0 → Vb = 1) ∧
    (1 ≤ j → ∃ c₀ s₀ : ℝ, c₀ ^ 2 + s₀ ^ 2 = 1 ∧ s₀ * y₀ + c₀ * z₀ = 0 ∧
      Vb *ᵥ Pi.single f₀ 1 = Chapter05.givensRotation f₀ f₁ c₀ s₀ *ᵥ Pi.single f₀ 1)

/-- **The bulge chase of Algorithm 8.6.1**, the loop: the invariant holds after the `n - 1`
chasing pairs. -/
private theorem golubKahanInv_run {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsUpperBidiagonal)
    (U V : Matrix (Fin n) (Fin n) ℝ) (y₀ z₀ : ℝ) (f₀ f₁ : Fin n) (hf₀ : (f₀ : ℕ) = 0)
    (hf₁ : (f₁ : ℕ) = 1) :
    GolubKahanInv B U V y₀ z₀ f₀ f₁ (n - 1)
      (Id.run (((List.finRange n).zip (List.finRange n).tail).foldlM
        (golubKahanRotate pure le_rfl (List.finRange n) y₀ z₀) (B, U, V, none))) := by
  have hzlen : ((List.finRange n).zip (List.finRange n).tail).length = n - 1 := by simp
  rw [← hzlen]
  refine idRun_foldlM_induction _ _ _ ⟨1, 1, one_mem _, one_mem _, by simp, (Matrix.mul_one U).symm,
    (Matrix.mul_one V).symm, fun i l hil _ => hB i l ?_, rfl, fun _ => rfl,
    fun h => absurd h (by omega)⟩ ?_
  · rcases hil with hil | hil
    · exact Or.inl (Fin.lt_def.2 hil)
    · exact Or.inr ⟨⟨(i : ℕ) + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩
  intro j hj ⟨X, Ua, Va, prev⟩ ⟨Ub, Vb, hUo, hVo, hX, hUa, hVa, hXc, hprev, hV1, hcol⟩
  simp only at hX hUa hVa hXc hprev
  rw [hzlen] at hj
  have hpair : ((List.finRange n).zip (List.finRange n).tail)[j]'(by rw [hzlen]; exact hj) =
      (⟨j, by omega⟩, ⟨j + 1, by omega⟩) := by
    simp [List.getElem_zip, List.getElem_tail]
  rw [hpair]
  set a : Fin n := ⟨j, by omega⟩ with hadef
  set b : Fin n := ⟨j + 1, by omega⟩ with hbdef
  have ha : (a : ℕ) = j := rfl
  have hb : (b : ℕ) = j + 1 := rfl
  have hab : a ≠ b := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  rw [golubKahanRotate_pure hab]
  set yz : ℝ × ℝ := prev.elim (y₀, z₀) fun pr => (X pr a, X pr b) with hyz
  obtain ⟨hcs, hzcs, -⟩ := Chapter05.algorithm_5_1_3_spec yz.1 yz.2
  set cs := Id.run (Chapter05.algorithm_5_1_3 pure yz.1 yz.2)
  set G := Chapter05.givensRotation a b cs.1 cs.2 with hG
  obtain ⟨hcs', hzcs', -⟩ := Chapter05.algorithm_5_1_3_spec ((X * G) a a) ((X * G) b a)
  set cs' := Id.run (Chapter05.algorithm_5_1_3 pure ((X * G) a a) ((X * G) b a))
  set G' := Chapter05.givensRotation a b cs'.1 cs'.2 with hG'
  have hGo : G ∈ orthogonalGroup (Fin n) ℝ := Chapter05.givensRotation_mem_orthogonalGroup hab hcs
  have hG'o : G' ∈ orthogonalGroup (Fin n) ℝ :=
    Chapter05.givensRotation_mem_orthogonalGroup hab hcs'
  have hXG : IsColBulge j (X * G) := isColBulge_mul hXc ha hb fun pr hj1 hpr => by
    cases prev with
    | none => exact absurd (hprev : j = 0) (Nat.one_le_iff_ne_zero.1 hj1)
    | some pr' =>
      have h2 : (pr' : ℕ) + 1 = j := hprev.2
      have hpr' : pr' = pr := Fin.ext (Nat.add_right_cancel (h2.trans hpr.symm))
      subst hpr'
      exact hzcs
  refine ⟨Ub * G', Vb * G, Submonoid.mul_mem _ hUo hG'o, Submonoid.mul_mem _ hVo hGo, ?_, ?_, ?_,
    isRowBulge_mul hXG ha hb hzcs', ⟨Nat.succ_pos _, by simp [ha]⟩,
    fun h => absurd h (Nat.succ_ne_zero _), fun _ => ?_⟩
  · simp only
    rw [hX, transpose_mul]
    simp only [Matrix.mul_assoc]
  · simp only
    rw [hUa, Matrix.mul_assoc]
  · simp only
    rw [hVa, Matrix.mul_assoc]
  · rcases Nat.eq_zero_or_pos j with rfl | hj1
    · cases prev with
      | some pr => exact absurd hprev.1 (by omega)
      | none =>
        have ha' : a = f₀ := Fin.ext (by rw [ha, hf₀])
        have hb' : b = f₁ := Fin.ext (by rw [hb, hf₁])
        refine ⟨cs.1, cs.2, hcs, hzcs, ?_⟩
        rw [hV1 rfl, Matrix.one_mul, hG, ha', hb']
    · obtain ⟨c₀, s₀, h₀, hz₀, he₀⟩ := hcol hj1
      refine ⟨c₀, s₀, h₀, hz₀, ?_⟩
      rw [← mulVec_mulVec, givensRotation_mulVec_single_of_ne hab
        (fun e => by rw [e, ha] at hf₀; omega) (fun e => by rw [e, hb] at hf₀; omega), he₀]

/-- A matrix with the zero pattern of the chase after the last pair is upper bidiagonal. -/
private theorem isUpperBidiagonal_of_isRowBulge {B : Matrix (Fin n) (Fin n) ℝ}
    (h : IsRowBulge (n - 1) B) : B.IsUpperBidiagonal := by
  rintro i l (hil | ⟨k, h1, h2⟩)
  · rw [Fin.lt_def] at hil
    exact h i l (Or.inl hil) (by omega)
  · rw [Fin.lt_def] at h1 h2
    exact h i l (Or.inr (by omega)) (by omega)

/-- The exact Wilkinson shift that Algorithm 8.6.1 computes from the entries of an upper
bidiagonal `B` is the Wilkinson shift (8.3.3) of `T = BᵀB`. -/
private theorem algorithm_8_6_1_shift {N : ℕ} {B : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hB : B.IsUpperBidiagonal) (f₂ : ℝ)
    (hf₂ : f₂ = if h : N = 0 then 0 else B ⟨N - 1, by omega⟩ (Fin.last N).castSucc) :
    Id.run (wilkinsonShiftComputed pure
      (B (Fin.last N).castSucc (Fin.last N).castSucc * B (Fin.last N).castSucc (Fin.last N).castSucc
        + f₂ * f₂)
      (B (Fin.last (N + 1)) (Fin.last (N + 1)) * B (Fin.last (N + 1)) (Fin.last (N + 1)) +
        B (Fin.last N).castSucc (Fin.last (N + 1)) * B (Fin.last N).castSucc (Fin.last (N + 1)))
      (B (Fin.last N).castSucc (Fin.last N).castSucc * B (Fin.last N).castSucc (Fin.last (N + 1))))
      = wilkinsonShift (Bᵀ * B) := by
  obtain ⟨hTs, -, hdiag, hsup, -⟩ := gram_bidiagonal hB
  set l := Fin.last (N + 1)
  set l' := (Fin.last N).castSucc
  have hl : (l : ℕ) = N + 1 := rfl
  have hl' : (l' : ℕ) = N := by simp [l']
  -- the trailing entries of `T = BᵀB`
  have ha : (Bᵀ * B) l l = B l l * B l l + B l' l * B l' l := by
    rw [hdiag, Finset.sum_eq_single l', ite_eq_left (by rw [hl, hl'])]
    · ring
    · intro j _ hj
      exact ite_eq_right (fun h => hj (Fin.ext (by rw [hl'] ; rw [hl] at h; omega)))
    · simp
  have ha' : (Bᵀ * B) l' l' = B l' l' * B l' l' + f₂ * f₂ := by
    rw [hdiag, hf₂]
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · rw [Finset.sum_eq_zero fun j _ => ite_eq_right (by rw [hl']; omega)]
      simp only [dite_eq_left h0, mul_zero, add_zero]
      ring
    · rw [dite_eq_right (by omega : ¬ N = 0), Finset.sum_eq_single ⟨N - 1, by omega⟩,
        ite_eq_left (by simp only; rw [hl']; omega)]
      · ring
      · intro j _ hj
        exact ite_eq_right fun h => hj (Fin.ext (by rw [hl'] at h; simp only; omega))
      · simp
  have hb : (Bᵀ * B) l l' = B l' l' * B l' l := by
    rw [hTs.apply l' l, hsup l' l (by rw [hl, hl'])]
  rw [wilkinsonShiftComputed_pure, (equation_8_3_3 (Bᵀ * B)).2.2]
  simp only [← ha, ← ha', ← hb]
  rfl

/-- **Exact semantics of Algorithm 8.6.1** (the Golub–Kahan SVD step: "Given a bidiagonal matrix
`B` having no zeros on its diagonal or superdiagonal, the following algorithm overwrites `B` with
the bidiagonal matrix `B̄ = ŪᵀBV̄` where `Ū` and `V̄` are orthogonal and `V̄` is essentially the
orthogonal matrix that would be obtained by applying Algorithm 8.3.2 to `T = BᵀB`"), for square
`B` of order `n = N + 2` on the full window: the exact run `(B̄, U', V')` has orthogonal `Ū`,
`V̄` (the products of the `n - 1` row and column rotations) with `B̄ = Ūᵀ B V̄` upper bidiagonal,
`U' = U Ū`, `V' = V V̄`, `B̄ᵀ B̄ = V̄ᵀ T V̄`, `V̄ e₁` parallel to `(T - μ I) e₁` for the Wilkinson
shift `μ` of `T` and `V̄ᵀ (T - μ I)` upper triangular; so when `T - μ I` is nonsingular,
`B̄ᵀ B̄ = D (Matrix.shiftedQrStep μ T) D` for a `±1` diagonal `D` — the same step as Algorithm
8.3.2 on `T` (`algorithm_8_3_2_spec`), up to signs. The proof is the chase of one bulge,
alternately below the diagonal and right of the superdiagonal. -/
theorem algorithm_8_6_1_spec {N : ℕ} {B : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hB : B.IsUpperBidiagonal) (hd : ∀ i, B i i ≠ 0)
    (hf : ∀ i j : Fin (N + 2), (j : ℕ) = i + 1 → B i j ≠ 0)
    (U V : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) :
    let out := Id.run (algorithm_8_6_1 pure le_rfl (List.finRange (N + 2)) B U V)
    ∃ Ub ∈ orthogonalGroup (Fin (N + 2)) ℝ, ∃ Vb ∈ orthogonalGroup (Fin (N + 2)) ℝ,
      out.1 = Ubᵀ * B * Vb ∧ out.2.1 = U * Ub ∧ out.2.2 = V * Vb ∧ out.1.IsUpperBidiagonal ∧
      out.1ᵀ * out.1 = Vbᵀ * (Bᵀ * B) * Vb ∧
      Vb.col 0 ∈ Submodule.span ℝ {(Bᵀ * B - wilkinsonShift (Bᵀ * B) • 1).col 0} ∧
      (Vbᵀ * (Bᵀ * B - wilkinsonShift (Bᵀ * B) • 1)).IsUpperTriangular ∧
      (IsUnit (Bᵀ * B - wilkinsonShift (Bᵀ * B) • 1).det →
        ∃ d : Fin (N + 2) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧
          out.1ᵀ * out.1 = diagonal d * shiftedQrStep (wilkinsonShift (Bᵀ * B)) (Bᵀ * B) *
            diagonal d) := by
  intro out
  set T := Bᵀ * B with hT
  set μ := wilkinsonShift T with hμ
  obtain ⟨hTs, hTt, hdiag, hsup, hunred⟩ := gram_bidiagonal hB
  have hTu : IsUnreducedTridiagonal T := hunred.2 fun i j hj => mul_ne_zero (hd i) (hf i j hj)
  -- the window and its trailing pair
  have hval : ∀ k (hk : k < (List.finRange (N + 2)).length),
      ((List.finRange (N + 2))[k] : ℕ) = k := fun k hk => by simp
  have hlen : (List.finRange (N + 2)).length = N + 2 := by simp
  obtain ⟨f₀, f₁, rest, hw⟩ := exists_cons_cons (List.finRange (N + 2)) (by simp)
  have hlen' : (f₀ :: f₁ :: rest).length = N + 2 := hw ▸ hlen
  have hval' : ∀ k (hk : k < (f₀ :: f₁ :: rest).length), ((f₀ :: f₁ :: rest)[k] : ℕ) = k :=
    fun k hk => by rw [← List.getElem_of_eq hw]; exact hval k (by omega)
  have hf₀ : f₀ = 0 := Fin.ext (by have := hval' 0 (by simp); simpa using this)
  have hf₁ : f₁ = 1 := Fin.ext (by have := hval' 1 (by simp); simpa using this)
  have hl : (f₁ :: rest).getLast (List.cons_ne_nil _ _) = Fin.last (N + 1) := by
    refine Fin.ext ?_
    rw [← List.getLast_cons (List.cons_ne_nil f₁ rest) (a := f₀), List.getLast_eq_getElem,
      hval' _ (by omega), hlen']
    simp
  have hl' : (f₀ :: f₁ :: rest).dropLast.getLast (by simp) = (Fin.last N).castSucc := by
    refine Fin.ext ?_
    rw [List.getLast_eq_getElem, List.getElem_dropLast, hval' _ (by simp)]
    simp only [List.length_dropLast, hlen']
    simp
  -- the program is the fold of `golubKahanRotate` over the consecutive pairs
  have key := golubKahanInv_run hB U V (B 0 0 * B 0 0 - μ) (B 0 0 * B 0 1) 0 1 rfl rfl
  set st := Id.run (((List.finRange (N + 2)).zip (List.finRange (N + 2)).tail).foldlM
    (golubKahanRotate pure le_rfl (List.finRange (N + 2)) (B 0 0 * B 0 0 - μ) (B 0 0 * B 0 1))
    (B, U, V, none)) with hst
  have hout : out = (st.1, st.2.1, st.2.2.1) := by
    change Id.run (algorithm_8_6_1 pure le_rfl (List.finRange (N + 2)) B U V) = _
    rw [hst, hw, List.tail_cons]
    simp only [algorithm_8_6_1, pure_bind, Id.run_bind, Fin.castLE_refl]
    rw [hl, hl']
    have hrl : rest.length = N := by simp at hlen'; omega
    split
    · have hN : N = 0 := by simp at hlen'; omega
      rw [algorithm_8_6_1_shift hB 0 (by rw [dite_eq_left hN])]
      subst hf₀ hf₁
      rfl
    · rename_i hr
      have hN : N ≠ 0 := fun h0 => hr (List.eq_nil_of_length_eq_zero (by omega))
      have hf₂ : B ((f₀ :: f₁ :: rest).dropLast.dropLast.getLast?.getD (Fin.last N).castSucc)
          (Fin.last N).castSucc = B ⟨N - 1, by omega⟩ (Fin.last N).castSucc := by
        congr 1
        have hne : (f₀ :: f₁ :: rest).dropLast.dropLast ≠ [] := by
          rcases rest with _ | ⟨r, rest'⟩
          · exact absurd rfl hr
          · simp
        rw [List.getLast?_eq_some_getLast hne, Option.getD_some]
        refine Fin.ext ?_
        rw [List.getLast_eq_getElem, List.getElem_dropLast, List.getElem_dropLast,
          hval' _ (by simp; omega)]
        simp
        omega
      rw [algorithm_8_6_1_shift hB _ (by rw [dite_eq_right hN]; exact hf₂)]
      subst hf₀ hf₁
      rfl
  -- the invariant after the last pair
  obtain ⟨Ub, Vb, hUo, hVo, h1, h2, h3, hXc, -, -, hcol⟩ := key
  rw [hout]
  have hUU : Ub * Ubᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hUo
  have hVV : Vb * Vbᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hVo
  have hVV' : Vbᵀ * Vb = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hVo
  have hbid : st.1.IsUpperBidiagonal := isUpperBidiagonal_of_isRowBulge hXc
  have hgram : st.1ᵀ * st.1 = Vbᵀ * T * Vb := by
    rw [h1, hT, transpose_mul, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ub Ubᵀ, hUU, Matrix.one_mul]
  have htri : (Vbᵀ * T * Vb).IsTridiagonal := hgram ▸ (gram_bidiagonal hbid).2.1
  -- the first column of `V̄`
  obtain ⟨c₀, s₀, hcs, hz, he⟩ := hcol (by omega)
  rw [show ((0 : Fin (N + 2)) : Fin (N + 2)) = 0 from rfl,
    givensRotation_mulVec_single_zero] at he
  have hT00 : T 0 0 = B 0 0 * B 0 0 := by
    rw [hT, hdiag, Finset.sum_eq_zero fun j _ => ite_eq_right (by simp)]
    ring
  have hT10 : T 1 0 = B 0 0 * B 0 1 := by
    rw [hT, ← hTs.apply 1 0, hsup 0 1 (by simp)]
  rw [← hT00, ← hT10] at hz
  have hsub : T 1 0 ≠ 0 := by
    have := hTu.2.apply_succ_castSucc_ne_zero (0 : Fin (N + 1))
    simpa using this
  have hT0 : (T - μ • 1).col 0 = (T 0 0 - μ) • Pi.single 0 1 + T 1 0 • Pi.single 1 1 := by
    funext t
    rw [col_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply]
    by_cases h0 : t = 0
    · subst h0; simp
    · by_cases h1 : t = 1
      · subst h1; simp
      · have ht : T t 0 = 0 := hTu.1 t 0 (Or.inl ⟨1, by simp, by
          rw [Fin.lt_def]; have : (t : ℕ) ≠ 0 := fun e => h0 (Fin.ext e)
          have : (t : ℕ) ≠ 1 := fun e => h1 (Fin.ext e)
          simp; omega⟩)
        simp [h0, h1, ht]
  set r := c₀ * (T 0 0 - μ) - s₀ * T 1 0 with hr
  have hTr : (T - μ • 1).col 0 = r • Vb.col 0 := by
    have ex : T 0 0 - μ = r * c₀ := by
      rw [hr]; linear_combination (-(T 0 0 - μ)) * hcs + s₀ * hz
    have ez : T 1 0 = -(r * s₀) := by
      rw [hr]; linear_combination (-(T 1 0)) * hcs + c₀ * hz
    rw [← mulVec_single_one Vb 0, he, hT0, ex, ez]
    module
  have hr0 : r ≠ 0 := by
    intro h0
    have := congrFun hTr 1
    rw [h0, zero_smul, Pi.zero_apply, col_apply, Matrix.sub_apply, Matrix.smul_apply,
      one_apply_ne (by simp), smul_zero, sub_zero] at this
    exact hsub this
  have hcol' : Vb.col 0 ∈ Submodule.span ℝ {(T - μ • 1).col 0} := by
    have : Vb.col 0 = r⁻¹ • (T - μ • 1).col 0 := by
      rw [hTr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hstar : star Vb = Vbᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have haeval : Polynomial.aeval T (Polynomial.X - Polynomial.C μ) = T - μ • 1 := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hUT : (Vbᵀ * (T - μ • 1)).IsUpperTriangular := by
    have := IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval hTu.2
      (Polynomial.X - Polynomial.C μ) hVo (by rw [hstar]; exact htri.isUpperHessenberg)
      (by rw [haeval, mulVec_single_one]; exact hcol')
    rwa [haeval, hstar] at this
  refine ⟨Ub, hUo, Vb, hVo, h1, h2, h3, hbid, hgram, hcol', hUT, fun hdet => ?_⟩
  have hstep : IsShiftedQrStep μ T (st.1ᵀ * st.1) := by
    refine ⟨Vb, hVo, Vbᵀ * (T - μ • 1), hUT, ?_, ?_⟩
    · rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
    · rw [hgram, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        hVV', sub_add_cancel]
  obtain ⟨d, hd, hdd⟩ := (isShiftedQrStep_shiftedQrStep μ T).unique_of_isUnit hstep hdet
  refine ⟨d, fun i => ?_, ?_⟩
  · have := hd i
    rw [Real.norm_eq_abs] at this
    exact (abs_eq zero_le_one).1 this
  · rw [hdd, star_eq_conjTranspose, diagonal_conjTranspose, star_trivial]

end GolubKahan

/-! ### Algorithm 8.6.2: exact semantics -/

section SVDAlgorithm

open Chapter07 (francisWindow)

/-! #### Rotations of an `m × n` array, and windows -/

/-- The length of the window `[p, q)`. -/
private theorem length_francisWindow' {p q : ℕ} (hq : q ≤ n) :
    (francisWindow n p q).length = q - p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Chapter07.francisWindow]
    omega
  · have : NeZero n := ⟨hn.ne'⟩
    rw [Chapter07.francisWindow_eq_map hq, List.length_map, List.length_range]

/-- The `k`-th index of the window `[p, q)` is `p + k`. -/
private theorem val_getElem_francisWindow' {p q : ℕ} (hq : q ≤ n) (k : ℕ)
    (hk : k < (francisWindow n p q).length) : ((francisWindow n p q)[k] : ℕ) = p + k := by
  have hk' := hk
  rw [length_francisWindow' hq] at hk'
  have : NeZero n := ⟨by omega⟩
  rw [List.getElem_of_eq (Chapter07.francisWindow_eq_map hq) hk]
  simp only [List.getElem_map, List.getElem_range, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- The rows `w.map (Fin.castLE hnm)` of the window `w = [p, q)`. -/
private theorem mem_map_castLE_francisWindow (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n) (r : Fin m) :
    r ∈ (francisWindow n p q).map (Fin.castLE hnm) ↔ p ≤ (r : ℕ) ∧ (r : ℕ) < q := by
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa using Chapter07.mem_francisWindow.1 hi
  · rintro ⟨h1, h2⟩
    exact ⟨⟨r, by omega⟩, Chapter07.mem_francisWindow.2 ⟨h1, h2⟩, Fin.ext rfl⟩

/-- `X` agrees with `B` off the block `[p, q) × [p, q)` (rows and columns by value). -/
private def AgreeOff (p q : ℕ) (X B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (r : Fin m) (s : Fin n), ¬ ((p ≤ (r : ℕ) ∧ (r : ℕ) < q) ∧ (p ≤ (s : ℕ) ∧ (s : ℕ) < q)) →
    X r s = B r s

/-- `B` is decoupled along the window `[p, q)`: its entries in a row of the window and a column
off it, or the other way round, vanish. -/
private def IsDecoupledAt (p q : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (r : Fin m) (s : Fin n), ((p ≤ (r : ℕ) ∧ (r : ℕ) < q) ∧ ¬ (p ≤ (s : ℕ) ∧ (s : ℕ) < q)) ∨
    (¬ (p ≤ (r : ℕ) ∧ (r : ℕ) < q) ∧ (p ≤ (s : ℕ) ∧ (s : ℕ) < q)) → B r s = 0

private theorem AgreeOff.trans {p q : ℕ} {X Y B : Matrix (Fin m) (Fin n) ℝ}
    (h₁ : AgreeOff p q X Y) (h₂ : AgreeOff p q Y B) : AgreeOff p q X B :=
  fun r s h => (h₁ r s h).trans (h₂ r s h)

private theorem IsDecoupledAt.of_agreeOff {p q : ℕ} {X B : Matrix (Fin m) (Fin n) ℝ}
    (hB : IsDecoupledAt p q B) (h : AgreeOff p q X B) : IsDecoupledAt p q X :=
  fun r s hrs => (h r s (by tauto)).trans (hB r s hrs)

/-- A column rotation in two window columns of a decoupled array changes only the block. -/
private theorem agreeOff_mul_givensRotation {p q : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    (hX : IsDecoupledAt p q X) {a b : Fin n} (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q)
    (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b) (c s : ℝ) :
    AgreeOff p q (X * Chapter05.givensRotation a b c s) X := by
  intro r t hrt
  rw [Chapter07.mul_givensRotation_apply hab]
  by_cases hta : t = a
  · subst hta
    have hr : ¬ (p ≤ (r : ℕ) ∧ (r : ℕ) < q) := fun hr => hrt ⟨hr, ha⟩
    rw [ite_eq_left rfl, hX r t (Or.inr ⟨hr, ha⟩), hX r b (Or.inr ⟨hr, hb⟩)]
    ring
  · by_cases htb : t = b
    · subst htb
      have hr : ¬ (p ≤ (r : ℕ) ∧ (r : ℕ) < q) := fun hr => hrt ⟨hr, hb⟩
      rw [ite_eq_right hta, ite_eq_left rfl, hX r a (Or.inr ⟨hr, ha⟩), hX r t (Or.inr ⟨hr, hb⟩)]
      ring
    · rw [ite_eq_right hta, ite_eq_right htb]

/-- A row rotation in two window rows of a decoupled array changes only the block. -/
private theorem agreeOff_givensRotation_transpose_mul {p q : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    (hX : IsDecoupledAt p q X) {a b : Fin m} (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q)
    (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b) (c s : ℝ) :
    AgreeOff p q ((Chapter05.givensRotation a b c s)ᵀ * X) X := by
  intro r t hrt
  rw [Chapter05.givensRotation_transpose_mul_apply hab]
  by_cases hra : r = a
  · subst hra
    have ht : ¬ (p ≤ (t : ℕ) ∧ (t : ℕ) < q) := fun ht => hrt ⟨ha, ht⟩
    rw [ite_eq_left rfl, hX r t (Or.inl ⟨ha, ht⟩), hX b t (Or.inl ⟨hb, ht⟩)]
    ring
  · by_cases hrb : r = b
    · subst hrb
      have ht : ¬ (p ≤ (t : ℕ) ∧ (t : ℕ) < q) := fun ht => hrt ⟨hb, ht⟩
      rw [ite_eq_right hra, ite_eq_left rfl, hX a t (Or.inl ⟨ha, ht⟩), hX r t (Or.inl ⟨hb, ht⟩)]
      ring
    · rw [ite_eq_right hra, ite_eq_right hrb]

/-- **The column update over the window's rows** of a decoupled array is the full rotation. -/
private theorem givensApplyRight_window (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n)
    {X : Matrix (Fin m) (Fin n) ℝ} (hX : IsDecoupledAt p q X) {a b : Fin n}
    (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q) (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b) (c s : ℝ) :
    Id.run (Chapter05.givensApplyRight pure a b c s
        ((francisWindow n p q).map (Fin.castLE hnm)) X) =
      X * Chapter05.givensRotation a b c s := by
  refine Chapter07.givensApplyRight_eq_mul hab c s
    ((Chapter07.nodup_francisWindow n p q).map (Fin.castLE_injective hnm)) fun r hr => ?_
  rw [mem_map_castLE_francisWindow hnm hq] at hr
  exact ⟨hX r a (Or.inr ⟨hr, ha⟩), hX r b (Or.inr ⟨hr, hb⟩)⟩

/-- **The row update over the window's columns** of a decoupled array is the full rotation. -/
private theorem givensApplyLeft_window {p q : ℕ} {X : Matrix (Fin m) (Fin n) ℝ}
    (hX : IsDecoupledAt p q X) {a b : Fin m} (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q)
    (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b) (c s : ℝ) :
    Id.run (Chapter05.givensApplyLeft pure a b c s (francisWindow n p q) X) =
      (Chapter05.givensRotation a b c s)ᵀ * X := by
  refine Chapter07.givensApplyLeft_eq_mul hab c s (Chapter07.nodup_francisWindow n p q)
    fun t ht => ?_
  rw [Chapter07.mem_francisWindow] at ht
  exact ⟨hX a t (Or.inl ⟨ha, ht⟩), hX b t (Or.inl ⟨hb, ht⟩)⟩

/-! #### Algorithm 8.6.1 on a window of an `m × n` array -/

/-- The zero pattern of the Golub–Kahan chase before the pair `(a, a + 1)`: upper bidiagonal but
for the bulge `(a - 1, a + 1)`. -/
private def IsRowBulgeAt (a : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (i : Fin m) (l : Fin n), ((l : ℕ) < i ∨ (i : ℕ) + 1 < l) →
    ¬ ((i : ℕ) + 1 = a ∧ (l : ℕ) = a + 1) → X i l = 0

/-- The zero pattern after the column rotation of the pair `(a, a + 1)`: upper bidiagonal but for
the bulge `(a + 1, a)`. -/
private def IsColBulgeAt (a : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (i : Fin m) (l : Fin n), ((l : ℕ) < i ∨ (i : ℕ) + 1 < l) →
    ¬ ((i : ℕ) = a + 1 ∧ (l : ℕ) = a) → X i l = 0

/-- The column rotation of the pair `(a, a + 1)`, annihilating the bulge `(a - 1, a + 1)`, moves
it to `(a + 1, a)`. -/
private theorem isColBulgeAt_mul {a : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} (hX : IsRowBulgeAt a X)
    {a' b' : Fin n} (ha : (a' : ℕ) = a) (hb : (b' : ℕ) = a + 1) {c s : ℝ}
    (hz : ∀ pr : Fin m, (pr : ℕ) + 1 = a → s * X pr a' + c * X pr b' = 0) :
    IsColBulgeAt a (X * Chapter05.givensRotation a' b' c s) := by
  have hab : a' ≠ b' := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  intro i l hil hnb
  rw [Chapter07.mul_givensRotation_apply hab]
  by_cases hla : l = a'
  · rw [ite_eq_left hla]
    subst hla
    rw [hX i l (by omega) (by omega), hX i b' (by omega) (by omega)]
    ring
  rw [ite_eq_right hla]
  by_cases hlb : l = b'
  · rw [ite_eq_left hlb]
    subst hlb
    by_cases hi1 : (i : ℕ) + 1 = a
    · linear_combination hz i hi1
    · rw [hX i a' (by omega) (by omega), hX i l (by omega) (by omega)]
      ring
  rw [ite_eq_right hlb]
  exact hX i l hil (fun h => hlb (Fin.ext (by omega)))

/-- The row rotation of the pair `(a, a + 1)`, annihilating the bulge `(a + 1, a)`, moves it to
`(a, a + 2)`. -/
private theorem isRowBulgeAt_mul {a : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} (hX : IsColBulgeAt a X)
    {ra rb : Fin m} {a' : Fin n} (hra : (ra : ℕ) = a) (hrb : (rb : ℕ) = a + 1)
    (ha : (a' : ℕ) = a) {c s : ℝ} (hz : s * X ra a' + c * X rb a' = 0) :
    IsRowBulgeAt (a + 1) ((Chapter05.givensRotation ra rb c s)ᵀ * X) := by
  have hab : ra ≠ rb := fun e => by rw [Fin.ext_iff, hra, hrb] at e; omega
  intro i l hil hnb
  rw [Chapter05.givensRotation_transpose_mul_apply hab]
  by_cases hia : i = ra
  · rw [ite_eq_left hia]
    subst hia
    rw [hX i l (by omega) (by omega), hX rb l (by omega) (by omega)]
    ring
  rw [ite_eq_right hia]
  by_cases hib : i = rb
  · rw [ite_eq_left hib]
    subst hib
    by_cases hla : l = a'
    · subst hla
      exact hz
    · have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext (by omega))
      rw [hX ra l (by omega) (by omega), hX i l (by omega) (by omega)]
      ring
  rw [ite_eq_right hib]
  exact hX i l hil (fun h => hib (Fin.ext (by omega)))

/-- **One chasing pair of Algorithm 8.6.1 on a window of a decoupled array, exactly**: the new
state is `(G'ᵀ (X G), U G', V G, a)` for the column rotation `G` of the pair and the row rotation
`G'` of the new `(x_aa, x_ba)`. -/
private theorem golubKahanRotate_window (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n)
    {X : Matrix (Fin m) (Fin n) ℝ} (hX : IsDecoupledAt p q X) {a b : Fin n}
    (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < q) (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < q) (hab : a ≠ b)
    (y₀ z₀ : ℝ) (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    (prev : Option (Fin n)) :
    let yz : ℝ × ℝ := prev.elim (y₀, z₀) fun pr =>
      (X (Fin.castLE hnm pr) a, X (Fin.castLE hnm pr) b)
    let cs := Id.run (Chapter05.algorithm_5_1_3 pure yz.1 yz.2)
    let B₁ := X * Chapter05.givensRotation a b cs.1 cs.2
    let cs' := Id.run (Chapter05.algorithm_5_1_3 pure (B₁ (Fin.castLE hnm a) a)
      (B₁ (Fin.castLE hnm b) a))
    Id.run (golubKahanRotate pure hnm (francisWindow n p q) y₀ z₀ (X, U, V, prev) (a, b)) =
      ((Chapter05.givensRotation (Fin.castLE hnm a) (Fin.castLE hnm b) cs'.1 cs'.2)ᵀ * B₁,
        U * Chapter05.givensRotation (Fin.castLE hnm a) (Fin.castLE hnm b) cs'.1 cs'.2,
        V * Chapter05.givensRotation a b cs.1 cs.2, some a) := by
  intro yz cs B₁ cs'
  have hcab : Fin.castLE hnm a ≠ Fin.castLE hnm b := fun e => hab (Fin.castLE_injective hnm e)
  have hB₁ : ∀ c s : ℝ, IsDecoupledAt p q (X * Chapter05.givensRotation a b c s) := fun c s =>
    hX.of_agreeOff (agreeOff_mul_givensRotation hX ha hb hab c s)
  simp only [golubKahanRotate, Id.run_bind, Id.run_pure]
  rw [givensApplyRight_window hnm hq hX ha hb hab,
    givensApplyLeft_window (hB₁ _ _) ha hb hcab,
    Chapter05.givensApplyRight_spec_of_forall_mem hab _ _ (List.nodup_finRange n)
      List.mem_finRange,
    Chapter05.givensApplyRight_spec_of_forall_mem hcab _ _ (List.nodup_finRange m)
      List.mem_finRange]

/-- The loop invariant of Algorithm 8.6.1 on the window `[p, q)` of an `m × n` array after `j`
chasing pairs: the state `(X, U', V', prev)` is `(Gᵀ B H, U G, V H, p + j - 1)` for orthogonal
`G`, `H`, `X` agrees with `B` off the block and has the zero pattern of the chase. -/
private def GKWindowInv (p q : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin m) (Fin m) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Option (Fin n)) : Prop :=
  ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
    st.1 = Gᵀ * B * H ∧ st.2.1 = U * G ∧ st.2.2.1 = V * H ∧ AgreeOff p q st.1 B ∧
    IsRowBulgeAt (p + j) st.1 ∧ st.2.2.2.elim (j = 0) (fun pr => 1 ≤ j ∧ (pr : ℕ) + 1 = p + j)

/-- **The bulge chase of Algorithm 8.6.1 on a window**, the loop: the invariant holds after the
`q - p - 1` chasing pairs, whatever the first pair `(y₀, z₀)`. -/
private theorem gkWindowInv_run (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n) (hpq : p + 2 ≤ q)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (y₀ z₀ : ℝ) :
    GKWindowInv p q B U V (q - p - 1)
      (Id.run (((francisWindow n p q).zip (francisWindow n p q).tail).foldlM
        (golubKahanRotate pure hnm (francisWindow n p q) y₀ z₀) (B, U, V, none))) := by
  set w := francisWindow n p q with hwdef
  have hlen : w.length = q - p := length_francisWindow' hq
  have hval : ∀ k (hk : k < w.length), (w[k] : ℕ) = p + k := val_getElem_francisWindow' hq
  have hzlen : (w.zip w.tail).length = q - p - 1 := by simp [hlen]
  rw [← hzlen]
  refine idRun_foldlM_induction _ _ _ ⟨1, one_mem _, 1, one_mem _, by simp,
    (Matrix.mul_one U).symm, (Matrix.mul_one V).symm, fun _ _ _ => rfl,
    fun i l hil _ => hB i l (by omega) (by omega), rfl⟩ ?_
  intro j hj ⟨X, Ua, Va, prev⟩ ⟨G, hGo, H, hHo, hX, hUa, hVa, hXa, hXc, hprev⟩
  simp only at hX hUa hVa hXa hXc hprev
  rw [hzlen] at hj
  have hja : j < w.length := by omega
  have hjb : j + 1 < w.length := by omega
  have hpair : (w.zip w.tail)[j]'(by rw [hzlen]; exact hj) = (w[j], w[j + 1]) := by
    simp [List.getElem_zip, List.getElem_tail]
  rw [hpair]
  set a := w[j] with hadef
  set b := w[j + 1] with hbdef
  have ha : (a : ℕ) = p + j := hval j hja
  have hb : (b : ℕ) = p + j + 1 := hval (j + 1) hjb
  have hab : a ≠ b := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  have hXd : IsDecoupledAt p q X := hBd.of_agreeOff hXa
  have haw : p ≤ (a : ℕ) ∧ (a : ℕ) < q := ⟨by omega, by omega⟩
  have hbw : p ≤ (b : ℕ) ∧ (b : ℕ) < q := ⟨by omega, by omega⟩
  rw [golubKahanRotate_window hnm hq hXd haw hbw hab]
  set yz : ℝ × ℝ := prev.elim (y₀, z₀) fun pr =>
    (X (Fin.castLE hnm pr) a, X (Fin.castLE hnm pr) b) with hyz
  obtain ⟨hcs, hzcs, -⟩ := Chapter05.algorithm_5_1_3_spec yz.1 yz.2
  set cs := Id.run (Chapter05.algorithm_5_1_3 pure yz.1 yz.2)
  set Gc := Chapter05.givensRotation a b cs.1 cs.2 with hGc
  set ra := Fin.castLE hnm a with hradef
  set rb := Fin.castLE hnm b with hrbdef
  have hra : (ra : ℕ) = p + j := ha
  have hrb : (rb : ℕ) = p + j + 1 := hb
  have hrab : ra ≠ rb := fun e => by rw [Fin.ext_iff, hra, hrb] at e; omega
  obtain ⟨hcs', hzcs', -⟩ := Chapter05.algorithm_5_1_3_spec ((X * Gc) ra a) ((X * Gc) rb a)
  set cs' := Id.run (Chapter05.algorithm_5_1_3 pure ((X * Gc) ra a) ((X * Gc) rb a))
  set Gr := Chapter05.givensRotation ra rb cs'.1 cs'.2 with hGr
  have hGco : Gc ∈ orthogonalGroup (Fin n) ℝ :=
    Chapter05.givensRotation_mem_orthogonalGroup hab hcs
  have hGro : Gr ∈ orthogonalGroup (Fin m) ℝ :=
    Chapter05.givensRotation_mem_orthogonalGroup hrab hcs'
  have hXGa : AgreeOff p q (X * Gc) X := agreeOff_mul_givensRotation hXd haw hbw hab _ _
  have hXGd : IsDecoupledAt p q (X * Gc) := hXd.of_agreeOff hXGa
  have hXGc : IsColBulgeAt (p + j) (X * Gc) := isColBulgeAt_mul hXc ha hb fun pr hpr => by
    cases prev with
    | none =>
      have hj0 : j = 0 := hprev
      rw [hXd pr a (Or.inr ⟨by omega, haw⟩), hXd pr b (Or.inr ⟨by omega, hbw⟩)]
      ring
    | some pr' =>
      have h2 : (pr' : ℕ) + 1 = p + j := hprev.2
      have hpr' : pr = Fin.castLE hnm pr' := Fin.ext (by simp only [Fin.val_castLE]; omega)
      subst hpr'
      exact hzcs
  refine ⟨G * Gr, Submonoid.mul_mem _ hGo hGro, H * Gc, Submonoid.mul_mem _ hHo hGco, ?_, ?_, ?_,
    (agreeOff_givensRotation_transpose_mul hXGd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hrab
      _ _).trans (hXGa.trans hXa), ?_, ⟨Nat.succ_pos _, by omega⟩⟩
  · simp only
    rw [hX, transpose_mul]
    simp only [Matrix.mul_assoc]
  · simp only
    rw [hUa, Matrix.mul_assoc]
  · simp only
    rw [hVa, Matrix.mul_assoc]
  · have := isRowBulgeAt_mul hXGc hra hrb ha hzcs'
    rwa [show p + j + 1 = p + (j + 1) by omega] at this

/-- A matrix with the zero pattern of the chase after the last pair of the window `[p, q)`, equal
to an upper bidiagonal matrix off the block, is upper bidiagonal. -/
private theorem isUpperBidiagonalRect_of_isRowBulgeAt {p q : ℕ} (hpq : p + 2 ≤ q)
    {X B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hXa : AgreeOff p q X B)
    (hX : IsRowBulgeAt (q - 1) X) : X.IsUpperBidiagonalRect := by
  intro i l h1 h2
  by_cases hb : (i : ℕ) + 1 = q - 1 ∧ (l : ℕ) = q - 1 + 1
  · rw [hXa i l (fun h => by omega)]
    exact hB i l h1 h2
  · exact hX i l (by omega) hb

/-- **Algorithm 8.6.1 on a window of an `m × n` array** (what Algorithm 8.6.2 runs on `B₂₂`): for
an upper bidiagonal `B` decoupled along the window `[p, q)` of at least two indices, the exact run
`(B', U', V')` has orthogonal `G`, `H` with `B' = Gᵀ B H` upper bidiagonal, `U' = U G`,
`V' = V H`, and `B'` agrees with `B` off the block. -/
private theorem algorithm_8_6_1_window (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n) (hpq : p + 2 ≤ q)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    let out := Id.run (algorithm_8_6_1 pure hnm (francisWindow n p q) B U V)
    ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      out.1 = Gᵀ * B * H ∧ out.2.1 = U * G ∧ out.2.2 = V * H ∧ out.1.IsUpperBidiagonalRect ∧
      AgreeOff p q out.1 B := by
  intro out
  obtain ⟨f₀, f₁, rest, hw⟩ := exists_cons_cons (francisWindow n p q)
    (by rw [length_francisWindow' hq]; omega)
  have key := gkWindowInv_run hnm hq hpq hB hBd U V
  rw [hw] at key
  simp only [List.tail_cons] at key
  obtain ⟨y₀, z₀, hout⟩ : ∃ y₀ z₀ : ℝ, out =
      ((Id.run (((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
          (golubKahanRotate pure hnm (f₀ :: f₁ :: rest) y₀ z₀) (B, U, V, none))).1,
        (Id.run (((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
          (golubKahanRotate pure hnm (f₀ :: f₁ :: rest) y₀ z₀) (B, U, V, none))).2.1,
        (Id.run (((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
          (golubKahanRotate pure hnm (f₀ :: f₁ :: rest) y₀ z₀) (B, U, V, none))).2.2.1) := by
    exact ⟨_, _, by
      change Id.run (algorithm_8_6_1 pure hnm (francisWindow n p q) B U V) = _
      rw [hw]
      rfl⟩
  obtain ⟨G, hG, H, hH, h1, h2, h3, ha, hc, -⟩ := key y₀ z₀
  rw [hout]
  exact ⟨G, hG, H, hH, h1, h2, h3, isUpperBidiagonalRect_of_isRowBulgeAt hpq hB ha
    (by rwa [show p + (q - p - 1) = q - 1 by omega] at hc), ha⟩

/-! #### The zero-diagonal chases of Algorithm 8.6.2 -/

/-- **One step of the row chase** of §8.6.3 (`bidiagonal_decouple` (ii)) on an `m × n` array: if
the rows other than `k` have the bidiagonal pattern and row `k` is supported in column `j > k`,
the rotation of the rows `(j, k)` by `givens(x_jj, x_kj)` keeps the pattern and moves the support
of row `k` to column `j + 1`. -/
private theorem rowChase_step' {k j : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} {rj rk : Fin m}
    {cj : Fin n} (hrj : (rj : ℕ) = j) (hrk : (rk : ℕ) = k) (hcj : (cj : ℕ) = j) (hkj : k < j)
    (hrows : ∀ (i : Fin m) (l : Fin n), (i : ℕ) ≠ k → X i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1)
    (hrow : ∀ (i : Fin m) (l : Fin n), (i : ℕ) = k → X i l ≠ 0 → (l : ℕ) = j) {c s : ℝ}
    (hz : s * X rj cj + c * X rk cj = 0) :
    (∀ (i : Fin m) (l : Fin n), (i : ℕ) ≠ k →
        ((Chapter05.givensRotation rj rk c s)ᵀ * X) i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (i : ℕ) = k →
        ((Chapter05.givensRotation rj rk c s)ᵀ * X) i l ≠ 0 → (l : ℕ) = j + 1 := by
  have hjk : rj ≠ rk := fun e => by rw [Fin.ext_iff, hrj, hrk] at e; omega
  refine ⟨fun i l hik h => ?_, fun i l hik h => ?_⟩
  · rw [Chapter05.givensRotation_transpose_mul_apply hjk] at h
    by_cases h1 : i = rj
    · rw [ite_eq_left h1] at h
      by_cases hx : X rk l = 0
      · rw [hx, mul_zero, sub_zero] at h
        have := hrows rj l (by omega) (right_ne_zero_of_mul h)
        rwa [h1]
      · have := hrow rk l hrk hx
        left
        rw [h1]
        omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : i = rk
      · exact (hik (by rw [h2]; exact hrk)).elim
      · rw [ite_eq_right h2] at h
        exact hrows i l hik h
  · have hi : i = rk := Fin.ext (by omega)
    rw [Chapter05.givensRotation_transpose_mul_apply hjk, ite_eq_right (by rw [hi]; exact hjk.symm),
      ite_eq_left hi] at h
    by_cases hl : l = cj
    · rw [hl] at h
      exact absurd hz h
    · have hx : X rk l = 0 := by
        by_contra hx
        exact hl (Fin.ext (by rw [hrow rk l hrk hx, hcj]))
      rw [hx, mul_zero, add_zero] at h
      rcases hrows rj l (by omega) (right_ne_zero_of_mul h) with h3 | h3
      · exact absurd (Fin.ext (by omega)) hl
      · omega

/-- **One step of the column chase** of §8.6.3 (`bidiagonal_decouple` (iii)): if the columns
other than `k` have the bidiagonal pattern and column `k` is supported in row `j < k`, the rotation
of the columns `(j, k)` by `givens(x_jj, x_jk)` keeps the pattern and moves the support of column
`k` to row `j - 1`. -/
private theorem colChase_step' {k j : ℕ} {X : Matrix (Fin m) (Fin n) ℝ} {rj : Fin m}
    {cj ck : Fin n} (hrj : (rj : ℕ) = j) (hcj : (cj : ℕ) = j) (hck : (ck : ℕ) = k) (hjk : j < k)
    (hcols : ∀ (i : Fin m) (l : Fin n), (l : ℕ) ≠ k → X i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1)
    (hcol : ∀ (i : Fin m) (l : Fin n), (l : ℕ) = k → X i l ≠ 0 → (i : ℕ) = j) {c s : ℝ}
    (hz : s * X rj cj + c * X rj ck = 0) :
    (∀ (i : Fin m) (l : Fin n), (l : ℕ) ≠ k →
        (X * Chapter05.givensRotation cj ck c s) i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (l : ℕ) = k →
        (X * Chapter05.givensRotation cj ck c s) i l ≠ 0 → (i : ℕ) + 1 = j := by
  have hjk' : cj ≠ ck := fun e => by rw [Fin.ext_iff, hcj, hck] at e; omega
  refine ⟨fun i l hlk h => ?_, fun i l hlk h => ?_⟩
  · rw [Chapter07.mul_givensRotation_apply hjk'] at h
    by_cases h1 : l = cj
    · rw [ite_eq_left h1] at h
      by_cases hx : X i ck = 0
      · rw [hx, mul_zero, sub_zero] at h
        have := hcols i cj (by omega) (right_ne_zero_of_mul h)
        rwa [h1]
      · have := hcol i ck hck hx
        left
        rw [h1]
        omega
    · rw [ite_eq_right h1] at h
      by_cases h2 : l = ck
      · exact (hlk (by rw [h2]; exact hck)).elim
      · rw [ite_eq_right h2] at h
        exact hcols i l hlk h
  · have hl : l = ck := Fin.ext (by omega)
    rw [Chapter07.mul_givensRotation_apply hjk', ite_eq_right (by rw [hl]; exact hjk'.symm),
      ite_eq_left hl] at h
    by_cases hi : i = rj
    · rw [hi] at h
      exact absurd hz h
    · have hx : X i ck = 0 := by
        by_contra hx
        exact hi (Fin.ext (by rw [hcol i ck hck hx, hrj]))
      rw [hx, mul_zero, add_zero] at h
      rcases hcols i cj (by omega) (right_ne_zero_of_mul h) with h3 | h3
      · exact absurd (Fin.ext (by omega)) hi
      · omega

/-- The indices of the window `[p, q)` after `k ≥ p` are the window `[k + 1, q)`. -/
private theorem filter_gt_francisWindow {p q : ℕ} (k : Fin n) (hpk : p ≤ (k : ℕ)) :
    (francisWindow n p q).filter (fun j => decide (k < j)) = francisWindow n (k + 1) q := by
  unfold Chapter07.francisWindow
  rw [List.filter_filter]
  refine List.filter_congr fun i _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.lt_def]
  omega

/-- The indices of the window `[p, q)` before `k ≤ q` are the window `[p, k)`. -/
private theorem filter_lt_francisWindow {p q : ℕ} (k : Fin n) (hkq : (k : ℕ) ≤ q) :
    (francisWindow n p q).filter (fun j => decide (j < k)) = francisWindow n p k := by
  unfold Chapter07.francisWindow
  rw [List.filter_filter]
  refine List.filter_congr fun i _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.lt_def]
  omega

/-- **The row chase of Algorithm 8.6.2, exactly** (`bidiagonal_decouple` (ii) on the window
`[p, q)`): for an upper bidiagonal `B` decoupled along the window with `b_kk = 0`, `k` not the last
index of the window, the rotations of the rows `(j, k)`, `j = k + 1, …, q - 1`, give
`G` orthogonal with `Gᵀ B` upper bidiagonal (row `k` zeroed), agreeing with `B` off the block. The
loop body `f` is any whose exact run is the program's. -/
private theorem rowChase_spec (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    {k : Fin n} (hpk : p ≤ (k : ℕ)) (hkq : (k : ℕ) + 1 < q) (hkk : B (Fin.castLE hnm k) k = 0)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    {f : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ → Fin n →
      Id (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ)}
    (hf : ∀ st j, Id.run (f st j) =
      (Id.run (Chapter05.givensApplyLeft pure (Fin.castLE hnm j) (Fin.castLE hnm k)
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm k) j))).1
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm k) j))).2 (francisWindow n p q) st.1),
        Id.run (Chapter05.givensApplyRight pure (Fin.castLE hnm j) (Fin.castLE hnm k)
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm k) j))).1
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm k) j))).2 (List.finRange m) st.2.1), st.2.2)) :
    let out := Id.run ((francisWindow n (k + 1) q).foldlM f (B, U, V))
    ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      out.1 = Gᵀ * B * H ∧ out.2.1 = U * G ∧ out.2.2 = V * H ∧ out.1.IsUpperBidiagonalRect ∧
      AgreeOff p q out.1 B := by
  intro out
  set L := francisWindow n (k + 1) q with hL
  have hlen : L.length = q - (k + 1) := length_francisWindow' hq
  have hval : ∀ t (ht : t < L.length), (L[t] : ℕ) = k + 1 + t := val_getElem_francisWindow' hq
  have key : ∃ G ∈ orthogonalGroup (Fin m) ℝ, out.1 = Gᵀ * B ∧ out.2.1 = U * G ∧ out.2.2 = V ∧
      AgreeOff p q out.1 B ∧
      (∀ (i : Fin m) (l : Fin n), (i : ℕ) ≠ k → out.1 i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (i : ℕ) = k → out.1 i l ≠ 0 → (l : ℕ) = k + 1 + L.length := by
    refine idRun_foldlM_induction L (fun t st => ∃ G ∈ orthogonalGroup (Fin m) ℝ,
      st.1 = Gᵀ * B ∧ st.2.1 = U * G ∧ st.2.2 = V ∧ AgreeOff p q st.1 B ∧
      (∀ (i : Fin m) (l : Fin n), (i : ℕ) ≠ k → st.1 i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (i : ℕ) = k → st.1 i l ≠ 0 → (l : ℕ) = k + 1 + t) (B, U, V)
      ⟨1, one_mem _, by simp, (Matrix.mul_one U).symm, rfl, fun _ _ _ => rfl,
        fun i l _ h => ?_, fun i l hi h => ?_⟩ ?_
    · by_contra hc
      exact h (hB i l (by omega) (by omega))
    · by_contra hc
      refine h ?_
      by_cases hl : (l : ℕ) = k
      · rw [show i = Fin.castLE hnm k from Fin.ext hi, show l = k from Fin.ext hl]
        exact hkk
      · exact hB i l (by omega) (by omega)
    intro t ht ⟨X, Ua, Va⟩ ⟨G, hGo, hX, hUa, hVa, hXa, hrows, hrow⟩
    simp only at hX hUa hVa hXa hrows hrow
    have hj : (L[t] : ℕ) = k + 1 + t := hval t ht
    have hjq : (L[t] : ℕ) < q := by omega
    have hrj : (Fin.castLE hnm L[t] : ℕ) = k + 1 + t := hj
    have hrk : (Fin.castLE hnm k : ℕ) = k := rfl
    have hjk : Fin.castLE hnm L[t] ≠ Fin.castLE hnm k := fun e => by
      rw [Fin.ext_iff, hrj, hrk] at e; omega
    have hXd : IsDecoupledAt p q X := hBd.of_agreeOff hXa
    rw [hf]
    simp only
    obtain ⟨hcs, hzcs, -⟩ := Chapter05.algorithm_5_1_3_spec (X (Fin.castLE hnm L[t]) L[t])
      (X (Fin.castLE hnm k) L[t])
    set cs := Id.run (Chapter05.algorithm_5_1_3 pure (X (Fin.castLE hnm L[t]) L[t])
      (X (Fin.castLE hnm k) L[t]))
    have hjw : p ≤ (Fin.castLE hnm L[t] : ℕ) ∧ (Fin.castLE hnm L[t] : ℕ) < q :=
      ⟨by omega, by omega⟩
    have hkw : p ≤ (Fin.castLE hnm k : ℕ) ∧ (Fin.castLE hnm k : ℕ) < q := ⟨by omega, by omega⟩
    rw [givensApplyLeft_window hXd hjw hkw hjk,
      Chapter05.givensApplyRight_spec_of_forall_mem hjk _ _ (List.nodup_finRange m)
        List.mem_finRange]
    obtain ⟨h1, h2⟩ := rowChase_step' hrj hrk hj (by omega) hrows hrow hzcs
    refine ⟨G * Chapter05.givensRotation (Fin.castLE hnm L[t]) (Fin.castLE hnm k) cs.1 cs.2,
      Submonoid.mul_mem _ hGo (Chapter05.givensRotation_mem_orthogonalGroup hjk hcs), ?_, ?_, hVa,
      (agreeOff_givensRotation_transpose_mul hXd hjw hkw hjk _ _).trans hXa, h1,
      fun i l hi h => by have := h2 i l hi h; omega⟩
    · rw [hX, transpose_mul, Matrix.mul_assoc]
    · rw [hUa, Matrix.mul_assoc]
  obtain ⟨G, hG, h1, h2, h3, ha, hrows, hrow⟩ := key
  refine ⟨G, hG, 1, one_mem _, by rw [h1, Matrix.mul_one], h2, by rw [h3, Matrix.mul_one],
    fun i l hl1 hl2 => ?_, ha⟩
  by_contra h0
  by_cases hik : (i : ℕ) = k
  · have hlq := hrow i l hik h0
    rw [hlen] at hlq
    exact h0 ((ha i l fun h => by omega).trans (hB i l (by omega) (by omega)))
  · rcases hrows i l hik h0 with h | h <;> omega

/-- **The column chase of Algorithm 8.6.2, exactly** (`bidiagonal_decouple` (iii) on the window
`[p, q)`): for an upper bidiagonal `B` decoupled along the window with `b_kk = 0`, `k = q - 1` the
last index of the window, the rotations of the columns `(j, k)`, `j = k - 1, …, p`, give `H`
orthogonal with `B H` upper bidiagonal (column `k` zeroed), agreeing with `B` off the block. -/
private theorem colChase_spec (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    {k : Fin n} (hpk : p + 1 ≤ (k : ℕ)) (hkq : (k : ℕ) < q) (hkk : B (Fin.castLE hnm k) k = 0)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    {f : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ → Fin n →
      Id (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ)}
    (hf : ∀ st j, Id.run (f st j) =
      (Id.run (Chapter05.givensApplyRight pure j k
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm j) k))).1
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm j) k))).2 ((francisWindow n p q).map (Fin.castLE hnm)) st.1),
        st.2.1,
        Id.run (Chapter05.givensApplyRight pure j k
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm j) k))).1
          (Id.run (Chapter05.algorithm_5_1_3 pure (st.1 (Fin.castLE hnm j) j)
            (st.1 (Fin.castLE hnm j) k))).2 (List.finRange n) st.2.2))) :
    let out := Id.run ((francisWindow n p k).reverse.foldlM f (B, U, V))
    ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      out.1 = Gᵀ * B * H ∧ out.2.1 = U * G ∧ out.2.2 = V * H ∧ out.1.IsUpperBidiagonalRect ∧
      AgreeOff p q out.1 B := by
  intro out
  set L := (francisWindow n p k).reverse with hL
  have hlen : L.length = k - p := by
    rw [hL, List.length_reverse, length_francisWindow' (by omega)]
  have hval : ∀ t (ht : t < L.length), (L[t] : ℕ) + t + 1 = k := fun t ht => by
    have ht' := ht
    rw [hlen] at ht'
    simp only [hL, List.getElem_reverse]
    rw [val_getElem_francisWindow' (by omega), length_francisWindow' (by omega)]
    omega
  have key : ∃ H ∈ orthogonalGroup (Fin n) ℝ, out.1 = B * H ∧ out.2.1 = U ∧ out.2.2 = V * H ∧
      AgreeOff p q out.1 B ∧
      (∀ (i : Fin m) (l : Fin n), (l : ℕ) ≠ k → out.1 i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (l : ℕ) = k → out.1 i l ≠ 0 → (i : ℕ) + L.length + 1 = k := by
    refine idRun_foldlM_induction L (fun t st => ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      st.1 = B * H ∧ st.2.1 = U ∧ st.2.2 = V * H ∧ AgreeOff p q st.1 B ∧
      (∀ (i : Fin m) (l : Fin n), (l : ℕ) ≠ k → st.1 i l ≠ 0 → (l : ℕ) = i ∨ (l : ℕ) = i + 1) ∧
      ∀ (i : Fin m) (l : Fin n), (l : ℕ) = k → st.1 i l ≠ 0 → (i : ℕ) + t + 1 = k) (B, U, V)
      ⟨1, one_mem _, (Matrix.mul_one B).symm, rfl, (Matrix.mul_one V).symm, fun _ _ _ => rfl,
        fun i l _ h => ?_, fun i l hl h => ?_⟩ ?_
    · by_contra hc
      exact h (hB i l (by omega) (by omega))
    · by_contra hc
      refine h ?_
      by_cases hi : (i : ℕ) = k
      · rw [show i = Fin.castLE hnm k from Fin.ext hi, show l = k from Fin.ext hl]
        exact hkk
      · exact hB i l (by omega) (by omega)
    intro t ht ⟨X, Ua, Va⟩ ⟨H, hHo, hX, hUa, hVa, hXa, hcols, hcol⟩
    simp only at hX hUa hVa hXa hcols hcol
    have hj : (L[t] : ℕ) + t + 1 = k := hval t ht
    have hrj : (Fin.castLE hnm L[t] : ℕ) = k - 1 - t := by simp only [Fin.val_castLE]; omega
    have hcj : (L[t] : ℕ) = k - 1 - t := by omega
    have hjk : L[t] ≠ k := fun e => by rw [Fin.ext_iff] at e; omega
    have hXd : IsDecoupledAt p q X := hBd.of_agreeOff hXa
    rw [hf]
    simp only
    obtain ⟨hcs, hzcs, -⟩ := Chapter05.algorithm_5_1_3_spec (X (Fin.castLE hnm L[t]) L[t])
      (X (Fin.castLE hnm L[t]) k)
    set cs := Id.run (Chapter05.algorithm_5_1_3 pure (X (Fin.castLE hnm L[t]) L[t])
      (X (Fin.castLE hnm L[t]) k))
    have hjw : p ≤ (L[t] : ℕ) ∧ (L[t] : ℕ) < q := by
      have hmem : L[t] ∈ francisWindow n p k := List.mem_reverse.1 (List.getElem_mem ht)
      have := Chapter07.mem_francisWindow.1 hmem
      omega
    have hkw : p ≤ (k : ℕ) ∧ (k : ℕ) < q := ⟨by omega, hkq⟩
    rw [givensApplyRight_window hnm hq hXd hjw hkw hjk,
      Chapter05.givensApplyRight_spec_of_forall_mem hjk _ _ (List.nodup_finRange n)
        List.mem_finRange]
    obtain ⟨h1, h2⟩ := colChase_step' hrj hcj rfl (by omega) hcols
      (fun i l hl h => by have := hcol i l hl h; omega) hzcs
    refine ⟨H * Chapter05.givensRotation L[t] k cs.1 cs.2,
      Submonoid.mul_mem _ hHo (Chapter05.givensRotation_mem_orthogonalGroup hjk hcs), ?_, hUa, ?_,
      (agreeOff_mul_givensRotation hXd hjw hkw hjk _ _).trans hXa, h1,
      fun i l hl h => by have := h2 i l hl h; omega⟩
    · rw [hX, Matrix.mul_assoc]
    · rw [hVa, Matrix.mul_assoc]
  obtain ⟨H, hH, h1, h2, h3, ha, hcols, hcol⟩ := key
  refine ⟨1, one_mem _, H, hH, by rw [h1, transpose_one, Matrix.one_mul],
    by rw [h2, Matrix.mul_one],
    h3, fun i l hl1 hl2 => ?_, ha⟩
  by_contra h0
  by_cases hlk : (l : ℕ) = k
  · have hip := hcol i l hlk h0
    rw [hlen] at hip
    exact h0 ((ha i l fun h => by omega).trans (hB i l (by omega) (by omega)))
  · rcases hcols i l hlk h0 with h | h <;> omega

/-- **The zero-diagonal branch of Algorithm 8.6.2, exactly**: for an upper bidiagonal `B`
decoupled along the window `[p, q)` of at least two indices and a window index `k` with
`b_kk = 0`, `zeroDiagonalChase` (the row chase if `k < q - 1`, the column chase if `k = q - 1`)
gives orthogonal `G`, `H` with `B' = Gᵀ B H` upper bidiagonal, `U' = U G`, `V' = V H`, and `B'`
agrees with `B` off the block. -/
private theorem zeroDiagonalChase_window (hnm : n ≤ m) {p q : ℕ} (hq : q ≤ n) (hpq : p + 2 ≤ q)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.IsUpperBidiagonalRect) (hBd : IsDecoupledAt p q B)
    {k : Fin n} (hk : p ≤ (k : ℕ) ∧ (k : ℕ) < q) (hkk : B (Fin.castLE hnm k) k = 0)
    (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    let out := Id.run (zeroDiagonalChase pure hnm (francisWindow n p q) k B U V)
    ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      out.1 = Gᵀ * B * H ∧ out.2.1 = U * G ∧ out.2.2 = V * H ∧ out.1.IsUpperBidiagonalRect ∧
      AgreeOff p q out.1 B := by
  intro out
  have hlast : (francisWindow n p q).getLast? = some k ↔ (k : ℕ) = q - 1 := by
    have hl : (francisWindow n p q).length - 1 < (francisWindow n p q).length := by
      rw [length_francisWindow' hq]; omega
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hl, Option.some_inj]
    constructor
    · rintro h
      rw [← h, val_getElem_francisWindow' hq, length_francisWindow' hq]
      omega
    · intro h
      apply Fin.ext
      rw [val_getElem_francisWindow' hq, h, length_francisWindow' hq]
      omega
  by_cases hkl : (k : ℕ) = q - 1
  · have hk' := hlast.2 hkl
    simp only [out, zeroDiagonalChase, hk', ↓reduceIte, filter_lt_francisWindow k hk.2.le]
    exact colChase_spec hnm hq hB hBd (by omega) hk.2 hkk U V (by intros; rfl)
  · have hk' : ¬ (francisWindow n p q).getLast? = some k := fun h => hkl (hlast.1 h)
    simp only [out, zeroDiagonalChase, hk', ↓reduceIte, filter_gt_francisWindow k hk.1]
    exact rowChase_spec hnm hq hB hBd hk.1 (by omega) hkk U V (by intros; rfl)

/-! #### The deflation pass of Algorithm 8.6.2 -/

/-- The deflation test of Algorithm 8.6.2 at the superdiagonal entry `a`, exactly:
`|b_{a,a+1}| ≤ ε (|b_aa| + |b_{a+1,a+1}|)`. -/
private def IsSmallSuper (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ) (a : ℕ) : Prop :=
  ∃ h : a + 1 < n, |D ⟨a, by omega⟩ ⟨a + 1, h⟩| ≤
    ε * (|D ⟨a, by omega⟩ ⟨a, by omega⟩| + |D ⟨a + 1, by omega⟩ ⟨a + 1, h⟩|)

open Classical in
/-- The array after the first `k` tests of the deflation pass of Algorithm 8.6.2, exactly: the
small superdiagonal entries among the first `k` set to `0`. -/
private noncomputable def svdDeflateStage (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun r s => if ∃ a < k, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a then 0
    else D r s

open Classical in
private theorem svdDeflateStage_succ_apply (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) (r : Fin m) (s : Fin n) :
    svdDeflateStage hnm ε D (k + 1) r s =
      if (r : ℕ) = k ∧ (s : ℕ) = k + 1 ∧ IsSmallSuper hnm ε D k then 0
      else svdDeflateStage hnm ε D k r s := by
  simp only [svdDeflateStage, of_apply]
  by_cases h1 : ∃ a < k, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a
  · obtain ⟨a, ha, hr, hs, hsm⟩ := h1
    have h1' : ∃ a < k + 1, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a :=
      ⟨a, by omega, hr, hs, hsm⟩
    have h1'' : ∃ a < k, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a :=
      ⟨a, ha, hr, hs, hsm⟩
    rw [ite_eq_left h1', ite_eq_left h1'', ite_self]
  · rw [ite_eq_right h1]
    by_cases h2 : (r : ℕ) = k ∧ (s : ℕ) = k + 1 ∧ IsSmallSuper hnm ε D k
    · have h2' : ∃ a < k + 1, (r : ℕ) = a ∧ (s : ℕ) = a + 1 ∧ IsSmallSuper hnm ε D a :=
        ⟨k, by omega, h2⟩
      rw [ite_eq_left h2', ite_eq_left h2]
    · rw [ite_eq_right, ite_eq_right h2]
      rintro ⟨a, ha, hr, hs, hsm⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · exact h1 ⟨a, ha, hr, hs, hsm⟩
      · exact h2 ⟨hr, hs, hsm⟩

/-- The deflation keeps the entries off the superdiagonal. -/
private theorem svdDeflateStage_apply_of_ne (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ)
    {k : ℕ} {r : Fin m} {s : Fin n} (h : (s : ℕ) ≠ r + 1) :
    svdDeflateStage hnm ε D k r s = D r s := by
  rw [svdDeflateStage, of_apply, ite_eq_right]
  rintro ⟨a, -, h1, h2, -⟩
  omega

open Classical in
/-- The deflation sets the small superdiagonal entries, and only those, to `0`. -/
private theorem svdDeflateStage_apply_super (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n) (h : (a : ℕ) + 1 < n) :
    svdDeflateStage hnm ε D n (Fin.castLE hnm a) ⟨a + 1, h⟩ =
      if IsSmallSuper hnm ε D a then 0 else D (Fin.castLE hnm a) ⟨a + 1, h⟩ := by
  simp only [svdDeflateStage, of_apply]
  by_cases hs : IsSmallSuper hnm ε D a
  · rw [ite_eq_left ⟨a, a.isLt, rfl, rfl, hs⟩, ite_eq_left hs]
  · rw [ite_eq_right, ite_eq_right hs]
    rintro ⟨b, -, h1, -, h3⟩
    have hb : b = a := by simp only [Fin.val_castLE] at h1; omega
    subst hb
    exact hs h3

/-- The Hoare rule of a loop over `List.finRange N` in `Id`. -/
private theorem idRun_foldlM_finRange_induction' {β : Type} {N : ℕ} {f : β → Fin N → Id β}
    (I : ℕ → β → Prop) {a : β} (h0 : I 0 a)
    (hs : ∀ (k : Fin N) (c : β), I k c → I (k + 1) (Id.run (f c k))) :
    I N (Id.run ((List.finRange N).foldlM f a)) := by
  have h := idRun_foldlM_induction (List.finRange N) I a h0 fun k hk c hc => by
    have e : (List.finRange N)[k] = ⟨k, by simpa using hk⟩ := by simp
    rw [e]
    exact hs ⟨k, _⟩ c hc
  rwa [List.length_finRange] at h

/-- **The deflation pass of Algorithm 8.6.2, exactly**: every test reads entries no earlier step
has changed, so the pass zeroes exactly the small superdiagonal entries of its input. -/
private theorem svdDeflate_pure (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (svdDeflate pure hnm ε D) = svdDeflateStage hnm ε D n := by
  unfold svdDeflate
  refine idRun_foldlM_finRange_induction' (fun k D' => D' = svdDeflateStage hnm ε D k) ?_ ?_
  · ext r s
    simp only [svdDeflateStage, of_apply]
    rw [ite_eq_right (fun ⟨a, ha, _⟩ => absurd ha (Nat.not_lt_zero a))]
  · intro k D' hD'
    have hstage : ∀ (r : Fin m) (s : Fin n), (s : ℕ) ≠ r + 1 ∨ (k : ℕ) ≤ r → D' r s = D r s := by
      intro r s h
      rw [hD', svdDeflateStage, of_apply, ite_eq_right]
      rintro ⟨a, ha, h1, h2, -⟩
      omega
    by_cases h : (k : ℕ) + 1 < n
    · have e1 := hstage (Fin.castLE hnm k) k (Or.inl (by simp))
      have e2 := hstage (Fin.castLE hnm ⟨k + 1, h⟩) ⟨k + 1, h⟩ (Or.inl (by simp))
      have e3 := hstage (Fin.castLE hnm k) ⟨k + 1, h⟩ (Or.inr (by simp))
      simp only [h, ↓reduceDIte, pure_bind, e1, e2, e3]
      split_ifs with hsm
      · have hsm' : IsSmallSuper hnm ε D k := ⟨h, hsm⟩
        ext r s
        rw [Id.run_pure, of_apply, svdDeflateStage_succ_apply]
        by_cases hp : (r : ℕ) = k ∧ (s : ℕ) = k + 1
        · rw [ite_eq_left (show r = Fin.castLE hnm k ∧ s = ⟨k + 1, h⟩ from
            ⟨Fin.ext hp.1, Fin.ext hp.2⟩), ite_eq_left ⟨hp.1, hp.2, hsm'⟩]
        · rw [ite_eq_right (fun h' => hp ⟨by rw [h'.1]; rfl, by rw [h'.2]⟩),
            ite_eq_right (fun h' => hp ⟨h'.1, h'.2.1⟩), hD']
      · have hsm' : ¬ IsSmallSuper hnm ε D k := fun ⟨_, h'⟩ => hsm h'
        rw [Id.run_pure, hD']
        ext r s
        rw [svdDeflateStage_succ_apply, ite_eq_right (fun h' => hsm' h'.2.2)]
    · simp only [h, ↓reduceDIte, Id.run_pure]
      rw [hD']
      ext r s
      rw [svdDeflateStage_succ_apply, ite_eq_right (fun h' => h h'.2.2.1)]

/-- The deflation keeps an array upper bidiagonal. -/
private theorem isUpperBidiagonalRect_svdDeflateStage (hnm : n ≤ m) (ε : ℝ)
    {D : Matrix (Fin m) (Fin n) ℝ} (hD : D.IsUpperBidiagonalRect) (k : ℕ) :
    (svdDeflateStage hnm ε D k).IsUpperBidiagonalRect := fun i j h1 h2 => by
  rw [svdDeflateStage_apply_of_ne hnm ε D h2]
  exact hD i j h1 h2

open Classical in
/-- The zero superdiagonal entries `b_{a,a+1} = 0` of an `m × n` array. -/
private noncomputable def zeroSupers (hnm : n ≤ m) (D : Matrix (Fin m) (Fin n) ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ h : (a : ℕ) + 1 < n, D (Fin.castLE hnm a) ⟨a + 1, h⟩ = 0

open Classical in
/-- The superdiagonal entries the deflation of Algorithm 8.6.2 newly sets to zero. -/
private noncomputable def newSupers (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => IsSmallSuper hnm ε D a ∧
    ∃ h : (a : ℕ) + 1 < n, D (Fin.castLE hnm a) ⟨a + 1, h⟩ ≠ 0

/-- There are at most `n - 1` superdiagonal entries. -/
private theorem card_zeroSupers_le (hnm : n ≤ m) (D : Matrix (Fin m) (Fin n) ℝ) :
    (zeroSupers hnm D).card ≤ n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (Finset.card_le_univ _).trans (by simp)
  have hsub : zeroSupers hnm D ⊆ Finset.univ.erase ⟨n - 1, by omega⟩ := fun a ha => by
    simp only [zeroSupers, Finset.mem_filter] at ha
    obtain ⟨-, h, -⟩ := ha
    refine Finset.mem_erase.2 ⟨fun e => ?_, Finset.mem_univ _⟩
    rw [e] at h
    simp at h
    omega
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- The deflation adds exactly the new zeros to the zero superdiagonal entries. -/
private theorem zeroSupers_svdDeflateStage (hnm : n ≤ m) (ε : ℝ)
    (D : Matrix (Fin m) (Fin n) ℝ) :
    (zeroSupers hnm (svdDeflateStage hnm ε D n)).card =
      (zeroSupers hnm D).card + (newSupers hnm ε D).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext a
    simp only [zeroSupers, newSupers, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h, h0⟩
      rw [svdDeflateStage_apply_super] at h0
      by_cases hs : IsSmallSuper hnm ε D a
      · by_cases hz : D (Fin.castLE hnm a) ⟨a + 1, h⟩ = 0
        · exact Or.inl ⟨h, hz⟩
        · exact Or.inr ⟨hs, h, hz⟩
      · rw [ite_eq_right hs] at h0
        exact Or.inl ⟨h, h0⟩
    · rintro (⟨h, h0⟩ | ⟨hs, h, -⟩)
      · refine ⟨h, ?_⟩
        rw [svdDeflateStage_apply_super]
        split_ifs
        · rfl
        · exact h0
      · exact ⟨h, by rw [svdDeflateStage_apply_super, ite_eq_left hs]⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [zeroSupers, newSupers, Finset.mem_filter] at ha hb
    obtain ⟨-, h, h0⟩ := ha
    obtain ⟨-, -, h', hne⟩ := hb
    exact hne h0

/-- The part of `D` on the superdiagonal entry `a`: the entry `(a, a + 1)`. -/
private def superPart (D : Matrix (Fin m) (Fin n) ℝ) (a : Fin n) : Matrix (Fin m) (Fin n) ℝ :=
  of fun r s => if (r : ℕ) = a ∧ (s : ℕ) = a + 1 then D r s else 0

/-- The deflation removes the superdiagonal parts of the new zeros. -/
private theorem sub_svdDeflateStage_eq_sum (hnm : n ≤ m) (ε : ℝ) (D : Matrix (Fin m) (Fin n) ℝ) :
    D - svdDeflateStage hnm ε D n = ∑ a ∈ newSupers hnm ε D, superPart D a := by
  classical
  ext r s
  rw [Matrix.sub_apply, Matrix.sum_apply]
  by_cases hrs : (s : ℕ) = r + 1
  swap
  · rw [svdDeflateStage_apply_of_ne hnm ε D hrs, sub_self]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [superPart, of_apply, ite_eq_right]
    rintro ⟨h1, h2⟩
    omega
  obtain ⟨c, hc, rfl, rfl⟩ : ∃ c : Fin n, ∃ hc : (c : ℕ) + 1 < n,
      r = Fin.castLE hnm c ∧ s = ⟨c + 1, hc⟩ :=
    ⟨⟨r, by omega⟩, by simp only; omega, Fin.ext rfl, Fin.ext hrs⟩
  have hsum : ∑ a ∈ newSupers hnm ε D, superPart D a (Fin.castLE hnm c) ⟨c + 1, hc⟩ =
      if c ∈ newSupers hnm ε D then D (Fin.castLE hnm c) ⟨c + 1, hc⟩ else 0 := by
    rw [← Finset.sum_ite_eq' (newSupers hnm ε D) c (fun _ => D (Fin.castLE hnm c) ⟨c + 1, hc⟩)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [superPart, of_apply]
    by_cases hac : a = c
    · subst hac
      rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl]
    · rw [ite_eq_right (fun h' => hac (Fin.ext h'.1.symm)), ite_eq_right hac]
  rw [hsum, svdDeflateStage_apply_super]
  have hmem : c ∈ newSupers hnm ε D ↔
      IsSmallSuper hnm ε D c ∧ D (Fin.castLE hnm c) ⟨c + 1, hc⟩ ≠ 0 := by
    simp only [newSupers, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hc, h2⟩⟩
  by_cases hsm : IsSmallSuper hnm ε D c
  · rw [ite_eq_left hsm, sub_zero]
    by_cases hz : D (Fin.castLE hnm c) ⟨c + 1, hc⟩ = 0
    · rw [ite_eq_right (fun h' => (hmem.1 h').2 hz), hz]
    · rw [ite_eq_left (hmem.2 ⟨hsm, hz⟩)]
  · rw [ite_eq_right hsm, sub_self, ite_eq_right (fun h' => hsm (hmem.1 h').1)]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- An entry of an `m × n` matrix is at most its Frobenius norm. -/
private theorem abs_apply_le_frobenius' (D : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    |D i j| ≤ ‖D‖ := by
  have h := frobenius_norm_sq_eq_sum_sq D
  have h1 : ‖D i j‖ ^ 2 ≤ ∑ j', ‖D i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖D i j'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ j', ‖D i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖D i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖D i' j'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)
  rw [← Real.norm_eq_abs]
  nlinarith [norm_nonneg (D i j), norm_nonneg D]

/-- The superdiagonal part of the entry `(a, a + 1)` has the norm of the entry. -/
private theorem norm_superPart_le (hnm : n ≤ m) (D : Matrix (Fin m) (Fin n) ℝ) (a : Fin n)
    (h : (a : ℕ) + 1 < n) : ‖superPart D a‖ ≤ |D (Fin.castLE hnm a) ⟨a + 1, h⟩| := by
  have hsq : ‖superPart D a‖ ^ 2 = |D (Fin.castLE hnm a) ⟨a + 1, h⟩| ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_sq, Finset.sum_eq_single (Fin.castLE hnm a)]
    · rw [Finset.sum_eq_single (⟨a + 1, h⟩ : Fin n)]
      · simp [superPart, Real.norm_eq_abs]
      · intro s _ hs
        rw [superPart, of_apply, ite_eq_right (fun h' => hs (Fin.ext h'.2))]
        simp
      · simp
    · intro r _ hr
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [superPart, of_apply, ite_eq_right (fun h' => hr (Fin.ext h'.1))]
      simp
    · simp
  exact ((pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 hsq).le

/-- **The deflation perturbation**: `‖D - deflated D‖_F ≤ 2 ε ‖D‖_F` per new zero. -/
private theorem norm_sub_svdDeflateStage_le (hnm : n ≤ m) {ε : ℝ} (hε : 0 ≤ ε)
    (D : Matrix (Fin m) (Fin n) ℝ) :
    ‖D - svdDeflateStage hnm ε D n‖ ≤ (newSupers hnm ε D).card * (2 * ε * ‖D‖) := by
  rw [sub_svdDeflateStage_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun a ha => ?_
  simp only [newSupers, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨⟨h, hsm⟩, -⟩ := ha
  refine (norm_superPart_le hnm D a h).trans ?_
  have h1 := abs_apply_le_frobenius' D (Fin.castLE hnm a) a
  have h2 := abs_apply_le_frobenius' D (Fin.castLE hnm ⟨a + 1, h⟩) ⟨a + 1, h⟩
  have hsm' : |D (Fin.castLE hnm a) ⟨a + 1, h⟩| ≤ ε * (|D (Fin.castLE hnm a) a| +
      |D (Fin.castLE hnm ⟨a + 1, h⟩) ⟨a + 1, h⟩|) := hsm
  nlinarith

/-- The loop invariant of Algorithm 8.6.2 on the state `(B, U, V, done)`: `U`, `V` are orthogonal,
`B` is upper bidiagonal, `Uᵀ (A + F) V = B` for an `F` (the deflations so far, carried back) of
norm at most `κ` per zero superdiagonal entry of `B` (when `κ` is large enough), and `B` is
diagonal once `done`. -/
private def SVDInv (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) (ε κ : ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Bool) : Prop :=
  st.2.1 ∈ orthogonalGroup (Fin m) ℝ ∧ st.2.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧
    st.1.IsUpperBidiagonalRect ∧
    (∃ F : Matrix (Fin m) (Fin n) ℝ, st.2.1ᵀ * (A + F) * st.2.2.1 = st.1 ∧
      (2 * ε * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F‖ ≤ κ * (zeroSupers hnm st.1).card)) ∧
    (st.2.2.2 = true → ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → st.1 i j = 0)

/-- The invariant after a step of Algorithm 8.6.2 on the window `[p, q)` of the deflated `D₁`
(Algorithm 8.6.1 or a zero-diagonal chase): a two-sided orthogonal transformation of `D₁` that
keeps it upper bidiagonal and changes only the block, whose superdiagonal is nonzero. -/
private theorem svdInv_window_step (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ} {ε κ : ℝ}
    (hκ0 : 0 ≤ κ) {p q : ℕ} {D₁ F₁ : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (hF₁ : Uᵀ * (A + F₁) * V = D₁)
    (hF₁n : 2 * ε * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F₁‖ ≤ κ * (zeroSupers hnm D₁).card)
    (hrun : ∀ (a : Fin n) (h : (a : ℕ) + 1 < n), p ≤ (a : ℕ) → (a : ℕ) + 1 < q →
      D₁ (Fin.castLE hnm a) ⟨a + 1, h⟩ ≠ 0)
    {M : Id (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ)}
    (hr : ∃ G ∈ orthogonalGroup (Fin m) ℝ, ∃ H ∈ orthogonalGroup (Fin n) ℝ,
      (Id.run M).1 = Gᵀ * D₁ * H ∧ (Id.run M).2.1 = U * G ∧ (Id.run M).2.2 = V * H ∧
      (Id.run M).1.IsUpperBidiagonalRect ∧ AgreeOff p q (Id.run M).1 D₁) :
    SVDInv hnm A ε κ (do let r ← M; pure (r.1, r.2.1, r.2.2, false) :
      Id (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ ×
        Bool)) := by
  change SVDInv hnm A ε κ ((Id.run M).1, (Id.run M).2.1, (Id.run M).2.2, false)
  set r := Id.run M
  obtain ⟨G, hG, H, hH, h1, h2, h3, hb, ha⟩ := hr
  have hzero : (zeroSupers hnm D₁).card ≤ (zeroSupers hnm r.1).card := by
    refine Finset.card_le_card fun a ha' => ?_
    simp only [zeroSupers, Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢
    obtain ⟨h, h0⟩ := ha'
    refine ⟨h, ?_⟩
    rw [ha _ _ fun hin => hrun a h hin.1.1 hin.2.2 h0]
    exact h0
  refine ⟨?_, ?_, hb, ⟨F₁, ?_, fun hκ => ?_⟩, fun h => absurd h (by simp)⟩
  · dsimp only
    rw [h2]
    exact Submonoid.mul_mem _ hU hG
  · dsimp only
    rw [h3]
    exact Submonoid.mul_mem _ hV hH
  · dsimp only
    rw [h1, h2, h3, ← hF₁, transpose_mul]
    simp only [Matrix.mul_assoc]
  · exact (hF₁n hκ).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hzero) hκ0)

/-- **One pass of Algorithm 8.6.2 keeps the invariant.** -/
private theorem svdPass_inv (hnm : n ≤ m) {A : Matrix (Fin m) (Fin n) ℝ} {ε κ : ℝ} (hε : 0 ≤ ε)
    (hκ0 : 0 ≤ κ)
    {st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool}
    (h : SVDInv hnm A ε κ st) : SVDInv hnm A ε κ (Id.run (svdPass pure hnm ε st)) := by
  obtain ⟨D, U, V, done⟩ := st
  obtain ⟨hU, hV, hDb, ⟨F, hF, hFn⟩, hdone⟩ := h
  dsimp only at hU hV hDb hF hFn hdone
  cases done with
  | true => exact ⟨hU, hV, hDb, ⟨F, hF, hFn⟩, hdone⟩
  | false =>
  unfold svdPass
  simp only [Bool.false_eq_true, ↓reduceIte, Id.run_bind, svdDeflate_pure]
  set D₁ := svdDeflateStage hnm ε D n with hD₁
  have hD₁b : D₁.IsUpperBidiagonalRect := isUpperBidiagonalRect_svdDeflateStage hnm ε hDb n
  have hUt : Uᵀ ∈ orthogonalGroup (Fin m) ℝ := by
    refine (mem_orthogonalGroup_iff' _ ℝ).2 ?_
    rw [transpose_transpose]
    exact (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hVt : Vᵀ ∈ orthogonalGroup (Fin n) ℝ := by
    refine (mem_orthogonalGroup_iff' _ ℝ).2 ?_
    rw [transpose_transpose]
    exact (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hUU : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU
  -- the deflation, carried back
  set F₁ := F - U * (D - D₁) * Vᵀ with hF₁
  have hF₁eq : Uᵀ * (A + F₁) * V = D₁ := by
    have e : A + F₁ = (A + F) - U * (D - D₁) * Vᵀ := by rw [hF₁]; abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul, hF]
    simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ ℝ).1 hV, Matrix.mul_one]
    abel
  have hF₁n : 2 * ε * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F₁‖ ≤ κ * (zeroSupers hnm D₁).card := by
    intro hκ
    have hFb := hFn hκ
    have hz := card_zeroSupers_le hnm D
    have hDn : ‖D‖ ≤ ‖A‖ + κ * (n - 1 : ℕ) := by
      rw [← hF, frobenius_norm_unitary_mul_mul_unitary hUt (A + F) hV]
      have h1 := hFb.trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.2 hz : ((zeroSupers hnm D).card : ℝ) ≤ ((n - 1 : ℕ) : ℝ)) hκ0)
      linarith [norm_add_le A F]
    have hconj : ‖U * (D - D₁) * Vᵀ‖ = ‖D - D₁‖ :=
      frobenius_norm_unitary_mul_mul_unitary hU (D - D₁) hVt
    have he := norm_sub_svdDeflateStage_le hnm hε D
    rw [hD₁, zeroSupers_svdDeflateStage, Nat.cast_add]
    calc ‖F₁‖ ≤ ‖F‖ + ‖U * (D - D₁) * Vᵀ‖ := norm_sub_le _ _
      _ ≤ κ * (zeroSupers hnm D).card + (newSupers hnm ε D).card * (2 * ε * ‖D‖) := by
          rw [hconj]; exact add_le_add hFb he
      _ ≤ κ * (zeroSupers hnm D).card + (newSupers hnm ε D).card * κ := by
          gcongr
          nlinarith
      _ = κ * ((zeroSupers hnm D).card + (newSupers hnm ε D).card) := by ring
  -- the window of `B₂₂`
  have hspec := lastRunWindow_spec (n := n)
    (nz := fun i => ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0)
    (fun i ⟨h, _⟩ => h)
  have hwin : bidiagonalWindow hnm D₁ = lastRunWindow n
      (fun i => ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0) := rfl
  split
  · -- `q = n`: `D₁` is diagonal
    rename_i hw
    refine ⟨hU, hV, hD₁b, ⟨F₁, hF₁eq, hF₁n⟩, fun _ i j hij => ?_⟩
    change D₁ i j = 0
    have hnz : ∀ i, ¬ ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0 := by
      rcases hspec with ⟨-, hno⟩ | ⟨p, e, hpe, he, hw', -⟩
      · exact hno
      · rw [← hwin, hw] at hw'
        have : (⟨p, by omega⟩ : Fin n) ∈ Chapter07.francisWindow n p (e + 2) :=
          Chapter07.mem_francisWindow.2 ⟨le_rfl, show p < e + 2 by omega⟩
        rw [← hw'] at this
        exact absurd this List.not_mem_nil
    by_contra h0
    by_cases hj : (j : ℕ) = i + 1
    · have hj' : j = ⟨i + 1, by omega⟩ := Fin.ext hj
      rw [hj'] at h0
      exact hnz i ⟨by omega, h0⟩
    · exact h0 (hD₁b i j (fun h => hij h.symm) hj)
  · -- `q < n`: a step on the window
    rename_i hne
    obtain ⟨p, e, hpe, he, hw', hrun, hbefore, hafter⟩ : ∃ p e : ℕ, p ≤ e ∧ e + 1 < n ∧
        bidiagonalWindow hnm D₁ = Chapter07.francisWindow n p (e + 2) ∧
        (∀ i, p ≤ i → i ≤ e →
          ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0) ∧
        (0 < p → ¬ ∃ h : p - 1 + 1 < n,
          D₁ (Fin.castLE hnm ⟨p - 1, by omega⟩) ⟨p - 1 + 1, h⟩ ≠ 0) ∧
        ∀ i, e < i → ¬ ∃ h : i + 1 < n, D₁ (Fin.castLE hnm ⟨i, by omega⟩) ⟨i + 1, h⟩ ≠ 0 := by
      rcases hspec with ⟨hw0, -⟩ | ⟨p, e, hpe, he, hw', h1, h2, h3⟩
      · exact absurd (hwin.trans hw0) hne
      · exact ⟨p, e, hpe, he, hwin.trans hw', h1, h2, h3⟩
    -- `D₁` is decoupled along the window
    have hDd : IsDecoupledAt p (e + 2) D₁ := by
      intro r s hrs
      by_contra h0
      by_cases hsr : (s : ℕ) = r + 1
      · rcases hrs with ⟨hr, hs⟩ | ⟨hr, hs⟩
        · have he1 : e + 1 < n := by omega
          have he2 : e + 1 + 1 < n := by omega
          have hr' : r = Fin.castLE hnm ⟨e + 1, he1⟩ :=
            Fin.ext (by simp only [Fin.val_castLE]; omega)
          have hs' : s = ⟨e + 1 + 1, he2⟩ := Fin.ext (by simp only; omega)
          subst hr' hs'
          exact hafter (e + 1) (by omega) ⟨_, h0⟩
        · have hp : 0 < p := by omega
          have hp1 : p - 1 < n := by omega
          have hp2 : p - 1 + 1 < n := by omega
          have hr' : r = Fin.castLE hnm ⟨p - 1, hp1⟩ :=
            Fin.ext (by simp only [Fin.val_castLE]; omega)
          have hs' : s = ⟨p - 1 + 1, hp2⟩ := Fin.ext (by simp only; omega)
          subst hr' hs'
          exact hbefore hp ⟨_, h0⟩
      · refine h0 (hD₁b r s (fun h => ?_) hsr)
        rcases hrs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have hrun' : ∀ (a : Fin n) (h : (a : ℕ) + 1 < n), p ≤ (a : ℕ) → (a : ℕ) + 1 < e + 2 →
        D₁ (Fin.castLE hnm a) ⟨a + 1, h⟩ ≠ 0 := fun a h hpa hae => by
      obtain ⟨_, hne0⟩ := hrun a hpa (by omega)
      exact hne0
    have he2 : e + 2 ≤ n := by omega
    rw [hw']
    split
    · rename_i k hk
      have hkw := Chapter07.mem_francisWindow.1 (List.mem_of_find?_eq_some hk)
      have hkk : D₁ (Fin.castLE hnm k) k = 0 := by simpa using List.find?_some hk
      exact svdInv_window_step hnm hκ0 hU hV hF₁eq hF₁n hrun'
        (zeroDiagonalChase_window hnm he2 (by omega) hD₁b hDd hkw hkk U V)
    · exact svdInv_window_step hnm hκ0 hU hV hF₁eq hF₁n hrun'
        (algorithm_8_6_1_window hnm he2 (by omega) hD₁b hDd U V)

/-- **Exact semantics of Algorithm 8.6.2** (the SVD algorithm: "overwrites `A` with
`UᵀAV = D + E`, where `U`, `V` are orthogonal, `D` is diagonal, and `E` satisfies
`‖E‖₂ ≈ u‖A‖₂`"), in exact arithmetic with the deflation tolerance `ε ≥ 0`: for
`A ∈ ℝ^{m×n}`, `m ≥ n`, and any `fuel`, the run `(B, U, V, done)` has `U`, `V` orthogonal, `B`
upper bidiagonal (`m × n`, zero below row `n`), and `B = Uᵀ (A + E) V` for an `E` (the
deflations `b_{i,i+1} := 0`, carried back to `A`) with `‖E‖_F ≤ c ε ‖A‖_F / (1 - c ε)` for
`c = 2 (n - 1)` whenever `c ε < 1`; and if the loop stopped on its test (`done`, `q = n`) within
the fuel, `B` is diagonal. Each deflation zeroes an entry `|b_{i,i+1}| ≤ ε (|b_ii| + |b_{i+1,i+1}|)`
of the current `B`, of size `≤ 2 ε ‖B‖_F ≤ 2 ε (‖A‖_F + ‖E‖_F)`, and a zeroed superdiagonal entry
stays zero (the steps of Algorithm 8.6.1 and the zero-diagonal chases act on the unreduced block
`B₂₂` only), so there are at most `n - 1` of them. The forward form `Uᵀ A V = B + E` with `E`
supported on the deflated positions is false, as for `algorithm_8_3_3_spec`: a later rotation on a
window `[p, …]` mixes a deflated entry `b_{p-1,p}` into `b_{p-1,p+1}`. Convergence (that some
finite fuel suffices) is not claimed. -/
theorem algorithm_8_6_2_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (fuel : ℕ) :
    let out := Id.run (algorithm_8_6_2 pure hnm ε A fuel)
    out.2.1 ∈ orthogonalGroup (Fin m) ℝ ∧ out.2.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧
      out.1.IsUpperBidiagonalRect ∧
      (∃ E : Matrix (Fin m) (Fin n) ℝ, out.2.1ᵀ * (A + E) * out.2.2.1 = out.1 ∧
        (2 * ((n - 1 : ℕ) : ℝ) * ε < 1 →
          ‖E‖ ≤ 2 * ((n - 1 : ℕ) : ℝ) * ε * ‖A‖ / (1 - 2 * ((n - 1 : ℕ) : ℝ) * ε))) ∧
      (out.2.2.2 = true → ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → out.1 i j = 0) := by
  intro out
  set c : ℝ := 2 * ((n - 1 : ℕ) : ℝ) * ε with hc
  set κ : ℝ := if c < 1 then 2 * ε * ‖A‖ / (1 - c) else 0 with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    split_ifs with h
    · exact div_nonneg (by positivity) (by linarith)
    · exact le_rfl
  -- the initial state: chapter 5's bidiagonalization
  obtain ⟨hbid, -, -⟩ := Chapter05.algorithm_5_4_2_spec hnm A
  have h0 : SVDInv hnm A ε κ
      (Chapter05.bidiagonalPart (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).1,
        Id.run (Chapter05.forwardAccumulation pure (Chapter05.storedReflectors
          (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).1
          (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).2.1)),
        Id.run (Chapter05.forwardAccumulation pure (List.ofFn fun k =>
          (Chapter05.storedRowVec hnm (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).1 k,
            (Id.run (Chapter05.algorithm_5_4_2 pure hnm A)).2.2 k))),
        false) := by
    rw [Chapter05.forwardAccumulation_spec, Chapter05.forwardAccumulation_spec]
    refine ⟨hbid.left_mem_unitaryGroup, hbid.right_mem_unitaryGroup, hbid.isUpperBidiagonalRect,
      ⟨0, ?_, fun _ => ?_⟩, fun h => absurd h (by simp)⟩
    · rw [add_zero, ← conjTranspose_eq_transpose_of_trivial]
      exact hbid.conj_eq
    · rw [norm_zero]
      exact mul_nonneg hκ0 (Nat.cast_nonneg _)
  have key : SVDInv hnm A ε κ out :=
    idRun_foldlM_induction (List.range fuel) (fun _ st => SVDInv hnm A ε κ st) _ h0
      (fun _ _ _ h => svdPass_inv hnm hε hκ0 h)
  obtain ⟨hU, hV, hb, ⟨F, hF, hFn⟩, hdone⟩ := key
  refine ⟨hU, hV, hb, ⟨F, hF, fun hc1 => ?_⟩, hdone⟩
  have hκ : κ = 2 * ε * ‖A‖ / (1 - c) := by rw [hκdef, ite_eq_left hc1]
  have h1c : 0 < 1 - c := by linarith
  have hκeq : 2 * ε * (‖A‖ + κ * (n - 1 : ℕ)) = κ := by
    rw [hκ]
    field_simp
    rw [hc]
    ring
  have hF' := hFn hκeq.le
  have hz := card_zeroSupers_le hnm out.1
  calc ‖F‖ ≤ κ * (zeroSupers hnm out.1).card := hF'
    _ ≤ κ * (n - 1 : ℕ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hz) hκ0
    _ = c * ‖A‖ / (1 - c) := by rw [hκ, hc]; field_simp
    _ = _ := by rw [hc]

end Frobenius

end SVDAlgorithm

end GolubVanLoan.Chapter08
