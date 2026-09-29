import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.Kronecker.Spectral
import Numlib.LinearAlgebra.Matrix.KroneckerApprox
import Numlib.LinearAlgebra.Matrix.QR
import NumlibSurface.GolubVanLoan.Chapter01.Section03

/-!
# Golub–Van Loan §12.3: Kronecker product computations

Surface file for §12.3 of Golub and Van Loan, *Matrix Computations* (4th edition): the properties
of the Kronecker product listed in §12.3.1 ((12.3.1)–(12.3.4) and the unnumbered facts), the
Tracy–Singh product (12.3.5)–(12.3.8), the Hadamard and Khatri–Rao products (§12.3.3), `vec` and
`reshape` (12.3.9)–(12.3.11), `vec` and perfect shuffles (12.3.12) with the two-pass transposition
of §12.3.5, the Kronecker product SVD and nearest Kronecker products (12.3.14)–(12.3.19) with
Theorem 12.3.1, the nearest `X ⊗ X` and `X ⊗ Y − Y ⊗ X` problems with Lemmas 12.3.2–12.3.3 and
(12.3.20)–(12.3.21), and the reshaping identity of §12.3.10.

## Design

Where the book's positional layout matters (perfect shuffles, `vec`, `reshape`, the rearrangement
`𝓡`), matrices live on `Fin` and the Kronecker product is chapter 1's `Matrix.kroneckerFin` (block
`(i, j)` is `b_ij C`, row `(i₁, i₂)` at position `i₂ + m₂ i₁`); `vec` is `Matrix.vecFin`, and the
book's `reshape(a, m, n)` of a vector is `reshapeVec a`. Statements that do not depend on the layout
use Mathlib's typed `B ⊗ₖ C` on product index types. The four basic identities of §12.3.1
(transpose, inverse, product, associativity) are chapter 1's (1.3.1)–(1.3.4) and are not restated.

The rearrangement `𝓡(A)` of an `m₁ m₂ × n₁ n₂` matrix blocked as (12.3.16) is `rearrangement A`, the
backbone's typed `Matrix.kroneckerRearrange` read through `finProdFinEquiv`: row `(j − 1) m₁ + i` is
`vec(A_{ij})ᵀ`. It permutes entries, so every nearest-Kronecker-product problem is a nearest
low-rank problem for `𝓡(A)`.

Lemma 12.3.2 and §12.3.8 are stated for an arbitrary Schur decomposition `Qᵀ T Q = diag(α)` of the
symmetric part `T = (M + Mᵀ)/2` (`Matrix.hermitianPart M` over `ℝ`), as the book does.

## Not formalized here

§12.3.7 (constrained nearest Kronecker products: the positive definiteness and nonnegativity of
`B_opt`, `C_opt` are cited without proof, the Toeplitz-constrained reduction is a method sketch),
the memory-hierarchy discussion of multipass transposition beyond the two-pass identity, the small
numerical examples, and all operation counts.
-/

open Matrix
open scoped Kronecker

namespace GolubVanLoan.Chapter12

variable {m₁ n₁ m₂ n₂ : ℕ}

/-! ### §12.3.1: basic properties -/

/-- **(12.3.1)**: `𝒫_{m₁,m₂} (B ⊗ C) 𝒫_{n₁,n₂}ᵀ = C ⊗ B` for `B ∈ ℝ^{m₁×n₁}`, `C ∈ ℝ^{m₂×n₂}` —
chapter 1's (1.3.5). -/
theorem equation_12_3_1 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    perfectShuffle m₁ m₂ * kroneckerFin B C *
        (perfectShuffle n₁ n₂ : Matrix (Fin (n₂ * n₁)) (Fin (n₁ * n₂)) ℝ)ᵀ =
      kroneckerFin C B :=
  Chapter01.equation_1_3_5 B C

/-- The row permutation `w` of (12.3.2): `(i, j) ↦ (p i, q j)` in the positional layout. -/
def kroneckerPermIndex {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m * n)) :=
  finProdFinEquiv.symm.trans ((p.prodCongr q).trans finProdFinEquiv)

/-- **(12.3.2)**: for permutations `p` of `1:m` and `q` of `1:n`, `I_m(p, :) ⊗ I_n(q, :) = I_{mn}(w,
:)` with `w = (1_m ⊗ q) + n · (p − 1_m) ⊗ 1_n`, i.e. (0-based) `w((i − 1) n + j) = q_j + n p_i`; in
particular the Kronecker product of two permutation matrices is a permutation matrix. -/
theorem equation_12_3_2 {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n)) :
    kroneckerFin ((1 : Matrix (Fin m) (Fin m) ℝ).submatrix p id)
        ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix q id) =
      (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ).submatrix (kroneckerPermIndex p q) id ∧
    ∀ i j, (kroneckerPermIndex p q (finProdFinEquiv (i, j)) : ℕ) = q j + n * p i := by
  refine ⟨?_, fun i j => by simp [kroneckerPermIndex, finProdFinEquiv_apply_val]⟩
  ext I J
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective J
  simp only [kroneckerFin_apply, submatrix_apply, id, one_apply, kroneckerPermIndex,
    Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  rw [ite_zero_mul_ite_zero, one_mul]

/-- **§12.3.1**, structure preserved by the Kronecker product: (orthogonal) ⊗ (orthogonal) =
(orthogonal), (stochastic) ⊗ (stochastic) = (stochastic), (sym. pos. def.) ⊗ (sym. pos. def.) =
(sym. pos. def.), and `B = G_B G_Bᵀ`, `C = G_C G_Cᵀ ⇒ B ⊗ C = (G_B ⊗ G_C)(G_B ⊗ G_C)ᵀ`. -/
theorem kronecker_structure_preserved {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    (B ∈ orthogonalGroup (Fin m) ℝ → C ∈ orthogonalGroup (Fin n) ℝ →
      B ⊗ₖ C ∈ orthogonalGroup (Fin m × Fin n) ℝ) ∧
    (B ∈ rowStochastic ℝ (Fin m) → C ∈ rowStochastic ℝ (Fin n) →
      B ⊗ₖ C ∈ rowStochastic ℝ (Fin m × Fin n)) ∧
    (B.PosDef → C.PosDef → (B ⊗ₖ C).PosDef) ∧
    ∀ G_B G_C : Matrix _ _ ℝ, B = G_B * G_Bᵀ → C = G_C * G_Cᵀ →
      B ⊗ₖ C = (G_B ⊗ₖ G_C) * (G_B ⊗ₖ G_C)ᵀ :=
  ⟨fun hB hC => kronecker_mem_unitary hB hC, kronecker_mem_rowStochastic, PosDef.kronecker,
    fun G_B G_C hB hC => by rw [hB, hC, mul_kronecker_mul, kroneckerMap_transpose]⟩

/-- The positional Kronecker product of orthogonal matrices is orthogonal. -/
theorem kroneckerFin_mem_orthogonalGroup {m n : ℕ} {Q₁ : Matrix (Fin m) (Fin m) ℝ}
    {Q₂ : Matrix (Fin n) (Fin n) ℝ} (h₁ : Q₁ ∈ orthogonalGroup (Fin m) ℝ)
    (h₂ : Q₂ ∈ orthogonalGroup (Fin n) ℝ) :
    kroneckerFin Q₁ Q₂ ∈ orthogonalGroup (Fin (m * n)) ℝ := by
  rw [mem_orthogonalGroup_iff] at h₁ h₂ ⊢
  rw [transpose_kroneckerFin, kroneckerFin_mul_kroneckerFin, h₁, h₂, kroneckerFin_one_one]

/-- **§12.3.1**, factorizations of a Kronecker product: the Cholesky factor of `B ⊗ C` is the
Kronecker product of the Cholesky factors; `P_B B = L_B U_B`, `P_C C = L_C U_C` give the LU
factorization `(P_B ⊗ P_C)(B ⊗ C) = (L_B ⊗ L_C)(U_B ⊗ U_C)`; square QR factorizations `B = Q_B R_B`,
`C = Q_C R_C` give the QR factorization `B ⊗ C = (Q_B ⊗ Q_C)(R_B ⊗ R_C)`; and thin (pivoted) QR
factorizations `B P_B = Q_B R_B`, `C P_C = Q_C R_C` give the thin QR factorization
`(B ⊗ C)(P_B ⊗ P_C) = (Q_B ⊗ Q_C)(R_B ⊗ R_C)`. All in the book's positional layout. -/
theorem kronecker_factorizations {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    (∀ H_B H_C, IsCholesky B H_B → IsCholesky C H_C →
      IsCholesky (kroneckerFin B C) (kroneckerFin H_B H_C)) ∧
    (∀ P_B L_B U_B P_C L_C U_C, IsLU (P_B * B) L_B U_B → IsLU (P_C * C) L_C U_C →
      IsLU (kroneckerFin P_B P_C * kroneckerFin B C) (kroneckerFin L_B L_C)
        (kroneckerFin U_B U_C)) ∧
    (∀ Q_B R_B Q_C R_C, IsQR B Q_B R_B → IsQR C Q_C R_C →
      IsQR (kroneckerFin B C) (kroneckerFin Q_B Q_C) (kroneckerFin R_B R_C)) := by
  refine ⟨fun _ _ hB hC => hB.kroneckerFin hC, fun P_B L_B U_B P_C L_C U_C hB hC => ?_,
    fun Q_B R_B Q_C R_C hB hC => ?_⟩
  · rw [kroneckerFin_mul_kroneckerFin]
    exact hB.kroneckerFin hC
  · have hRB : R_B.IsUpperTriangular := fun i j h => hB.apply_eq_zero i j h
    have hRC : R_C.IsUpperTriangular := fun i j h => hC.apply_eq_zero i j h
    refine ⟨kroneckerFin_mem_orthogonalGroup hB.mem_unitaryGroup hC.mem_unitaryGroup,
      fun i j h => (hRB.kroneckerFin hRC) h, ?_⟩
    rw [kroneckerFin_mul_kroneckerFin, hB.mul_eq, hC.mul_eq]

/-- **§12.3.1**, the thin pivoted QR factorization of a Kronecker product: if `B P_B = Q_B R_B` and
`C P_C = Q_C R_C` with `Q_B`, `Q_C` having orthonormal columns and `R_B`, `R_C` upper triangular,
then `(B ⊗ C)(P_B ⊗ P_C) = (Q_B ⊗ Q_C)(R_B ⊗ R_C)`, `Q_B ⊗ Q_C` has orthonormal columns and `R_B ⊗
R_C` is upper triangular. (The remark that rectangular `R` factors need row permutations to become
triangular is prose.) -/
theorem kronecker_thin_qr {m₁ n₁ m₂ n₂ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) (P_B : Equiv.Perm (Fin n₁)) (P_C : Equiv.Perm (Fin n₂))
    (Q_B : Matrix (Fin m₁) (Fin n₁) ℝ) (R_B : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Q_C : Matrix (Fin m₂) (Fin n₂) ℝ) (R_C : Matrix (Fin n₂) (Fin n₂) ℝ)
    (hB : B * P_B.permMatrix ℝ = Q_B * R_B) (hC : C * P_C.permMatrix ℝ = Q_C * R_C)
    (hQB : Q_Bᵀ * Q_B = 1) (hQC : Q_Cᵀ * Q_C = 1) (hRB : R_B.IsUpperTriangular)
    (hRC : R_C.IsUpperTriangular) :
    kroneckerFin B C * kroneckerFin (P_B.permMatrix ℝ) (P_C.permMatrix ℝ) =
        kroneckerFin Q_B Q_C * kroneckerFin R_B R_C ∧
      (kroneckerFin Q_B Q_C)ᵀ * kroneckerFin Q_B Q_C = 1 ∧
      (kroneckerFin R_B R_C).IsUpperTriangular := by
  refine ⟨?_, ?_, hRB.kroneckerFin hRC⟩
  · rw [kroneckerFin_mul_kroneckerFin, kroneckerFin_mul_kroneckerFin, hB, hC]
  · rw [transpose_kroneckerFin, kroneckerFin_mul_kroneckerFin, hQB, hQC, kroneckerFin_one_one]

/-- **(12.3.3)** and the display before it: Schur decompositions `Q_Bᴴ B Q_B = T_B`, `Q_Cᴴ C Q_C =
T_C` give `(Q_B ⊗ Q_C)ᴴ (B ⊗ C)(Q_B ⊗ Q_C) = T_B ⊗ T_C`, upper triangular when `T_B` and `T_C` are;
hence `λ(B ⊗ C) = {β_i γ_j}`: if the characteristic polynomials of `B` and `C` split as `∏ (x −
β_i)` and `∏ (x − γ_j)`, that of `B ⊗ C` is `∏_{i,j} (x − β_i γ_j)`. -/
theorem equation_12_3_3 {m n : ℕ} (B Q_B T_B : Matrix (Fin m) (Fin m) ℂ)
    (C Q_C T_C : Matrix (Fin n) (Fin n) ℂ) (hB : Q_Bᴴ * B * Q_B = T_B)
    (hC : Q_Cᴴ * C * Q_C = T_C) :
    (kroneckerFin Q_B Q_C)ᴴ * kroneckerFin B C * kroneckerFin Q_B Q_C = kroneckerFin T_B T_C ∧
      (T_B.IsUpperTriangular → T_C.IsUpperTriangular →
        (kroneckerFin T_B T_C).IsUpperTriangular) ∧
      ∀ (β : Fin m → ℂ) (γ : Fin n → ℂ),
        B.charpoly = ∏ i, (Polynomial.X - Polynomial.C (β i)) →
        C.charpoly = ∏ j, (Polynomial.X - Polynomial.C (γ j)) →
        (B ⊗ₖ C).charpoly = ∏ i, ∏ j, (Polynomial.X - Polynomial.C (β i * γ j)) := by
  refine ⟨?_, fun h₁ h₂ => h₁.kroneckerFin h₂, fun β γ h₁ h₂ => charpoly_kronecker B C h₁ h₂⟩
  rw [conjTranspose_kroneckerFin, kroneckerFin_mul_kroneckerFin, kroneckerFin_mul_kroneckerFin,
    hB, hC]

/-- **(12.3.4)** and the display before (12.3.3): SVDs `U_Bᵀ B V_B = S_B`, `U_Cᵀ C V_C = S_C` give
`(U_B ⊗ U_C)ᵀ (B ⊗ C)(V_B ⊗ V_C) = S_B ⊗ S_C`; hence `σ(B ⊗ C) = {β_i γ_j}`: the singular values of
`B ⊗ C` are the products of those of `B` and `C`, up to a relabelling. -/
theorem equation_12_3_4 {m₁ n₁ m₂ n₂ : ℕ} (U_B : Matrix (Fin m₁) (Fin m₁) ℝ)
    (V_B : Matrix (Fin n₁) (Fin n₁) ℝ) (U_C : Matrix (Fin m₂) (Fin m₂) ℝ)
    (V_C : Matrix (Fin n₂) (Fin n₂) ℝ) (Bᵣ : Matrix (Fin m₁) (Fin n₁) ℝ)
    (Cᵣ : Matrix (Fin m₂) (Fin n₂) ℝ) (S_B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (S_C : Matrix (Fin m₂) (Fin n₂) ℝ) (hB : U_Bᵀ * Bᵣ * V_B = S_B)
    (hC : U_Cᵀ * Cᵣ * V_C = S_C) :
    (U_B ⊗ₖ U_C)ᵀ * (Bᵣ ⊗ₖ Cᵣ) * (V_B ⊗ₖ V_C) = S_B ⊗ₖ S_C ∧
      ∃ e : Fin n₁ × Fin n₂ ≃ Fin n₁ × Fin n₂, ∀ q,
        (Bᵣ ⊗ₖ Cᵣ).colSingularValues (e q) =
          Bᵣ.colSingularValues q.1 * Cᵣ.colSingularValues q.2 := by
  refine ⟨?_, colSingularValues_kronecker Bᵣ Cᵣ⟩
  rw [← kroneckerMap_transpose, ← mul_kronecker_mul, ← mul_kronecker_mul, hB, hC]

/-- **§12.3.1**, after (12.3.4): `B y = β y`, `C z = γ z ⇒ (B ⊗ C)(y ⊗ z) = βγ (y ⊗ z)`;
`rank(B ⊗ C) = rank(B) rank(C)`; `det(B ⊗ C) = det(B)ⁿ det(C)ᵐ` for `B ∈ ℝ^{m×m}`, `C ∈ ℝ^{n×n}`;
`tr(B ⊗ C) = tr(B) tr(C)`. -/
theorem kronecker_invariants {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (y : Fin m → ℝ) (z : Fin n → ℝ) (β γ : ℝ), B *ᵥ y = β • y → C *ᵥ z = γ • z →
      (B ⊗ₖ C) *ᵥ kroneckerVec y z = (β * γ) • kroneckerVec y z) ∧
    (B ⊗ₖ C).rank = B.rank * C.rank ∧
    (B ⊗ₖ C).det = B.det ^ n * C.det ^ m ∧
    (B ⊗ₖ C).trace = B.trace * C.trace := by
  refine ⟨fun y z β γ hy hz => ?_, rank_kronecker B C, ?_, trace_kronecker B C⟩
  · rw [kronecker_mulVec, hy, hz, kroneckerVec_smul_left, kroneckerVec_smul_right, smul_smul]
  · rw [det_kronecker, Fintype.card_fin, Fintype.card_fin]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§12.3.1**: `‖B ⊗ C‖_F = ‖B‖_F ‖C‖_F`. -/
theorem kronecker_frobenius_norm {m₁ n₁ m₂ n₂ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) : ‖B ⊗ₖ C‖ = ‖B‖ * ‖C‖ :=
  frobenius_norm_kronecker B C

end Frobenius

section L2

open scoped Matrix.Norms.L2Operator

/-- **§12.3.1**: `‖B ⊗ C‖₂ = ‖B‖₂ ‖C‖₂`. -/
theorem kronecker_l2_norm {m₁ n₁ m₂ n₂ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) : ‖B ⊗ₖ C‖ = ‖B‖ * ‖C‖ :=
  l2_opNorm_kronecker B C

end L2

/-! ### The Tracy–Singh, Hadamard and Khatri–Rao products (§12.3.2–12.3.3) -/

section TracySingh

variable {M₁ N₁ M₂ N₂ : ℕ}

/-- The row layout of the Tracy–Singh product: block row `I₁`, then block row `I₂`, then the
Kronecker row `(i₁, i₂)`, each pair big-endian. -/
def tracySinghIndex (M₁ M₂ m₁ m₂ : ℕ) :
    (Fin M₁ × Fin M₂) × (Fin m₁ × Fin m₂) ≃ Fin (M₁ * M₂ * (m₁ * m₂)) :=
  (finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- **§12.3.2**, the Tracy–Singh product `B ⊗_TS C` of the block matrices (12.3.5) —
`B ∈ ℝ^{M₁m₁ × N₁n₁}` with `M₁ × N₁` blocks `B_ij ∈ ℝ^{m₁×n₁}` and `C ∈ ℝ^{M₂m₂ × N₂n₂}` with `M₂ ×
N₂` blocks `C_kl ∈ ℝ^{m₂×n₂}`, blocks laid out as `finProdFinEquiv` (block index slow) — in the
book's layout: the `M₁ × N₁` block matrix whose `(i, j)` block is `[B_ij ⊗ C_kl]_{k,l}`. It is the
backbone's typed `Matrix.tracySingh` read through `tracySinghIndex`. -/
def tracySinghFin (B : Matrix (Fin (M₁ * m₁)) (Fin (N₁ * n₁)) ℝ)
    (C : Matrix (Fin (M₂ * m₂)) (Fin (N₂ * n₂)) ℝ) :
    Matrix (Fin (M₁ * M₂ * (m₁ * m₂))) (Fin (N₁ * N₂ * (n₁ * n₂))) ℝ :=
  (tracySingh (B.submatrix finProdFinEquiv finProdFinEquiv)
    (C.submatrix finProdFinEquiv finProdFinEquiv)).reindex (tracySinghIndex M₁ M₂ m₁ m₂)
      (tracySinghIndex N₁ N₂ n₁ n₂)

/-- The position of the Kronecker row `((I₁, i₁), (I₂, i₂))` of `B ⊗ C`. -/
def kroneckerBlockIndex (M₁ M₂ m₁ m₂ : ℕ) :
    (Fin M₁ × Fin M₂) × (Fin m₁ × Fin m₂) ≃ Fin (M₁ * m₁ * (M₂ * m₂)) :=
  (Equiv.prodProdProdComm _ _ _ _).trans
    ((finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv)

/-- **(12.3.5)–(12.3.6)**: the Tracy–Singh product is a row and column permutation of the Kronecker
product, `B ⊗_TS C = P (B ⊗ C) Qᵀ` with `P`, `Q` the permutation matrices of the equivalences
`kroneckerBlockIndex ∘ (tracySinghIndex)⁻¹` (matrices of `Fin`-equivalences, as chapter 1's perfect
shuffle; `Matrix.tracySingh_eq_reindex_kronecker`). -/
theorem equation_12_3_6 (B : Matrix (Fin (M₁ * m₁)) (Fin (N₁ * n₁)) ℝ)
    (C : Matrix (Fin (M₂ * m₂)) (Fin (N₂ * n₂)) ℝ) :
    tracySinghFin B C =
      ((tracySinghIndex M₁ M₂ m₁ m₂).symm.trans
          (kroneckerBlockIndex M₁ M₂ m₁ m₂)).toPEquiv.toMatrix *
        kroneckerFin B C *
        (((tracySinghIndex N₁ N₂ n₁ n₂).symm.trans
          (kroneckerBlockIndex N₁ N₂ n₁ n₂)).toPEquiv.toMatrix)ᵀ := by
  rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext I J
  obtain ⟨⟨⟨I₁, I₂⟩, ⟨i₁, i₂⟩⟩, rfl⟩ := (tracySinghIndex M₁ M₂ m₁ m₂).surjective I
  obtain ⟨⟨⟨J₁, J₂⟩, ⟨j₁, j₂⟩⟩, rfl⟩ := (tracySinghIndex N₁ N₂ n₁ n₂).surjective J
  simp [tracySinghFin, kroneckerBlockIndex, tracySingh, kroneckerFin_apply]

/-- **§12.3.3**, the block Khatri–Rao product of two `M × N` block matrices: the block matrix of the
blockwise Kronecker products `B_ij ⊗ C_ij` (typed: block indices `M`, `N`). -/
def blockKhatriRao {M N p₁ q₁ p₂ q₂ : Type*} (B : Matrix (M × p₁) (N × q₁) ℝ)
    (C : Matrix (M × p₂) (N × q₂) ℝ) : Matrix (M × (p₁ × p₂)) (N × (q₁ × q₂)) ℝ :=
  of fun I J => B (I.1, I.2.1) (J.1, J.2.1) * C (I.1, I.2.2) (J.1, J.2.2)

/-- **§12.3.3**: the Hadamard product `B .* C` and the column Khatri–Rao product
`[b₁ | ⋯ | b_n] ⊙ [c₁ | ⋯ | c_n] = [b₁ ⊗ c₁ | ⋯ | b_n ⊗ c_n]` are submatrices of `B ⊗ C`, and the
block Khatri–Rao product (blocks `B_ij ⊗ C_ij`) is a submatrix of the Tracy–Singh product. -/
theorem hadamard_khatriRao_submatrix_kronecker {m n r : ℕ} (B C : Matrix (Fin m) (Fin n) ℝ)
    (F : Matrix (Fin m₁) (Fin r) ℝ) (G : Matrix (Fin m₂) (Fin r) ℝ) :
    B ⊙ C = (B ⊗ₖ C).submatrix (fun i => (i, i)) (fun j => (j, j)) ∧
      khatriRao F G = (F ⊗ₖ G).submatrix id (fun j => (j, j)) ∧
      (∀ j, (fun x => khatriRao F G x j) = kroneckerVec (fun i => F i j) fun i => G i j) ∧
      ∀ {M N p₁ q₁ p₂ q₂ : Type*} (B' : Matrix (M × p₁) (N × q₁) ℝ)
        (C' : Matrix (M × p₂) (N × q₂) ℝ),
        blockKhatriRao B' C' =
          (tracySingh B' C').submatrix (fun I => ((I.1, I.1), I.2)) fun J => ((J.1, J.1), J.2) :=
  ⟨hadamard_eq_submatrix_kronecker B C, khatriRao_eq_submatrix_kronecker F G,
    fun _ => rfl, fun _ _ => rfl⟩

end TracySingh

/-! ### `vec` and `reshape` (12.3.9)–(12.3.12) -/

/-- The book's `reshape(a, m, n)` of a vector `a ∈ ℝ^{mn}`: the `m × n` matrix `A` with
`vec(A) = a`. -/
def reshapeVec {m n : ℕ} (a : Fin (n * m) → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i j => a (finProdFinEquiv (j, i))

/-- `vec(reshape(a, m, n)) = a`. -/
@[simp]
theorem vecFin_reshapeVec {m n : ℕ} (a : Fin (n * m) → ℝ) : vecFin (reshapeVec a) = a := by
  funext t
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective t
  rw [vecFin_apply, reshapeVec, of_apply]

/-- **(12.3.9)**: `Y = C X Bᵀ ⇔ vec(Y) = (B ⊗ C) vec(X)` for `B ∈ ℝ^{m₁×n₁}`, `C ∈ ℝ^{m₂×n₂}` —
chapter 1's (1.3.6) (the book's `X ∈ ℝ^{n₁×m₂}` reads `X ∈ ℝ^{n₂×n₁}`). -/
theorem equation_12_3_9 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ)
    (X : Matrix (Fin n₂) (Fin n₁) ℝ) (Y : Matrix (Fin m₂) (Fin m₁) ℝ) :
    Y = C * X * Bᵀ ↔ vecFin Y = kroneckerFin B C *ᵥ vecFin X :=
  Chapter01.equation_1_3_6 B C X Y

/-- `vec` is additive over finite sums. -/
theorem vecFin_sum {m n p : ℕ} (A : Fin p → Matrix (Fin m) (Fin n) ℝ) :
    vecFin (∑ k, A k) = ∑ k, vecFin (A k) := by
  funext t
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective t
  simp [vecFin_apply, Finset.sum_apply, Matrix.sum_apply]

/-- **(12.3.10) ⇔ (12.3.11)**: `F₁ X G₁ᵀ + ⋯ + F_p X G_pᵀ = C` iff
`(G₁ ⊗ F₁ + ⋯ + G_p ⊗ F_p) vec(X) = vec(C)`; and `reshape(v ⊗ u, m, n) = u vᵀ` (typed:
`Matrix.unvec`). -/
theorem equation_12_3_11 {p : ℕ} (F : Fin p → Matrix (Fin m₂) (Fin n₂) ℝ)
    (G : Fin p → Matrix (Fin m₁) (Fin n₁) ℝ) (X : Matrix (Fin n₂) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin m₁) ℝ) :
    (∑ k, F k * X * (G k)ᵀ = C ↔ (∑ k, kroneckerFin (G k) (F k)) *ᵥ vecFin X = vecFin C) ∧
      ∀ {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ), unvec (kroneckerVec v u) = vecMulVec u v := by
  refine ⟨?_, fun u v => unvec_kroneckerVec v u⟩
  rw [sum_mulVec]
  have h : ∀ k, kroneckerFin (G k) (F k) *ᵥ vecFin X = vecFin (F k * X * (G k)ᵀ) :=
    fun k => ((equation_12_3_9 (G k) (F k) X _).1 rfl).symm
  simp only [h, ← vecFin_sum]
  exact ⟨fun h' => h' ▸ rfl, fun h' => vecFin_injective h'⟩

/-- **(12.3.12)**: `vec(Aᵀ) = 𝒫_{r,q} vec(A)` for `A ∈ ℝ^{q×r}`. -/
theorem equation_12_3_12 {q r : ℕ} (A : Matrix (Fin q) (Fin r) ℝ) :
    vecFin Aᵀ = perfectShuffle r q *ᵥ vecFin A :=
  (perfectShuffle_mulVec_vecFin A).symm

/-! ### The two-pass transposition (§12.3.5) -/

section TwoPass

/-- `reshape(vec(Y)) = Y`. -/
@[simp]
theorem reshapeVec_vecFin {m n : ℕ} (Y : Matrix (Fin m) (Fin n) ℝ) :
    reshapeVec (vecFin Y) = Y := by
  ext i j
  rw [reshapeVec, of_apply, vecFin_apply]

/-- The perfect shuffle in the left factor of a Kronecker product with an identity permutes the
blocks of a vector: `((𝒫_{p,r} ⊗ I) w)((a, b), c) = w((b, a), c)`. -/
theorem kroneckerFin_perfectShuffle_one_mulVec {p r q : ℕ} (w : Fin (p * r * q) → ℝ) (a : Fin r)
    (b : Fin p) (c : Fin q) :
    (kroneckerFin (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) ℝ)
      (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ w) (finProdFinEquiv (finProdFinEquiv (a, b), c)) =
      w (finProdFinEquiv (finProdFinEquiv (b, a), c)) := by
  conv_lhs => rw [← vecFin_reshapeVec w]
  rw [kroneckerFin_mulVec_vecFin, Matrix.one_mul, transpose_perfectShuffle, perfectShuffle,
    PEquiv.mul_toMatrix_toPEquiv, vecFin_apply, submatrix_apply, Equiv.symm_symm, id,
    finPerfectShuffle_apply, reshapeVec, of_apply]

/-- The perfect shuffle in the right factor of a Kronecker product with an identity permutes within
the blocks of a vector: `((I ⊗ 𝒫_{p,r}) w)(K, (a, b)) = w(K, (b, a))`. -/
theorem kroneckerFin_one_perfectShuffle_mulVec {p r k : ℕ} (w : Fin (k * (p * r)) → ℝ)
    (K : Fin k) (a : Fin r) (b : Fin p) :
    (kroneckerFin (1 : Matrix (Fin k) (Fin k) ℝ)
      (perfectShuffle p r : Matrix (Fin (r * p)) (Fin (p * r)) ℝ) *ᵥ w)
      (finProdFinEquiv (K, finProdFinEquiv (a, b))) =
      w (finProdFinEquiv (K, finProdFinEquiv (b, a))) := by
  conv_lhs => rw [← vecFin_reshapeVec w]
  rw [kroneckerFin_mulVec_vecFin, transpose_one, Matrix.mul_one, perfectShuffle,
    PEquiv.toMatrix_toPEquiv_mul, vecFin_apply, submatrix_apply, id, finPerfectShuffle_symm,
    finPerfectShuffle_apply, reshapeVec, of_apply]

variable {q r : ℕ}

/-- The first pass `Γ₁ vec(A)`, entrywise: its entry `(k, j, i)` is `(A_k)_{ij}`. -/
private theorem twoPass_first (A : Matrix (Fin (r * q)) (Fin q) ℝ) (k : Fin r) (i j : Fin q) :
    (kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ
      (vecFin A ∘ finCongr (by ring))) (finProdFinEquiv (finProdFinEquiv (k, j), i)) =
      A (finProdFinEquiv (k, i)) j := by
  rw [kroneckerFin_perfectShuffle_one_mulVec, Function.comp_apply]
  have : finCongr (by ring) (finProdFinEquiv (finProdFinEquiv (j, k), i)) =
      (finProdFinEquiv (j, finProdFinEquiv (k, i)) : Fin (q * (r * q))) := by
    ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [this, vecFin_apply]

/-- The two passes `Γ₂ Γ₁ vec(A)`, entrywise: the entry `(k, a, b)` is `(A_k)_{ab}`. -/
private theorem twoPass_second (A : Matrix (Fin (r * q)) (Fin q) ℝ) (k : Fin r) (a b : Fin q) :
    (kroneckerFin (1 : Matrix (Fin r) (Fin r) ℝ) (perfectShuffle q q) *ᵥ
      ((kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ
        (vecFin A ∘ finCongr (by ring))) ∘ finCongr (by ring)))
      (finProdFinEquiv (k, finProdFinEquiv (a, b))) = A (finProdFinEquiv (k, a)) b := by
  rw [kroneckerFin_one_perfectShuffle_mulVec, Function.comp_apply]
  have : finCongr (by ring) (finProdFinEquiv (k, finProdFinEquiv (b, a))) =
      (finProdFinEquiv (finProdFinEquiv (k, b), a) : Fin (r * q * q)) := by
    ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [this]
  exact twoPass_first A k a b

/-- **§12.3.5**, the two-pass transposition of `A = [A₁; ⋯; A_r]` (`A_k ∈ ℝ^{q×q}`): with
`Γ₁ = 𝒫_{q,r} ⊗ I_q` and `Γ₂ = I_r ⊗ 𝒫_{q,q}`, `reshape(Γ₁ vec(A), q, rq) = [A₁ | ⋯ | A_r]`,
`reshape(Γ₂ Γ₁ vec(A), q, rq) = [A₁ᵀ ⋯ A_rᵀ] = Aᵀ`, and `𝒫_{q,rq} = Γ₂ Γ₁` (up to the identification
of the size products). The book prints `Γ₁ = 𝒫_{r,q} ⊗ I_q` (its transpose; the two agree only for
`r = q`) and announces a factorization of `𝒫_{rq,q}` before writing `𝒫_{q,rq}`. -/
theorem perfectShuffle_two_pass (A : Matrix (Fin (r * q)) (Fin q) ℝ) :
    reshapeVec (kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ
        (vecFin A ∘ finCongr (by ring))) =
      (of fun i J => A (finProdFinEquiv ((finProdFinEquiv.symm J).1, i))
        (finProdFinEquiv.symm J).2 : Matrix (Fin q) (Fin (r * q)) ℝ) ∧
    reshapeVec ((kroneckerFin (1 : Matrix (Fin r) (Fin r) ℝ) (perfectShuffle q q) *ᵥ
        ((kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ) *ᵥ
          (vecFin A ∘ finCongr (by ring))) ∘ finCongr (by ring))) ∘ finCongr (by ring)) = Aᵀ ∧
    (perfectShuffle q (r * q) : Matrix (Fin (r * q * q)) (Fin (q * (r * q))) ℝ).submatrix
        (finCongr (by ring)) id =
      kroneckerFin (1 : Matrix (Fin r) (Fin r) ℝ) (perfectShuffle q q) *
        (kroneckerFin (perfectShuffle q r) (1 : Matrix (Fin q) (Fin q) ℝ)).submatrix
          (finCongr (by ring)) (finCongr (by ring)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i J
    obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective J
    rw [reshapeVec, of_apply, twoPass_first, of_apply, Equiv.symm_apply_apply]
  · ext i R'
    obtain ⟨⟨k, a⟩, rfl⟩ := finProdFinEquiv.surjective R'
    rw [reshapeVec, of_apply, Function.comp_apply, transpose_apply]
    have : finCongr (by ring) (finProdFinEquiv (finProdFinEquiv (k, a), i)) =
        (finProdFinEquiv (k, finProdFinEquiv (a, i)) : Fin (r * (q * q))) := by
      ext
      simp [finProdFinEquiv_apply_val]
      ring
    rw [this, twoPass_second]
  · refine ext_of_mulVec_single fun j => ?_
    set x : Fin (q * (r * q)) → ℝ := Pi.single j 1
    set B : Matrix (Fin (r * q)) (Fin q) ℝ := reshapeVec x
    have hx : x = vecFin B := (vecFin_reshapeVec x).symm
    rw [hx, ← mulVec_mulVec, submatrix_mulVec_equiv, finCongr_symm]
    funext t
    obtain ⟨⟨k, ab⟩, rfl⟩ := finProdFinEquiv.surjective t
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective ab
    rw [twoPass_second]
    change (perfectShuffle q (r * q) *ᵥ vecFin B) (finCongr _ _) = _
    rw [perfectShuffle_mulVec_vecFin]
    have : finCongr (by ring) (finProdFinEquiv (k, finProdFinEquiv (a, b))) =
        (finProdFinEquiv (finProdFinEquiv (k, a), b) : Fin (r * q * q)) := by
      ext
      simp [finProdFinEquiv_apply_val]
      ring
    rw [this, vecFin_apply, transpose_apply]

end TwoPass

/-! ### The Tracy–Singh permutations (12.3.7)–(12.3.8) -/

section TracySinghPerm

variable {M₁ M₂ m₁ m₂ : ℕ}

/-- The row permutation of (12.3.7) acting on a vector: the Kronecker order `(I₁, i₁, I₂, i₂)` goes
to the Tracy–Singh order `(I₁, I₂, i₁, i₂)`. -/
private theorem tracySinghPerm_mulVec (x : Fin (M₁ * m₁ * (M₂ * m₂)) → ℝ)
    (t : Fin (M₁ * M₂ * (m₁ * m₂))) :
    (kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *ᵥ
        ((kroneckerFin (1 : Matrix (Fin M₁) (Fin M₁) ℝ) (perfectShuffle m₁ (M₂ * m₂)) *ᵥ
          (x ∘ finCongr (by ring))) ∘ finCongr (by ring))) t =
      x (((tracySinghIndex M₁ M₂ m₁ m₂).symm.trans (kroneckerBlockIndex M₁ M₂ m₁ m₂)) t) := by
  obtain ⟨⟨⟨I₁, I₂⟩, ⟨i₁, i₂⟩⟩, rfl⟩ := (tracySinghIndex M₁ M₂ m₁ m₂).surjective t
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  change (kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *ᵥ _)
    (finProdFinEquiv (finProdFinEquiv (I₁, I₂), finProdFinEquiv (i₁, i₂))) = _
  rw [kroneckerFin_one_perfectShuffle_mulVec, Function.comp_apply]
  have e1 : finCongr (by ring) (finProdFinEquiv (finProdFinEquiv (I₁, I₂),
      finProdFinEquiv (i₂, i₁))) = (finProdFinEquiv (I₁, finProdFinEquiv
        (finProdFinEquiv (I₂, i₂), i₁)) : Fin (M₁ * (M₂ * m₂ * m₁))) := by
    ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [e1, kroneckerFin_one_perfectShuffle_mulVec, Function.comp_apply]
  congr 1
  ext
  simp [finProdFinEquiv_apply_val, kroneckerBlockIndex]
  ring

/-- **(12.3.7)–(12.3.8)**: the permutations of (12.3.6) are
`P = (I_{M₁M₂} ⊗ 𝒫_{m₂,m₁})(I_{M₁} ⊗ 𝒫_{m₁,M₂m₂})` and `Q = (I_{N₁N₂} ⊗ 𝒫_{n₂,n₁})(I_{N₁} ⊗
𝒫_{n₁,N₂n₂})` (chapter 1's perfect shuffles and positional Kronecker products, up to the
identification of the size products), so that `B ⊗_TS C = P (B ⊗ C) Qᵀ`. -/
theorem equation_12_3_7 {N₁ N₂ n₁ n₂ : ℕ} (B : Matrix (Fin (M₁ * m₁)) (Fin (N₁ * n₁)) ℝ)
    (C : Matrix (Fin (M₂ * m₂)) (Fin (N₂ * n₂)) ℝ) :
    ((tracySinghIndex M₁ M₂ m₁ m₂).symm.trans
        (kroneckerBlockIndex M₁ M₂ m₁ m₂)).toPEquiv.toMatrix =
      kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *
        (kroneckerFin (1 : Matrix (Fin M₁) (Fin M₁) ℝ) (perfectShuffle m₁ (M₂ * m₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring)) ∧
    ((tracySinghIndex N₁ N₂ n₁ n₂).symm.trans
        (kroneckerBlockIndex N₁ N₂ n₁ n₂)).toPEquiv.toMatrix =
      kroneckerFin (1 : Matrix (Fin (N₁ * N₂)) (Fin (N₁ * N₂)) ℝ) (perfectShuffle n₂ n₁) *
        (kroneckerFin (1 : Matrix (Fin N₁) (Fin N₁) ℝ) (perfectShuffle n₁ (N₂ * n₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring)) ∧
    tracySinghFin B C =
      (kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *
        (kroneckerFin (1 : Matrix (Fin M₁) (Fin M₁) ℝ) (perfectShuffle m₁ (M₂ * m₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring))) * kroneckerFin B C *
      (kroneckerFin (1 : Matrix (Fin (N₁ * N₂)) (Fin (N₁ * N₂)) ℝ) (perfectShuffle n₂ n₁) *
        (kroneckerFin (1 : Matrix (Fin N₁) (Fin N₁) ℝ) (perfectShuffle n₁ (N₂ * n₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring)))ᵀ := by
  have key : ∀ {M₁ M₂ m₁ m₂ : ℕ},
      ((tracySinghIndex M₁ M₂ m₁ m₂).symm.trans
        (kroneckerBlockIndex M₁ M₂ m₁ m₂)).toPEquiv.toMatrix =
      kroneckerFin (1 : Matrix (Fin (M₁ * M₂)) (Fin (M₁ * M₂)) ℝ) (perfectShuffle m₂ m₁) *
        (kroneckerFin (1 : Matrix (Fin M₁) (Fin M₁) ℝ) (perfectShuffle m₁ (M₂ * m₂))).submatrix
          (finCongr (by ring)) (finCongr (by ring)) := by
    intro M₁ M₂ m₁ m₂
    refine ext_of_mulVec_single fun j => ?_
    rw [← mulVec_mulVec, submatrix_mulVec_equiv, finCongr_symm, PEquiv.toMatrix_toPEquiv_mulVec]
    funext t
    rw [Function.comp_apply, tracySinghPerm_mulVec]
  refine ⟨key, key, ?_⟩
  rw [← key, ← key]
  exact equation_12_3_6 B C

end TracySinghPerm

/-! ### The rearrangement and the Kronecker product SVD (§12.3.6) -/

/-- **§12.3.6**, Definition: the book's `𝓡(A) ∈ ℝ^{m₁n₁ × m₂n₂}` for `A ∈ ℝ^{m₁m₂ × n₁n₂}` blocked
as (12.3.16) (`A_ij ∈ ℝ^{m₂×n₂}`): row `(j − 1) m₁ + i` is `vec(A_ij)ᵀ`, the rows ordered
`Ã₁, …, Ã_{n₁}`. The backbone's `Matrix.kroneckerRearrange` read through `finProdFinEquiv`. -/
def rearrangement (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) ℝ :=
  (kroneckerRearrange (A.reindex finProdFinEquiv.symm finProdFinEquiv.symm)).reindex
    finProdFinEquiv finProdFinEquiv

/-- The entries of the rearrangement: `𝓡(A)((j, i), (l, k)) = (A_ij)_kl`. -/
@[simp]
theorem rearrangement_apply (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) (i : Fin m₁)
    (j : Fin n₁) (k : Fin m₂) (l : Fin n₂) :
    rearrangement A (finProdFinEquiv (j, i)) (finProdFinEquiv (l, k)) =
      A (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) := by
  simp [rearrangement]

/-- The rearrangement is linear. -/
theorem rearrangement_sub (A A' : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    rearrangement (A - A') = rearrangement A - rearrangement A' :=
  rfl

/-- The rearrangement commutes with scalar multiples. -/
theorem rearrangement_smul (c : ℝ) (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    rearrangement (c • A) = c • rearrangement A :=
  rfl

/-- The rearrangement commutes with finite sums. -/
theorem rearrangement_sum {ι : Type*} (s : Finset ι)
    (X : ι → Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    rearrangement (∑ k ∈ s, X k) = ∑ k ∈ s, rearrangement (X k) := by
  ext I J
  simp [rearrangement, Matrix.sum_apply]

/-- `𝓡(B ⊗ C) = vec(B) vec(C)ᵀ`. -/
theorem rearrangement_kroneckerFin (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    rearrangement (kroneckerFin B C) = vecMulVec (vecFin B) (vecFin C) := by
  ext I J
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective I
  obtain ⟨⟨l, k⟩, rfl⟩ := finProdFinEquiv.surjective J
  rw [rearrangement_apply, kroneckerFin_apply, vecMulVec_apply, vecFin_apply, vecFin_apply]

section Norm

open scoped Matrix.Norms.Frobenius

/-- Reindexing preserves the Frobenius norm. -/
theorem frobenius_norm_reindex {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] (e₁ : α ≃ γ) (e₂ : β ≃ δ) (A : Matrix α β ℝ) : ‖A.reindex e₁ e₂‖ = ‖A‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq]
  simp only [reindex_apply, submatrix_apply]
  rw [← e₁.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e₂.sum_comp]
  simp

/-- `‖𝓡(A)‖_F = ‖A‖_F`: the rearrangement permutes the entries. -/
theorem frobenius_norm_rearrangement (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) :
    ‖rearrangement A‖ = ‖A‖ := by
  rw [rearrangement, frobenius_norm_reindex, frobenius_norm_kroneckerRearrange,
    frobenius_norm_reindex]

/-- **(12.3.14)** and the display after the example: `φ(B, C) = ‖A − B ⊗ C‖_F =
‖𝓡(A) − vec(B) vec(C)ᵀ‖_F`, so minimizing `φ` is finding a nearest rank-one matrix to `𝓡(A)`. -/
theorem equation_12_3_14 (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ)
    (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    ‖A - kroneckerFin B C‖ = ‖rearrangement A - vecMulVec (vecFin B) (vecFin C)‖ := by
  rw [← frobenius_norm_rearrangement, rearrangement_sub, rearrangement_kroneckerFin]

/-- **(12.3.20)**: for `A ∈ ℝ^{m²×m²}`, `φ_sym(X) = ‖A − X ⊗ X‖_F = ‖𝓡(A) − vec(X) vec(X)ᵀ‖_F`. -/
theorem equation_12_3_20 {m : ℕ} (A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ)
    (X : Matrix (Fin m) (Fin m) ℝ) :
    ‖A - kroneckerFin X X‖ = ‖rearrangement A - vecMulVec (vecFin X) (vecFin X)‖ :=
  equation_12_3_14 A X X

/-- **(12.3.21)**: for `A ∈ ℝ^{m²×m²}`, `φ_skew(X, Y) = ‖A − (X ⊗ Y − Y ⊗ X)‖_F =
‖𝓡(A) − (vec(X) vec(Y)ᵀ − vec(Y) vec(X)ᵀ)‖_F` (the book writes `φ_skew(X)` and drops a parenthesis).
-/
theorem equation_12_3_21 {m : ℕ} (A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ)
    (X Y : Matrix (Fin m) (Fin m) ℝ) :
    ‖A - (kroneckerFin X Y - kroneckerFin Y X)‖ =
      ‖rearrangement A - (vecMulVec (vecFin X) (vecFin Y) - vecMulVec (vecFin Y) (vecFin X))‖ := by
  rw [← frobenius_norm_rearrangement, rearrangement_sub, rearrangement_sub,
    rearrangement_kroneckerFin, rearrangement_kroneckerFin]

end Norm

/-- **Theorem 12.3.1** (Kronecker product SVD): if `𝓡(A) = ∑_{k=1}^r σ_k u_k v_kᵀ` (12.3.17) then
`A = ∑_{k=1}^r σ_k U_k ⊗ V_k` (12.3.18) with `U_k = reshape(u_k, m₁, n₁)`, `V_k = reshape(v_k, m₂,
n₂)`; and when the expansion is an SVD (`σ_k > 0`, the `u_k` and the `v_k` orthonormal) `r` is the
Kronecker product rank of `A`, the rank of `𝓡(A)`. -/
theorem theorem_12_3_1 {r : ℕ} (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ) (σ : Fin r → ℝ)
    (u : Fin r → Fin (n₁ * m₁) → ℝ) (v : Fin r → Fin (n₂ * m₂) → ℝ)
    (hA : rearrangement A = ∑ k, σ k • vecMulVec (u k) (v k)) :
    A = ∑ k, σ k • kroneckerFin (reshapeVec (u k)) (reshapeVec (v k)) ∧
      ((∀ k, 0 < σ k) → (∀ k l, u k ⬝ᵥ u l = if k = l then 1 else 0) →
        (∀ k l, v k ⬝ᵥ v l = if k = l then 1 else 0) →
        kroneckerRank (A.reindex finProdFinEquiv.symm finProdFinEquiv.symm) = r) := by
  refine ⟨?_, fun hσ hu hv => ?_⟩
  · ext I J
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective I
    obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective J
    have h := congrFun (congrFun hA (finProdFinEquiv (j, i))) (finProdFinEquiv (l, k))
    rw [rearrangement_apply] at h
    rw [h, Matrix.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [reshapeVec, kroneckerFin_apply, vecMulVec_apply]
  · have hR : kroneckerRank (A.reindex finProdFinEquiv.symm finProdFinEquiv.symm) =
        (rearrangement A).rank := by
      rw [kroneckerRank, rearrangement, rank_reindex]
    rw [hR, hA]
    set U : Matrix (Fin (n₁ * m₁)) (Fin r) ℝ := of fun I t => u t I
    set V : Matrix (Fin (n₂ * m₂)) (Fin r) ℝ := of fun J t => v t J
    have hUV : (∑ t, σ t • vecMulVec (u t) (v t)) = U * diagonal σ * Vᵀ := by
      ext I J
      simp [U, V, Matrix.sum_apply, mul_apply, vecMulVec_apply, diagonal_apply, mul_comm,
        mul_left_comm]
    have hU : Uᵀ * U = 1 := by
      ext t l
      rw [mul_apply, one_apply, ← hu t l]
      rfl
    have hV : Vᵀ * V = 1 := by
      ext t l
      rw [mul_apply, one_apply, ← hv t l]
      rfl
    rw [hUV]
    refine le_antisymm ?_ ?_
    · refine (rank_mul_le_left _ _).trans ((rank_mul_le_left _ _).trans ?_)
      exact (rank_le_card_width U).trans (by simp)
    · have hD : Uᵀ * (U * diagonal σ * Vᵀ) * V = diagonal σ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hV,
          Matrix.mul_one]
      have hrk : (diagonal σ).rank = r := by
        rw [rank_diagonal, Fintype.card_subtype, Finset.filter_true_of_mem
          (fun t _ => (hσ t).ne'), Finset.card_univ, Fintype.card_fin]
      calc r = (diagonal σ).rank := hrk.symm
        _ = (Uᵀ * (U * diagonal σ * Vᵀ) * V).rank := by rw [hD]
        _ ≤ (U * diagonal σ * Vᵀ).rank :=
          (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- A sum of `r` rank-one matrices has rank at most `r`. -/
private theorem rank_sum_vecMulVec_le {p q r : ℕ} (x : Fin r → Fin p → ℝ)
    (y : Fin r → Fin q → ℝ) : (∑ k, vecMulVec (x k) (y k)).rank ≤ r := by
  have h : (∑ k, vecMulVec (x k) (y k)) =
      (of fun I k => x k I : Matrix (Fin p) (Fin r) ℝ) * of fun k J => y k J := by
    ext I J
    simp [mul_apply, vecMulVec_apply, Matrix.sum_apply]
  rw [h]
  exact (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans (by simp))

/-- The rank-`k` truncation of an SVD as the sum `∑_{t<k} σ_t u_t v_tᵀ` of its leading terms, for
`k` at most both dimensions. -/
private theorem svdTruncation_eq_sum {p q k : ℕ} (hkp : k ≤ p) (hkq : k ≤ q)
    (U : Matrix (Fin p) (Fin p) ℝ) (σ : ℕ → ℝ) (V : Matrix (Fin q) (Fin q) ℝ) :
    svdTruncation U σ V k = ∑ t : Fin k,
      σ t • vecMulVec (fun I => U I (Fin.castLE hkp t)) (fun J => V J (Fin.castLE hkq t)) := by
  ext I J
  let g : Fin p → ℝ := fun a =>
    if h : (a : ℕ) < k then σ a * U I a * V J ⟨a, lt_of_lt_of_le h hkq⟩ else 0
  have hR : (∑ t : Fin k, σ t • vecMulVec (fun I => U I (Fin.castLE hkp t))
      (fun J => V J (Fin.castLE hkq t))) I J = ∑ a, g a := by
    rw [Matrix.sum_apply, show (∑ a, g a) = ∑ t : Fin k, g (Fin.castLE hkp t) from ?_]
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, g, Fin.val_castLE, t.isLt,
        ↓reduceDIte]
      rw [mul_assoc]
      rfl
    · rw [show (∑ t : Fin k, g (Fin.castLE hkp t)) =
          ∑ a ∈ Finset.univ.map (Fin.castLEEmb hkp), g a from
          (Finset.sum_map Finset.univ (Fin.castLEEmb hkp) g).symm]
      refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).symm
      have hak : ¬ (a : ℕ) < k := fun h =>
        ha (Finset.mem_map.2 ⟨⟨a, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      simp [g, hak]
  rw [hR, svdTruncation]
  simp only [mul_apply, rectDiagonal_apply, star_apply, star_trivial, Finset.sum_mul,
    RCLike.ofReal_real_eq_id, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < k
  · rw [Finset.sum_eq_single ⟨a, lt_of_lt_of_le ha hkq⟩]
    · simp only [g, ha, ↓reduceIte, ↓reduceDIte]
      ring
    · intro b _ hb
      have : (a : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp
  · refine (Finset.sum_eq_zero fun b _ => ?_).trans (by simp [g, ha])
    by_cases hab : (a : ℕ) = b
    · simp [← hab, ha]
    · simp [hab]

open scoped Matrix.Norms.Frobenius in
/-- **(12.3.19)** and the paragraph before it: if `Uᵀ 𝓡(A) V = Σ` is an SVD of the rearrangement
(12.3.17) and `r̃` is at most both dimensions of `𝓡(A)`, then
`A_r̃ = ∑_{k=1}^{r̃} σ_k U_k ⊗ V_k`, with `U_k = reshape(U(:, k), m₁, n₁)` and
`V_k = reshape(V(:, k), m₂, n₂)`, is a closest matrix to `A` in the Frobenius norm among the sums of
`r̃` Kronecker products: `‖A − A_r̃‖_F ≤ ‖A − ∑_{k=1}^{r̃} B_k ⊗ C_k‖_F`. Through `𝓡`, an isometry,
this is the Eckart–Young–Mirsky theorem for `𝓡(A)`
(`Matrix.isLeast_frobenius_norm_sub_of_rank_le`), since `𝓡(∑ B_k ⊗ C_k) = ∑ vec(B_k) vec(C_k)ᵀ` has
rank at most `r̃` and `𝓡(A_r̃)` is the truncation of the SVD. -/
theorem equation_12_3_19 (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ)
    {U : Matrix (Fin (n₁ * m₁)) (Fin (n₁ * m₁)) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n₂ * m₂)) (Fin (n₂ * m₂)) ℝ} (h : IsSVD (rearrangement A) U σ V) {r : ℕ}
    (hr₁ : r ≤ n₁ * m₁) (hr₂ : r ≤ n₂ * m₂) (B : Fin r → Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Fin r → Matrix (Fin m₂) (Fin n₂) ℝ) :
    ‖A - ∑ k : Fin r, σ k • kroneckerFin (reshapeVec fun I => U I (Fin.castLE hr₁ k))
        (reshapeVec fun J => V J (Fin.castLE hr₂ k))‖ ≤
      ‖A - ∑ k, kroneckerFin (B k) (C k)‖ := by
  rw [← frobenius_norm_rearrangement, rearrangement_sub, rearrangement_sum,
    ← frobenius_norm_rearrangement (A - _), rearrangement_sub, rearrangement_sum]
  simp only [rearrangement_smul, rearrangement_kroneckerFin, vecFin_reshapeVec]
  rw [← svdTruncation_eq_sum hr₁ hr₂, frobenius_norm_sub_svdTruncation h]
  have := (isLeast_frobenius_norm_sub_of_rank_le (rearrangement A) r).2
    ⟨_, rank_sum_vecMulVec_le (fun k => vecFin (B k)) (fun k => vecFin (C k)), rfl⟩
  simpa using this

/-- The Kronecker product is bilinear: scalars pass out of the left factor. -/
theorem kroneckerFin_smul_left (c : ℝ) (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) : kroneckerFin (c • B) C = c • kroneckerFin B C := by
  simp [kroneckerFin, smul_kronecker, submatrix_smul]

/-- The Kronecker product is bilinear: scalars pass out of the right factor. -/
theorem kroneckerFin_smul_right (c : ℝ) (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) : kroneckerFin B (c • C) = c • kroneckerFin B C := by
  simp [kroneckerFin, kronecker_smul, submatrix_smul]

/-- `reshape` is linear. -/
theorem reshapeVec_smul {m n : ℕ} (c : ℝ) (a : Fin (n * m) → ℝ) :
    reshapeVec (c • a) = c • reshapeVec a := by
  ext i j
  simp [reshapeVec]

open scoped Matrix.Norms.Frobenius in
/-- **(12.3.15)** and the sentence after it: "if `Uᵀ 𝓡(A) V = Σ` is the SVD of `𝓡(A)`, then
`vec(B_opt) = √σ₁ U(:, 1)`, `vec(C_opt) = √σ₁ V(:, 1)` minimize `φ(B, C) = ‖A − B ⊗ C‖_F`", "and
so do `α B_opt`, `C_opt/α` for any `α ≠ 0`": the case `r̃ = 1` of (12.3.19) (`equation_12_3_19`),
`B_opt ⊗ C_opt = σ₁ U₁ ⊗ V₁`. -/
theorem equation_12_3_15 (A : Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℝ)
    {U : Matrix (Fin (n₁ * m₁)) (Fin (n₁ * m₁)) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n₂ * m₂)) (Fin (n₂ * m₂)) ℝ} (h : IsSVD (rearrangement A) U σ V)
    (h₁ : 0 < n₁ * m₁) (h₂ : 0 < n₂ * m₂) {α : ℝ} (hα : α ≠ 0)
    (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    ‖A - kroneckerFin (α • reshapeVec (√(σ 0) • fun I => U I ⟨0, h₁⟩))
        (α⁻¹ • reshapeVec (√(σ 0) • fun J => V J ⟨0, h₂⟩))‖ ≤ ‖A - kroneckerFin B C‖ := by
  have hopt : kroneckerFin (α • reshapeVec (√(σ 0) • fun I => U I ⟨0, h₁⟩))
      (α⁻¹ • reshapeVec (√(σ 0) • fun J => V J ⟨0, h₂⟩)) =
      ∑ k : Fin 1, σ k • kroneckerFin (reshapeVec fun I => U I (Fin.castLE h₁ k))
        (reshapeVec fun J => V J (Fin.castLE h₂ k)) := by
    rw [Fin.sum_univ_one, kroneckerFin_smul_left, kroneckerFin_smul_right, reshapeVec_smul,
      reshapeVec_smul, kroneckerFin_smul_left, kroneckerFin_smul_right, smul_smul, smul_smul,
      smul_smul, mul_assoc, mul_assoc, Real.mul_self_sqrt (h.nonneg 0), ← mul_assoc,
      mul_inv_cancel₀ hα, one_mul]
    rfl
  have hBC : kroneckerFin B C = ∑ k : Fin 1, kroneckerFin ((fun _ => B) k) ((fun _ => C) k) := by
    rw [Fin.sum_univ_one]
  rw [hopt, hBC]
  exact equation_12_3_19 A h h₁ h₂ _ _

/-! ### Lemma 12.3.2 and the nearest `X ⊗ X` (§12.3.8) -/

section Symmetric

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- The quadratic form of `T` in the eigenbasis of a Schur decomposition `Qᵀ T Q = diag(α)`:
`xᵀ T x = ∑ α_i y_i²` with `y = Qᵀ x`, and `∑ y_i² = xᵀ x`. -/
private theorem dotProduct_mulVec_eq_sum {T Q : Matrix (Fin n) (Fin n) ℝ} {α : Fin n → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hT : Qᵀ * T * Q = diagonal α) (x : Fin n → ℝ) :
    x ⬝ᵥ (T *ᵥ x) = ∑ i, α i * (Qᵀ *ᵥ x) i ^ 2 ∧ ∑ i, (Qᵀ *ᵥ x) i ^ 2 = x ⬝ᵥ x := by
  have h1 : Q * Qᵀ = 1 := by
    exact (mem_orthogonalGroup_iff _ _).1 hQ
  have h2 : Qᵀ * Q = 1 := by
    exact (mem_orthogonalGroup_iff' _ _).1 hQ
  have hT' : T = Q * diagonal α * Qᵀ := by
    rw [← hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  have hy : ∀ w : Fin n → ℝ, x ⬝ᵥ (Q *ᵥ w) = (Qᵀ *ᵥ x) ⬝ᵥ w := fun w => by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  constructor
  · rw [hT', ← mulVec_mulVec, ← mulVec_mulVec, hy]
    simp only [dotProduct, mulVec_diagonal, sq]
    exact Finset.sum_congr rfl fun i _ => by ring
  · have h3 : (Qᵀ *ᵥ x) ⬝ᵥ (Qᵀ *ᵥ x) = x ⬝ᵥ x := by
      rw [← hy, mulVec_mulVec, h1, one_mulVec]
    rw [← h3]
    simp [dotProduct, sq]

/-- The column `q_k` of an orthogonal `Q` in a Schur decomposition `Qᵀ T Q = diag(α)` is a unit
eigenvector: `q_kᵀ q_k = 1` and `q_kᵀ T q_k = α_k`. -/
private theorem col_dotProduct {T Q : Matrix (Fin n) (Fin n) ℝ} {α : Fin n → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hT : Qᵀ * T * Q = diagonal α) (k : Fin n) :
    (fun i => Q i k) ⬝ᵥ (fun i => Q i k) = 1 ∧
      (fun i => Q i k) ⬝ᵥ (T *ᵥ fun i => Q i k) = α k := by
  have h2 : Qᵀ * Q = 1 := by
    exact (mem_orthogonalGroup_iff' _ _).1 hQ
  have hy : Qᵀ *ᵥ (fun i => Q i k) = Pi.single k 1 := by
    funext i
    have := congrFun (congrFun h2 i) k
    rw [mul_apply, one_apply] at this
    rw [Pi.single_apply]
    simpa [mulVec, dotProduct, eq_comm] using this
  obtain ⟨h1, h1'⟩ := dotProduct_mulVec_eq_sum hQ hT fun i => Q i k
  rw [hy] at h1 h1'
  refine ⟨?_, ?_⟩
  · rw [← h1']
    simp [Pi.single_apply]
  · rw [h1]
    simp [Pi.single_apply]

/-- The Rayleigh bounds from a Schur decomposition: for a unit `x`, `|xᵀ T x| ≤ max |α_i|` and
`xᵀ T x ≤ max α_i`. -/
private theorem rayleigh_bounds {T Q : Matrix (Fin n) (Fin n) ℝ} {α : Fin n → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hT : Qᵀ * T * Q = diagonal α) {x : Fin n → ℝ}
    (hx : x ⬝ᵥ x = 1) (k : Fin n) :
    ((∀ i, |α i| ≤ |α k|) → |x ⬝ᵥ (T *ᵥ x)| ≤ |α k|) ∧
      ((∀ i, α i ≤ α k) → x ⬝ᵥ (T *ᵥ x) ≤ α k) := by
  obtain ⟨h1, h2⟩ := dotProduct_mulVec_eq_sum hQ hT x
  rw [hx] at h2
  set y := Qᵀ *ᵥ x
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rw [h1]
    calc |∑ i, α i * y i ^ 2| ≤ ∑ i, |α i| * y i ^ 2 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          simp_rw [abs_mul, abs_sq]
      _ ≤ ∑ i, |α k| * y i ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hk i) (sq_nonneg _)
      _ = |α k| := by rw [← Finset.mul_sum, h2, mul_one]
  · rw [h1]
    calc ∑ i, α i * y i ^ 2 ≤ ∑ i, α k * y i ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hk i) (sq_nonneg _)
      _ = α k := by rw [← Finset.mul_sum, h2, mul_one]

/-- **Lemma 12.3.2**: for `M ∈ ℝ^{n×n}` and a Schur decomposition `Qᵀ T Q = diag(α₁, …, α_n)` of
`T = (M + Mᵀ)/2` (`Matrix.hermitianPart M`), if `|α_k| = max |α_i|` then `Z_opt = α_k q_k q_kᵀ`
(`q_k = Q(:, k)`) minimizes `‖M − Z‖_F` over symmetric `Z` of rank at most one. The book's
"`rank(Z) = 1`" fails for `T = 0`, where no matrix of rank exactly one attains the infimum; `rank ≤
1` is the formalized reading and coincides with it when `T ≠ 0`. -/
theorem lemma_12_3_2 (M Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hT : Qᵀ * hermitianPart M * Q = diagonal α) {k : Fin n}
    (hk : ∀ i, |α i| ≤ |α k|) :
    IsMinOn (fun Z => ‖M - Z‖) {Z | Z.IsSymm ∧ Z.rank ≤ 1}
      (α k • vecMulVec (fun i => Q i k) fun i => Q i k) := by
  have : Nonempty (Fin n) := ⟨k⟩
  set q : Fin n → ℝ := fun i => Q i k
  obtain ⟨hq, hqT⟩ := col_dotProduct hQ hT k
  have hqM : q ⬝ᵥ (M *ᵥ q) = α k := by rw [← dotProduct_mulVec_hermitianPart]; exact hqT
  have hopt : ‖M - α k • vecMulVec q q‖ ^ 2 = ‖M‖ ^ 2 - α k ^ 2 := by
    rw [norm_sub_smul_vecMulVec_self_sq M hq, hqM]
    ring
  rintro Z ⟨hZs, hZr⟩
  obtain ⟨β, x, hx, rfl⟩ := exists_eq_smul_vecMulVec_self_of_rank_le_one hZs hZr
  have ht : |x ⬝ᵥ (M *ᵥ x)| ≤ |α k| := by
    rw [← dotProduct_mulVec_hermitianPart]
    exact (rayleigh_bounds hQ hT hx k).1 hk
  have ht2 := sq_le_sq.2 ht
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  change ‖M - α k • vecMulVec q q‖ ^ 2 ≤ ‖M - β • vecMulVec x x‖ ^ 2
  rw [hopt, norm_sub_smul_vecMulVec_self_sq M hx]
  nlinarith [sq_nonneg (β - x ⬝ᵥ (M *ᵥ x)), sq_abs (x ⬝ᵥ (M *ᵥ x)), sq_abs (α k)]

end Symmetric

section NearestSelf

open scoped Matrix.Norms.Frobenius

/-- **§12.3.8**, "the solution `X_opt` is a reshaping of an eigenvector associated with the
symmetric part of `𝓡(A)`", in the form that is true: with a Schur decomposition `Qᵀ T Q = diag(α)`
of `T = (𝓡(A) + 𝓡(A)ᵀ)/2` and `α_k = max α_i`, `X_opt = reshape(√(α_k⁺) q_k, m, m)` minimizes
`φ_sym(X) = ‖A − X ⊗ X‖_F` (`α_k⁺ = max(α_k, 0)`). Lemma 12.3.2 alone does not give it:
`vec(X) vec(X)ᵀ` is positive semidefinite, so a negative eigenvalue of largest modulus is not
admissible. -/
theorem nearest_kronecker_self {m : ℕ} (A Q : Matrix (Fin (m * m)) (Fin (m * m)) ℝ)
    (α : Fin (m * m) → ℝ) (hQ : Q ∈ orthogonalGroup (Fin (m * m)) ℝ)
    (hT : Qᵀ * hermitianPart (rearrangement A) * Q = diagonal α) {k : Fin (m * m)}
    (hk : ∀ i, α i ≤ α k) :
    IsMinOn (fun X : Matrix (Fin m) (Fin m) ℝ => ‖A - kroneckerFin X X‖) Set.univ
      (reshapeVec (√(max (α k) 0) • fun i => Q i k)) := by
  intro X _
  change ‖A - kroneckerFin (reshapeVec (√(max (α k) 0) • fun i => Q i k))
      (reshapeVec (√(max (α k) 0) • fun i => Q i k))‖ ≤ ‖A - kroneckerFin X X‖
  rw [equation_12_3_20, equation_12_3_20, vecFin_reshapeVec]
  set R := rearrangement A
  set a := max (α k) 0 with ha
  set q : Fin (m * m) → ℝ := fun i => Q i k
  obtain ⟨hq, hqT⟩ := col_dotProduct hQ hT k
  have hqR : q ⬝ᵥ (R *ᵥ q) = α k := by rw [← dotProduct_mulVec_hermitianPart]; exact hqT
  have ha0 : 0 ≤ a := le_max_right _ _
  have haα : a * α k = a ^ 2 := by
    rcases le_total 0 (α k) with h | h
    · rw [ha, max_eq_left h]; ring
    · rw [ha, max_eq_right h]; ring
  have hopt : ‖R - vecMulVec (√a • q) (√a • q)‖ ^ 2 = ‖R‖ ^ 2 - a ^ 2 := by
    rw [smul_vecMulVec, vecMulVec_smul, smul_smul, Real.mul_self_sqrt ha0,
      norm_sub_smul_vecMulVec_self_sq R hq, hqR]
    nlinarith [haα]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hopt]
  set x := vecFin X
  by_cases hx0 : x ⬝ᵥ x = 0
  · have : x = 0 := by
      funext i
      have h := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j)) |>.1 hx0 i
        (Finset.mem_univ i)
      simpa using h
    have h0 : vecMulVec x x = 0 := by
      rw [this]
      ext i j
      simp [vecMulVec_apply]
    rw [h0, sub_zero]
    nlinarith [sq_nonneg a]
  · have hβ : 0 < x ⬝ᵥ x := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)) (Ne.symm hx0)
    set β := x ⬝ᵥ x
    set w := (√β)⁻¹ • x
    have hsβ : 0 < √β := Real.sqrt_pos.2 hβ
    have hw : w ⬝ᵥ w = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← sq, inv_pow,
        Real.sq_sqrt hβ.le, inv_mul_cancel₀ hβ.ne']
    have hc : β * ((√β)⁻¹ * (√β)⁻¹) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hβ.le, mul_inv_cancel₀ hβ.ne']
    have hxw : vecMulVec x x = β • vecMulVec w w := by
      ext i j
      simp only [w, vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(x i * x j)) * hc
    have ht : w ⬝ᵥ (R *ᵥ w) ≤ a := by
      rw [← dotProduct_mulVec_hermitianPart]
      exact ((rayleigh_bounds hQ hT hw k).2 hk).trans (le_max_left _ _)
    rw [hxw, norm_sub_smul_vecMulVec_self_sq R hw]
    nlinarith [sq_nonneg (β - a)]

end NearestSelf

/-! ### The reshaping identity of §12.3.10 -/

/-- **§12.3.10**: for `y = (B₁ ⊗ ⋯ ⊗ B_p) x`, with `P = B₁ ⊗ ⋯ ⊗ B_i ∈ ℝ^{M_i × N_i}` and
`Q = B_{i+1} ⊗ ⋯ ⊗ B_p` (so that `B₁ ⊗ ⋯ ⊗ B_p = P ⊗ Q` by associativity, chapter 1's (1.3.4)),
`reshape(y, M_p/M_i, M_i) = Q · reshape(x, N_p/N_i, N_i) · Pᵀ`. -/
theorem kronecker_mulVec_reshape {a b c e : ℕ} (P : Matrix (Fin a) (Fin b) ℝ)
    (Q : Matrix (Fin c) (Fin e) ℝ) (x : Fin (b * e) → ℝ) :
    reshapeVec (kroneckerFin P Q *ᵥ x) = Q * reshapeVec x * Pᵀ := by
  apply vecFin_injective
  rw [vecFin_reshapeVec, ← kroneckerFin_mulVec_vecFin, vecFin_reshapeVec]

/-! ### Lemma 12.3.3 -/

section Skew

open scoped Matrix.Norms.L2Operator

/-- For a skew-symmetric real `S` (a normal matrix), the spectral radius (of the complexification,
the eigenvalues `±iμ` being imaginary) is the spectral norm, `ρ(S) = ‖S‖₂`. -/
theorem complexSpectralRadius_toReal_of_skew {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : Sᵀ = -S) : (complexSpectralRadius S).toReal = lpOpNorm 2 S := by
  have hstar : star (complexify S) = -complexify S := by
    rw [star_eq_conjTranspose, ← complexify_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      hS, complexify_neg]
  have : IsStarNormal (complexify S) := ⟨by rw [hstar]; exact (Commute.refl _).neg_left⟩
  rw [complexSpectralRadius, ← l2_opNorm_eq_spectralRadius_of_isStarNormal,
    l2_opNNNorm_complexify, ENNReal.coe_toReal, coe_nnnorm, lpOpNorm_two]

end Skew

section SkewNearest

open scoped Matrix.Norms.Frobenius

/-- **Lemma 12.3.3.** "Suppose `M ∈ ℝ^{n×n}` and that `S = (M − Mᵀ)/2`. If
`S [u | v] = [u | v] [0 μ; −μ 0]` where `u, v ∈ ℝⁿ` are orthonormal and `μ = ρ(S)`, then
`Z_opt = μ (u vᵀ − v uᵀ)` minimizes `‖M − Z‖_F` over all rank-2 skew-symmetric matrices
`Z ∈ ℝ^{n×n}`." The spectral radius is the complex one (`ρ(S) = ‖S‖₂` for the normal `S`,
`complexSpectralRadius_toReal_of_skew`), and the competitors are the skew-symmetric matrices of rank
at most two (with `S = 0` the minimizer `Z_opt = 0` has rank `0`). Of the hypothesis
`S [u | v] = [u | v] [0 μ; −μ 0]` only the column `S v = μ u` is needed
(`Matrix.isMinOn_frobenius_norm_sub_skew_rank_le_two`). -/
theorem lemma_12_3_3 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {u v : Fin n → ℝ} {μ : ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (hSv : ((1 / 2 : ℝ) • (M - Mᵀ)) *ᵥ v = μ • u)
    (hμ : μ = (complexSpectralRadius ((1 / 2 : ℝ) • (M - Mᵀ))).toReal) :
    IsMinOn (fun Z => ‖M - Z‖) {Z | Zᵀ = -Z ∧ Z.rank ≤ 2}
      (μ • (vecMulVec u v - vecMulVec v u)) := by
  have hskew : ((1 / 2 : ℝ) • (M - Mᵀ))ᵀ = -((1 / 2 : ℝ) • (M - Mᵀ)) := by
    rw [transpose_smul, transpose_sub, transpose_transpose, ← smul_neg, neg_sub]
  rw [complexSpectralRadius_toReal_of_skew hskew] at hμ
  exact isMinOn_frobenius_norm_sub_skew_rank_le_two M hu hv huv hSv hμ

end SkewNearest

end GolubVanLoan.Chapter12
