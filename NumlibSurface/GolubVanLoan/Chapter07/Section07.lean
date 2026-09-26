import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.GeneralizedSchur
import NumlibSurface.GolubVanLoan.Chapter07.Section04

/-!
# Golub–Van Loan §7.7: the generalized eigenvalue problem

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.7: the spectrum `λ(A, B)` of a pencil and its basic properties (§7.7.1),
equivalent pencils (7.7.2), the generalized Schur decomposition (Theorem 7.7.1) and its real form
(Theorem 7.7.2), the Hessenberg–triangular form (§7.7.4), the first deflation of §7.7.5, generalized
inverse iteration and deflating subspaces (§7.7.8), and the linearization of a cubic polynomial
eigenvalue problem ((7.7.3)–(7.7.5)).

## Conventions

`λ(A, B)` is the backbone's `Matrix.pencilSpectrum A B = {z | det(A - z B) = 0}`, its eigenvectors
`Matrix.HasPencilEigenvector`, its characteristic polynomial `Matrix.pencilPoly`; complex
`Matrix (Fin n) (Fin n) ℂ` for the theory and real for the real Schur form. Block partitions are
`Matrix.fromBlocks`.

## Algorithms

The Hessenberg–triangular reduction (Algorithm 7.7.1), the zero chase of §7.7.5, the QZ step
(Algorithm 7.7.2) and the QZ algorithm (Algorithm 7.7.3) call chapter 5's Householder QR and shared
reflector and rotation helpers and chapter 3's back substitution, which are not yet available; they
are planned in this section's group and not written here.

## Not formalized

The Kronecker canonical form (mentioned, not stated); the `7`-digit example; Stewart's
chordal-metric bound (first order, quoted without proof) and Wilkinson's remark on
`t_kk = s_kk = 0`; the backward stability of QZ (`≈`, no derivation); flop counts.
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.7.1 Background -/

/-- **§7.7.1: "there are `n` eigenvalues if and only if `rank(B) = n`"**: the characteristic
polynomial `det(A - λB)` has degree `n` exactly when `B` has full rank. -/
theorem pencilSpectrum_card (A B : Matrix (Fin n) (Fin n) ℂ) :
    (pencilPoly A B).natDegree = n ↔ B.rank = n := by
  have h := natDegree_pencilPoly_eq_card_iff A B
  rw [Fintype.card_fin] at h
  rw [h, ← isUnit_iff_isUnit_det]
  exact ⟨fun h => by rw [rank_of_isUnit B h, Fintype.card_fin], fun h =>
    isUnit_of_rank_eq_card (by rw [h, Fintype.card_fin])⟩

/-- **§7.7.1, the three pencils**: with a rank-deficient `B`, `λ(A, B)` may be finite, empty or
all of `ℂ`: `λ([1 2; 0 3], [1 0; 0 0]) = {1}`, `λ([1 2; 0 3], [0 1; 0 0]) = ∅`,
`λ([1 2; 0 0], [1 0; 0 0]) = ℂ`. -/
theorem pencil_examples :
    pencilSpectrum !![(1 : ℂ), 2; 0, 3] !![1, 0; 0, 0] = {1} ∧
      pencilSpectrum !![(1 : ℂ), 2; 0, 3] !![0, 1; 0, 0] = ∅ ∧
      pencilSpectrum !![(1 : ℂ), 2; 0, 0] !![1, 0; 0, 0] = Set.univ := by
  have ha : ∀ μ : ℂ, (!![(1 : ℂ), 2; 0, 3] - μ • !![1, 0; 0, 0]).det = 3 * (1 - μ) := fun μ => by
    rw [det_fin_two]
    simp
    ring
  have hb : ∀ μ : ℂ, (!![(1 : ℂ), 2; 0, 3] - μ • !![0, 1; 0, 0]).det = 3 := fun μ => by
    rw [det_fin_two]
    simp
  have hc : ∀ μ : ℂ, (!![(1 : ℂ), 2; 0, 0] - μ • !![1, 0; 0, 0]).det = 0 := fun μ => by
    rw [det_fin_two]
    simp
  refine ⟨?_, ?_, ?_⟩ <;> ext μ
  · rw [Set.mem_singleton_iff, mem_pencilSpectrum_iff_det, ha]
    constructor
    · intro h
      have h1 : (1 : ℂ) - μ = 0 := by
        rcases mul_eq_zero.1 h with h3 | h3
        · norm_num at h3
        · exact h3
      exact (sub_eq_zero.1 h1).symm
    · rintro rfl
      ring
  · rw [mem_pencilSpectrum_iff_det, hb]
    simp
  · rw [mem_pencilSpectrum_iff_det, hc]
    simp

/-- **§7.7.1**: if `0 ≠ λ ∈ λ(A, B)` then `1/λ ∈ λ(B, A)`; and if `B` is nonsingular,
`λ(A, B) = λ(B⁻¹ A, I) = λ(B⁻¹ A)`. -/
theorem pencilSpectrum_inv (A B : Matrix (Fin n) (Fin n) ℂ) :
    (∀ μ : ℂ, μ ≠ 0 → μ ∈ pencilSpectrum A B → μ⁻¹ ∈ pencilSpectrum B A) ∧
      (IsUnit B → pencilSpectrum A B = pencilSpectrum (B⁻¹ * A) 1 ∧
        pencilSpectrum (B⁻¹ * A) 1 = spectrum ℂ (B⁻¹ * A)) :=
  ⟨fun _ hμ h => inv_mem_pencilSpectrum_swap hμ h, fun hB =>
    ⟨by rw [pencilSpectrum_one, pencilSpectrum_eq_spectrum_of_isUnit A hB],
      pencilSpectrum_one _⟩⟩

/-- **(7.7.2), equivalent pencils.** For nonsingular `Q`, `Z` and `A₁ = Q⁻¹ A Z`, `B₁ = Q⁻¹ B Z`,
`λ(A, B) = λ(A₁, B₁)`, and `A x = λ B x ⇔ A₁ y = λ B₁ y` with `x = Z y`. -/
theorem equation_7_7_2 {A B Q Z : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (hZ : IsUnit Z) :
    pencilSpectrum A B = pencilSpectrum (Q⁻¹ * A * Z) (Q⁻¹ * B * Z) ∧
      ∀ (μ : ℂ) (y : Fin n → ℂ),
        (Q⁻¹ * A * Z) *ᵥ y = μ • ((Q⁻¹ * B * Z) *ᵥ y) ↔ A *ᵥ (Z *ᵥ y) = μ • (B *ᵥ (Z *ᵥ y)) := by
  have hQd : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ
  have hQi : IsUnit Q⁻¹ := (isUnit_nonsing_inv_iff).2 hQ
  refine ⟨(pencilSpectrum_mul_mul_of_isUnit A B hQi hZ).symm, fun μ y => ?_⟩
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, (Q⁻¹ * M * Z) *ᵥ y = Q⁻¹ *ᵥ (M *ᵥ (Z *ᵥ y)) :=
    fun M => by simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [key A, key B, ← mulVec_smul]
  constructor
  · intro h
    have h' := congrArg (Q *ᵥ ·) h
    simpa [mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hQd] using h'
  · intro h
    rw [h]

/-! ### §7.7.2 The generalized Schur decomposition -/

/-- **Theorem 7.7.1 (generalized Schur decomposition), existence.** For `A, B ∈ ℂ^{n×n}` there are
unitary `Q`, `Z` with `Qᴴ A Z = T` and `Qᴴ B Z = S` upper triangular (for every pair, regular or
not). -/
theorem theorem_7_7_1 (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q ∈ unitaryGroup (Fin n) ℂ, ∃ Z ∈ unitaryGroup (Fin n) ℂ,
      (star Q * A * Z).IsUpperTriangular ∧ (star Q * B * Z).IsUpperTriangular :=
  exists_generalizedSchur A B

/-- **Theorem 7.7.1, the eigenvalue claims.** With `T = Qᴴ A Z`, `S = Qᴴ B Z` upper triangular
(`Q`, `Z` unitary), `det(A - λB) = det(Q Zᴴ) ∏ (t_ii - λ s_ii)`; if `t_kk = s_kk = 0` for some `k`
then `λ(A, B) = ℂ`; otherwise `λ(A, B) = {t_ii / s_ii : s_ii ≠ 0}`. -/
theorem theorem_7_7_1_spectrum {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hZ : Z ∈ unitaryGroup (Fin n) ℂ)
    (hT : (star Q * A * Z).IsUpperTriangular) (hS : (star Q * B * Z).IsUpperTriangular) :
    (∀ μ : ℂ, (A - μ • B).det =
      (Q * star Z).det * ∏ i, ((star Q * A * Z) i i - μ * (star Q * B * Z) i i)) ∧
    ((∃ k, (star Q * A * Z) k k = 0 ∧ (star Q * B * Z) k k = 0) → pencilSpectrum A B = Set.univ) ∧
    ((¬ ∃ k, (star Q * A * Z) k k = 0 ∧ (star Q * B * Z) k k = 0) →
      pencilSpectrum A B =
        {μ | ∃ i, (star Q * B * Z) i i ≠ 0 ∧ μ = (star Q * A * Z) i i / (star Q * B * Z) i i}) := by
  set T := star Q * A * Z
  set S := star Q * B * Z
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hZZ : Z * star Z = 1 := mem_unitaryGroup_iff.1 hZ
  have hQu : IsUnit (star Q) := (isUnit_iff_isUnit_det _).2
    (isUnit_det_of_left_inverse hQQ)
  have hZu : IsUnit Z := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hZZ)
  have hspec : pencilSpectrum A B = {μ | ∃ i, T i i = μ * S i i} := by
    rw [← pencilSpectrum_eq_of_isUpperTriangular hT hS]
    exact (pencilSpectrum_mul_mul_of_isUnit A B hQu hZu).symm
  refine ⟨fun μ => ?_, fun ⟨k, hk1, hk2⟩ => ?_, fun hno => ?_⟩
  · have hdecomp : A - μ • B = Q * (T - μ • S) * star Z := by
      simp only [T, S, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hZZ, Matrix.mul_one]
    have hup : (T - μ • S).IsUpperTriangular := fun i j hij => by
      simp [Matrix.sub_apply, hT hij, hS hij]
    rw [hdecomp, det_mul, det_mul, det_of_isUpperTriangular hup, det_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [hspec]
    exact Set.eq_univ_of_forall fun μ => ⟨k, by rw [hk1, hk2, mul_zero]⟩
  · rw [hspec]
    ext μ
    constructor
    · rintro ⟨i, hi⟩
      have hSi : S i i ≠ 0 := fun h0 => hno ⟨i, by rw [hi, h0, mul_zero], h0⟩
      exact ⟨i, hSi, by rw [hi, mul_div_cancel_right₀ _ hSi]⟩
    · rintro ⟨i, hSi, rfl⟩
      exact ⟨i, by rw [div_mul_cancel₀ _ hSi]⟩

/-- **Theorem 7.7.2 (generalized real Schur decomposition).** For `A, B ∈ ℝ^{n×n}` there are
orthogonal `Q`, `Z` with `Qᵀ A Z` upper quasi-triangular and `Qᵀ B Z` upper triangular. -/
theorem theorem_7_7_2 (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ,
      (Qᵀ * A * Z).IsQuasiUpperTriangular ∧ (Qᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨Q, hQ, Z, hZ, p, hp, hcard, hA, hB⟩ := exists_generalizedRealSchur A B
  exact ⟨Q, hQ, Z, hZ, ⟨p, hp, hcard, hA⟩, hB⟩

/-! ### §7.7.4 Hessenberg–triangular form -/

/-- **§7.7.4: the Hessenberg–triangular form exists.** For real `A`, `B` there are orthogonal `Q`,
`Z` with `Qᵀ A Z` upper Hessenberg and `Qᵀ B Z` upper triangular (from Theorem 7.7.2: an upper
quasi-triangular matrix is upper Hessenberg). -/
theorem exists_hessenbergTriangular (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ,
      (Qᵀ * A * Z).IsUpperHessenberg ∧ (Qᵀ * B * Z).IsUpperTriangular := by
  obtain ⟨Q, hQ, Z, hZ, hA, hB⟩ := theorem_7_7_2 A B
  exact ⟨Q, hQ, Z, hZ, hA.isUpperHessenberg, hB⟩

/-! ### §7.7.5 Deflation -/

/-- **§7.7.5, the first deflation**: if `a_{k+1,k} = 0` in a Hessenberg–triangular pencil, then
`A - λB = [A₁₁ - λB₁₁, A₁₂ - λB₁₂; 0, A₂₂ - λB₂₂]`, so `det(A - λB)` factors and
`λ(A, B) = λ(A₁₁, B₁₁) ∪ λ(A₂₂, B₂₂)`. -/
theorem pencil_decouple {p q : ℕ} (A₁₁ B₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (A₁₂ B₁₂ : Matrix (Fin p) (Fin q) ℂ) (A₂₂ B₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    (∀ μ : ℂ, (fromBlocks A₁₁ A₁₂ 0 A₂₂ - μ • fromBlocks B₁₁ B₁₂ 0 B₂₂).det =
      (A₁₁ - μ • B₁₁).det * (A₂₂ - μ • B₂₂).det) ∧
    pencilSpectrum (fromBlocks A₁₁ A₁₂ 0 A₂₂) (fromBlocks B₁₁ B₁₂ 0 B₂₂) =
      pencilSpectrum A₁₁ B₁₁ ∪ pencilSpectrum A₂₂ B₂₂ := by
  have hdet : ∀ μ : ℂ, (fromBlocks A₁₁ A₁₂ 0 A₂₂ - μ • fromBlocks B₁₁ B₁₂ 0 B₂₂).det =
      (A₁₁ - μ • B₁₁).det * (A₂₂ - μ • B₂₂).det := fun μ => by
    rw [fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, smul_zero, neg_zero,
      add_zero, det_fromBlocks_zero₂₁]
    simp only [← sub_eq_add_neg]
  refine ⟨hdet, ?_⟩
  ext μ
  simp only [Set.mem_union, mem_pencilSpectrum_iff_det, hdet, mul_eq_zero]

/-! ### §7.7.8 Generalized inverse iteration and deflating subspaces -/

/-- **§7.7.8, generalized inverse iteration.** Solving `(A - μB) z^(k) = B q^(k-1)` is inverse
iteration (7.6.1) for `B⁻¹ A` with the same shift when `B` is nonsingular:
`(A - μB)⁻¹ B = (B⁻¹ A - μ I)⁻¹`. (The book prints the eigenvalue estimate as
`λ^(k) = q^(k)ᴴ A q^(k) / q^(k)ᴴ A q^(k)`, a misprint for `/ q^(k)ᴴ B q^(k)`.) -/
theorem generalizedInverseIteration_eq {A B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B) (μ : ℂ) :
    (A - μ • B)⁻¹ * B = (B⁻¹ * A - μ • 1)⁻¹ := by
  have hBd : IsUnit B.det := (isUnit_iff_isUnit_det B).1 hB
  have hfac : A - μ • B = B * (B⁻¹ * A - μ • 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, mul_nonsing_inv _ hBd, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]
  rw [hfac, Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ hBd, Matrix.mul_one]

/-- **§7.7.8, deflating subspaces from the generalized Schur form.** With `Qᴴ A Z = T` and
`Qᴴ B Z = S` upper triangular, for every `k` `span{A z₀, …, A z_k} ⊆ span{q₀, …, q_k}` and
`span{B z₀, …, B z_k} ⊆ span{q₀, …, q_k}`, so `span{z₀, …, z_k}` is a deflating subspace of
`A - λB` (`{A x + B y : x, y ∈ S}` has dimension at most `dim S`). -/
theorem deflatingSubspace_of_generalizedSchur {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hZ : Z ∈ unitaryGroup (Fin n) ℂ)
    (hT : (star Q * A * Z).IsUpperTriangular) (hS : (star Q * B * Z).IsUpperTriangular)
    (k : Fin n) :
    (Submodule.span ℂ (Set.range fun j : Set.Iic k => A *ᵥ Z.col j) ≤
        Submodule.span ℂ (Set.range fun j : Set.Iic k => Q.col j)) ∧
      (Submodule.span ℂ (Set.range fun j : Set.Iic k => B *ᵥ Z.col j) ≤
        Submodule.span ℂ (Set.range fun j : Set.Iic k => Q.col j)) ∧
      IsDeflatingSubspace A B (Submodule.span ℂ (Set.range fun j : Set.Iic k => Z.col j)) := by
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hZZ : Z * star Z = 1 := mem_unitaryGroup_iff.1 hZ
  have hQu : IsUnit Q := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hQQ)
  have hZu : IsUnit Z := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hZZ)
  have hinv : Q⁻¹ = star Q := Matrix.inv_eq_right_inv hQQ
  exact isDeflatingSubspace_span_cols_of_isUpperTriangular hQu hZu (by rwa [hinv])
    (by rwa [hinv]) k

/-! ### §7.7.9 The polynomial eigenvalue problem -/

/-- **(7.7.5), the companion pencil of a cubic** `P(λ) = A₀ + λ A₁ + λ² A₂ + λ³ A₃`:
`L(λ) = [0 0 A₀; -I 0 A₁; 0 -I A₂] + λ [I 0 0; 0 I 0; 0 0 A₃]`, on the index
`(Fin n ⊕ Fin n) ⊕ Fin n` of the three block rows. -/
def cubicPencil (A₀ A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix ((Fin n ⊕ Fin n) ⊕ Fin n) ((Fin n ⊕ Fin n) ⊕ Fin n) ℂ :=
  fromBlocks (fromBlocks 0 0 (-1) 0) (fromRows A₀ A₁) (fromCols 0 (-1)) A₂ +
    l • fromBlocks 1 0 0 A₃

/-- A function on a sum type vanishes exactly when both of its restrictions do. -/
private theorem sum_elim_eq_zero_iff {α β : Type*} {a : α → ℂ} {b : β → ℂ} :
    Sum.elim a b = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h => ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩,
    ?_⟩
  rintro ⟨rfl, rfl⟩
  exact Sum.elim_zero_zero

/-- The block rows of `L(λ) [u₁; u₂; x]`: `λ u₁ + A₀ x`, `-u₁ + λ u₂ + A₁ x` and
`-u₂ + (A₂ + λ A₃) x`. -/
private theorem cubicPencil_mulVec (A₀ A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℂ) (l : ℂ)
    (u₁ u₂ x : Fin n → ℂ) :
    cubicPencil A₀ A₁ A₂ A₃ l *ᵥ Sum.elim (Sum.elim u₁ u₂) x =
      Sum.elim (Sum.elim (l • u₁ + A₀ *ᵥ x) (-u₁ + l • u₂ + A₁ *ᵥ x))
        (-u₂ + (A₂ + l • A₃) *ᵥ x) := by
  ext ((i | i) | i) <;>
    simp [cubicPencil, add_mulVec, smul_mulVec, fromBlocks_mulVec, fromRows_mulVec,
      fromCols_mulVec, neg_mulVec, one_mulVec] <;> ring

/-- **(7.7.3)–(7.7.5).** For the cubic `P(λ) = A₀ + λ A₁ + λ² A₂ + λ³ A₃` (7.7.4) and its companion
pencil `L(λ)` (7.7.5): `L(λ) [u₁; u₂; x] = 0` forces `P(λ) x = 0` (7.7.3) — the rows give
`u₂ = (A₂ + λ A₃) x`, `u₁ = A₁ x + λ u₂` and `λ u₁ + A₀ x = P(λ) x` (the book's chain writes
`A₀ + …` for `A₀ x + …`); conversely `P(λ) x = 0` gives `L(λ) [u₁; u₂; x] = 0` with these `u₁`,
`u₂`; and the stacked vector is nonzero exactly when `x` is, so `L` and `P` have the same
eigenvalues. -/
theorem equation_7_7_5 (A₀ A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    (∀ u₁ u₂ x : Fin n → ℂ, cubicPencil A₀ A₁ A₂ A₃ l *ᵥ Sum.elim (Sum.elim u₁ u₂) x = 0 →
      (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0) ∧
    (∀ x : Fin n → ℂ, (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0 →
      cubicPencil A₀ A₁ A₂ A₃ l *ᵥ
        Sum.elim (Sum.elim (A₁ *ᵥ x + l • (A₂ + l • A₃) *ᵥ x) ((A₂ + l • A₃) *ᵥ x)) x = 0) ∧
    ((∃ v ≠ 0, cubicPencil A₀ A₁ A₂ A₃ l *ᵥ v = 0) ↔
      ∃ x ≠ 0, (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0) := by
  have hrows : ∀ u₁ u₂ x : Fin n → ℂ,
      cubicPencil A₀ A₁ A₂ A₃ l *ᵥ Sum.elim (Sum.elim u₁ u₂) x = 0 →
        u₂ = (A₂ + l • A₃) *ᵥ x ∧ u₁ = l • u₂ + A₁ *ᵥ x ∧ A₀ *ᵥ x = -(l • u₁) := by
    intro u₁ u₂ x h
    rw [cubicPencil_mulVec, sum_elim_eq_zero_iff, sum_elim_eq_zero_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨neg_add_eq_zero.1 h3, neg_add_eq_zero.1 (by rw [← add_assoc]; exact h2),
      (neg_eq_of_add_eq_zero_right h1).symm⟩
  have hP : ∀ u₁ u₂ x : Fin n → ℂ,
      cubicPencil A₀ A₁ A₂ A₃ l *ᵥ Sum.elim (Sum.elim u₁ u₂) x = 0 →
        (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0 := by
    intro u₁ u₂ x h
    obtain ⟨e3, e2, e1⟩ := hrows u₁ u₂ x h
    simp only [add_mulVec, smul_mulVec]
    rw [e1, e2, e3]
    simp only [add_mulVec, smul_mulVec]
    module
  have hL : ∀ x : Fin n → ℂ, (A₀ + l • A₁ + l ^ 2 • A₂ + l ^ 3 • A₃) *ᵥ x = 0 →
      cubicPencil A₀ A₁ A₂ A₃ l *ᵥ
        Sum.elim (Sum.elim (A₁ *ᵥ x + l • (A₂ + l • A₃) *ᵥ x) ((A₂ + l • A₃) *ᵥ x)) x = 0 := by
    intro x h
    rw [cubicPencil_mulVec, sum_elim_eq_zero_iff, sum_elim_eq_zero_iff]
    refine ⟨⟨?_, ?_⟩, neg_add_cancel _⟩
    · rw [← h]
      simp only [add_mulVec, smul_mulVec]
      module
    · abel
  refine ⟨hP, hL, ⟨?_, ?_⟩⟩
  · rintro ⟨v, hv, h⟩
    have hv' : v = Sum.elim (Sum.elim (fun i => v (Sum.inl (Sum.inl i)))
        (fun i => v (Sum.inl (Sum.inr i)))) (fun i => v (Sum.inr i)) := by
      ext ((i | i) | i) <;> rfl
    rw [hv'] at h hv
    refine ⟨_, fun hx => hv ?_, hP _ _ _ h⟩
    obtain ⟨e3, e2, -⟩ := hrows _ _ _ h
    rw [hx, mulVec_zero] at e3
    rw [e3, smul_zero, hx, mulVec_zero, add_zero] at e2
    rw [e2, e3, hx, Sum.elim_zero_zero, Sum.elim_zero_zero]
  · rintro ⟨x, hx, h⟩
    exact ⟨_, fun h' => hx (funext fun i => congrFun h' (Sum.inr i)), hL x h⟩

end GolubVanLoan.Chapter07
