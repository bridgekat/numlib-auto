import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.GeneralizedSchur
import Mathlib.Data.Matrix.Composition
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter07.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section05

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

The Hessenberg–triangular reduction (`algorithm_7_7_1`), the zero chase of §7.7.5 (`qzZeroChase`),
the QZ step (`algorithm_7_7_2`, with `qzShiftVector` and the loop body `qzStep`) and the QZ
algorithm (`algorithm_7_7_3`, one pass `qzPass`, the deflation sweep `qzDeflate`) are monadic
programs with a rounding hook (conventions 1–14 of `NumlibSurface/GolubVanLoan`), calling chapter
5's Householder QR (`algorithm_5_2_1`), `houseOn`, `householderApplyLeft/Right`, `algorithm_5_1_3`
(`givens`) and `givensApplyLeft/Right`. The arrays are carried in `QZArrays` (`A`, `B` and the
accumulated `Q`, `Z`); the QZ step and the zero chase act on a block `p, …, r` of consecutive
indices of the whole arrays (the book's `diag(I_p, ·, I_q)` updates). A Householder matrix acting
on a row is `house` on the reversed index list. `algorithm_7_7_1_spec` and `qzZeroChase_spec` are
the exact semantics, through the invariant `QZArrays.IsEquiv` (`(A, B) = (Qᵀ A₀ Z, Qᵀ B₀ Z)`).
The QZ step's exact semantics on a block (`algorithm_7_7_2_block`) rests on the bulge-chasing
invariant `QZStepInv` (the bulge of `A` below the subdiagonal, of `B` below the diagonal); on the
whole pencil it is a Francis step on `A B⁻¹` (`algorithm_7_7_2_spec`), by the implicit Q theorem
and the first column `(M - aI)(M - bI) e₁` computed by `qzShiftVector`. The QZ algorithm's exact
semantics (`algorithm_7_7_3_spec`) is a statement with a perturbation: its deflation sweep is
Algorithm 7.5.2's (`qzDeflate_pure_eq`, `qrDeflate_spec`), the zero chase and the QZ steps are
exact equivalences.

`equation_7_7_6` states the linearization on `Fin d × Fin n` through `Matrix.comp` of block
matrices (`linearizationS`, `linearizationDiag`, `linearizationT`, `linearizationPencil`).

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

/-- **The working arrays of the QZ programs**: the pencil `(A, B)` being overwritten by
`(Qᵀ A Z, Qᵀ B Z)` and the accumulated orthogonal factors `Q`, `Z` (the book's "if `Q` and `Z` are
desired"). -/
structure QZArrays (n : ℕ) where
  /-- The array overwritten by `Qᵀ A Z`. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The array overwritten by `Qᵀ B Z`. -/
  B : Matrix (Fin n) (Fin n) ℝ
  /-- The accumulated left factor `Q`. -/
  Q : Matrix (Fin n) (Fin n) ℝ
  /-- The accumulated right factor `Z`. -/
  Z : Matrix (Fin n) (Fin n) ℝ

section Programs

open GolubVanLoan.Chapter05

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **One rotation pair of Algorithm 7.7.1** (row `i ≥ j + 2`, `k = i - 1`, 0-based):
```
[c, s] = givens(A(i-1, j), A(i, j))
A(i-1:i, j:n) = [c s; -s c]ᵀ A(i-1:i, j:n)
B(i-1:i, i-1:n) = [c s; -s c]ᵀ B(i-1:i, i-1:n)
[c, s] = givens(-B(i, i), B(i, i-1))
B(1:i, i-1:i) = B(1:i, i-1:i) [c s; -s c]
A(1:n, i-1:i) = A(1:n, i-1:i) [c s; -s c]
```
with the rotations accumulated into `Q` (on the right, all rows) and `Z` (on the right, all rows).
The negation `-B(i, i)` is exact (convention 1). -/
noncomputable def hessTriStep (j i : Fin n) (st : QZArrays n) : M (QZArrays n) := do
  let k : Fin n := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  let g ← algorithm_5_1_3 rnd (st.A k j) (st.A i j)
  let A ← givensApplyLeft rnd k i g.1 g.2 (indexFrom n j) st.A
  let B ← givensApplyLeft rnd k i g.1 g.2 (indexFrom n k) st.B
  let Q ← givensApplyRight rnd k i g.1 g.2 (List.finRange n) st.Q
  let h ← algorithm_5_1_3 rnd (-B i i) (B i k)
  let B ← givensApplyRight rnd k i h.1 h.2 ((List.finRange n).filter fun r => (r : ℕ) ≤ i) B
  let A ← givensApplyRight rnd k i h.1 h.2 (List.finRange n) A
  let Z ← givensApplyRight rnd k i h.1 h.2 (List.finRange n) st.Z
  pure ⟨A, B, Q, Z⟩

/-- **Algorithm 7.7.1 (Hessenberg–Triangular Reduction)**: "Given `A` and `B` in `ℝ^{n×n}`, the
following algorithm overwrites `A` with an upper Hessenberg matrix `QᵀAZ` and `B` with an upper
triangular matrix `QᵀBZ` where both `Q` and `Z` are orthogonal":
```
Compute the factorization B = QR using Algorithm 5.2.1 and overwrite A with QᵀA and B with QᵀB.
for j = 1:n-2
    for i = n:-1:j+2
        (the rotation pair of `hessTriStep`)
    end
end
```
`QᵀA` applies the reflector data of Algorithm 5.2.1 — the stored vectors with the returned `β`
(convention 13), never rebuilt — to `A` in order (`householderApplyLeft`, rows the support of
each vector, all columns), and `QᵀB = R` is the upper triangular part of the overwritten array.
`Q` is accumulated from the same data (`backwardAccumulation`) and then updated with every row
rotation, `Z` starts at `I` and is updated with every column rotation; the program returns
`(QᵀAZ, QᵀBZ, Q, Z)`. The inner loop `i = n:-1:j+2` is the reversed index list with the guard
`j + 2 ≤ i`. -/
noncomputable def algorithm_7_7_1 (A B : Matrix (Fin n) (Fin n) ℝ) : M (QZArrays n) := do
  let qr ← algorithm_5_2_1 rnd B
  let A ← (List.finRange n).foldlM (fun A j =>
    householderApplyLeft rnd (storedHouseholderVec qr.1 j) (qr.2 j) (indexFrom n j)
      (List.finRange n) A) A
  let Q ← backwardAccumulation rnd (storedReflectors qr.1 qr.2)
  (List.finRange n).foldlM (fun st (j : Fin n) =>
    (List.finRange n).reverse.foldlM (fun st (i : Fin n) =>
      if (j : ℕ) + 2 ≤ i then hessTriStep rnd j i st else pure st) st)
    ⟨A, upperPart qr.1, Q, 1⟩

end Programs

section Exact

open GolubVanLoan.Chapter05

/-- A loop invariant indexed by the position in the list. -/
theorem foldl_induction_getElem {α S : Type*} (l : List α) (f : S → α → S) (P : ℕ → S → Prop)
    (s : S) (h0 : P 0 s) (h : ∀ (p : ℕ) (hp : p < l.length) (s : S), P p s → P (p + 1) (f s l[p])) :
    P l.length (l.foldl f s) := by
  induction l generalizing P s with
  | nil => exact h0
  | cons a l ih =>
    rw [List.foldl_cons, List.length_cons]
    exact ih (fun p => P (p + 1)) (f s a) (h 0 (by simp) s h0) fun p hp s hs =>
      h (p + 1) (by simp; omega) s hs

/-- The entries of `G(i, k, θ)ᵀ A`. -/
theorem givensRotation_transpose_mul_apply {m p : ℕ} {i k : Fin m} (hik : i ≠ k) (c s : ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (r : Fin m) (q : Fin p) :
    ((givensRotation i k c s)ᵀ * A) r q =
      if r = i then c * A i q - s * A k q else if r = k then s * A i q + c * A k q
        else A r q := by
  have h : ((givensRotation i k c s)ᵀ * A) r q =
      ((givensRotation i k c s)ᵀ *ᵥ fun t => A t q) r := rfl
  rw [h, givensRotation_transpose_mulVec_apply hik]

/-- The entries of `A G(i, k, θ)`. -/
theorem mul_givensRotation_apply {m p : ℕ} {i k : Fin p} (hik : i ≠ k) (c s : ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (r : Fin m) (q : Fin p) :
    (A * givensRotation i k c s) r q =
      if q = i then c * A r i - s * A r k else if q = k then s * A r i + c * A r k
        else A r q := by
  have h : (A * givensRotation i k c s) r q = ((givensRotation i k c s)ᵀ *ᵥ A r) q := by
    rw [mulVec_transpose]; rfl
  rw [h, givensRotation_transpose_mulVec_apply hik]

/-- The row update on a column list is the full product `G(i, k, θ)ᵀ A` when the omitted
columns vanish in the rows `i`, `k`. -/
theorem givensApplyLeft_eq_mul {m p : ℕ} {i k : Fin m} (hik : i ≠ k) (c s : ℝ)
    {cols : List (Fin p)} (hcols : cols.Nodup) {A : Matrix (Fin m) (Fin p) ℝ}
    (hA : ∀ q, q ∉ cols → A i q = 0 ∧ A k q = 0) :
    Id.run (givensApplyLeft pure i k c s cols A) = (givensRotation i k c s)ᵀ * A := by
  rw [givensApplyLeft_spec hik c s hcols]
  ext r q
  rw [of_apply]
  split_ifs with hq
  · rfl
  · rw [givensRotation_transpose_mul_apply hik, (hA q hq).1, (hA q hq).2]
    split_ifs with h1 h2
    · subst h1; rw [(hA q hq).1]; ring
    · subst h2; rw [(hA q hq).2]; ring
    · rfl

/-- The column update on a row list is the full product `A G(i, k, θ)` when the omitted rows
vanish in the columns `i`, `k`. -/
theorem givensApplyRight_eq_mul {m p : ℕ} {i k : Fin p} (hik : i ≠ k) (c s : ℝ)
    {rows : List (Fin m)} (hrows : rows.Nodup) {A : Matrix (Fin m) (Fin p) ℝ}
    (hA : ∀ r, r ∉ rows → A r i = 0 ∧ A r k = 0) :
    Id.run (givensApplyRight pure i k c s rows A) = A * givensRotation i k c s := by
  rw [givensApplyRight_spec hik c s hrows]
  ext r q
  rw [of_apply]
  split_ifs with hr
  · rfl
  · rw [mul_givensRotation_apply hik, (hA r hr).1, (hA r hr).2]
    split_ifs with h1 h2
    · subst h1; rw [(hA r hr).1]; ring
    · subst h2; rw [(hA r hr).2]; ring
    · rfl

/-- The exact output of `givens`. -/
theorem givens_exact (a b : ℝ) :
    ∃ c s : ℝ, Id.run (algorithm_5_1_3 pure a b) = (c, s) ∧ c ^ 2 + s ^ 2 = 1 ∧
      s * a + c * b = 0 := by
  obtain ⟨h1, h2, -⟩ := algorithm_5_1_3_spec a b
  exact ⟨_, _, rfl, h1, h2⟩

end Exact

section HessTri

open GolubVanLoan.Chapter05

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- The invariant of the QZ programs: `(A, B) = (Qᵀ A₀ Z, Qᵀ B₀ Z)` with `Q`, `Z` orthogonal and
`B` upper triangular. -/
def QZArrays.IsEquiv (A₀ B₀ : Matrix (Fin n) (Fin n) ℝ) (st : QZArrays n) : Prop :=
  st.Q ∈ orthogonalGroup (Fin n) ℝ ∧ st.Z ∈ orthogonalGroup (Fin n) ℝ ∧
    st.A = st.Qᵀ * A₀ * st.Z ∧ st.B = st.Qᵀ * B₀ * st.Z

/-- Columns `< j` of `A` are Hessenberg and column `j` vanishes below row `b`. -/
def HessCols (A : Matrix (Fin n) (Fin n) ℝ) (j b : ℕ) : Prop :=
  ∀ r c : Fin n, (c : ℕ) + 1 < r → ((c : ℕ) < j ∨ ((c : ℕ) = j ∧ b < r)) → A r c = 0

/-- A row rotation `G(i, k, θ)ᵀ` applied to both arrays and accumulated into `Q` keeps the
equivalence. -/
theorem QZArrays.IsEquiv.rot_left {st : QZArrays n} (h : st.IsEquiv A₀ B₀) {i k : Fin n}
    (hik : i ≠ k) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (⟨(givensRotation i k c s)ᵀ * st.A, (givensRotation i k c s)ᵀ * st.B,
      st.Q * givensRotation i k c s, st.Z⟩ : QZArrays n).IsEquiv A₀ B₀ := by
  obtain ⟨hQ, hZ, hA, hB⟩ := h
  refine ⟨Submonoid.mul_mem _ hQ (givensRotation_mem_orthogonalGroup hik hcs), hZ, ?_, ?_⟩ <;>
    simp only [hA, hB, transpose_mul, Matrix.mul_assoc]

/-- A column rotation `G(i, k, θ)` applied to both arrays and accumulated into `Z` keeps the
equivalence. -/
theorem QZArrays.IsEquiv.rot_right {st : QZArrays n} (h : st.IsEquiv A₀ B₀) {i k : Fin n}
    (hik : i ≠ k) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (⟨st.A * givensRotation i k c s, st.B * givensRotation i k c s, st.Q,
      st.Z * givensRotation i k c s⟩ : QZArrays n).IsEquiv A₀ B₀ := by
  obtain ⟨hQ, hZ, hA, hB⟩ := h
  refine ⟨hQ, Submonoid.mul_mem _ hZ (givensRotation_mem_orthogonalGroup hik hcs), ?_, ?_⟩ <;>
    simp only [hA, hB, Matrix.mul_assoc]

/-- One rotation pair of Algorithm 7.7.1 keeps the equivalence and the triangular `B`, and
zeroes `A(i, j)`. -/
theorem hessTriStep_spec {st : QZArrays n} (h : st.IsEquiv A₀ B₀)
    (hB : st.B.IsUpperTriangular) {j i : Fin n} (hji : (j : ℕ) + 2 ≤ i)
    (hA : HessCols st.A j i) :
    (Id.run (hessTriStep pure j i st)).IsEquiv A₀ B₀ ∧
      (Id.run (hessTriStep pure j i st)).B.IsUpperTriangular ∧
      HessCols (Id.run (hessTriStep pure j i st)).A j (i - 1) := by
  set k : Fin n := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ with hk
  have hki : k ≠ i := fun e => by
    have := congrArg Fin.val e; simp [k] at this; omega
  have hkv : (k : ℕ) = i - 1 := rfl
  have hBv : ∀ r c : Fin n, (c : ℕ) < r → st.B r c = 0 := fun r c h => hB (Fin.lt_def.2 h)
  obtain ⟨c, s, hg, hcs, hz⟩ := givens_exact (st.A k j) (st.A i j)
  set A₁ := (givensRotation k i c s)ᵀ * st.A with hA₁
  set B₁ := (givensRotation k i c s)ᵀ * st.B with hB₁
  obtain ⟨c', s', hg', hcs', hz'⟩ := givens_exact (-B₁ i i) (B₁ i k)
  have hA1 : Id.run (givensApplyLeft pure k i c s (indexFrom n j) st.A) = A₁ := by
    refine givensApplyLeft_eq_mul hki c s (nodup_indexFrom n j) fun q hq => ?_
    rw [mem_indexFrom, not_le] at hq
    exact ⟨hA k q (by omega) (Or.inl hq), hA i q (by omega) (Or.inl hq)⟩
  have hB1 : Id.run (givensApplyLeft pure k i c s (indexFrom n k) st.B) = B₁ := by
    refine givensApplyLeft_eq_mul hki c s (nodup_indexFrom n k) fun q hq => ?_
    rw [mem_indexFrom, not_le] at hq
    exact ⟨hBv k q hq, hBv i q (by omega)⟩
  have hB2 : Id.run (givensApplyRight pure k i c' s'
      ((List.finRange n).filter fun r => (r : ℕ) ≤ i) B₁) = B₁ * givensRotation k i c' s' := by
    refine givensApplyRight_eq_mul hki c' s' ((List.nodup_finRange n).filter _) fun r hr => ?_
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, not_le] at hr
    have hrk : r ≠ k := fun e => by rw [e] at hr; omega
    have hri : r ≠ i := fun e => by rw [e] at hr; omega
    rw [hB₁, givensRotation_transpose_mul_apply hki, givensRotation_transpose_mul_apply hki]
    simp only [hrk, hri, ↓reduceIte]
    exact ⟨hBv r k (by omega), hBv r i hr⟩
  have hrun : Id.run (hessTriStep pure j i st) =
      ⟨A₁ * givensRotation k i c' s', B₁ * givensRotation k i c' s',
        st.Q * givensRotation k i c s, st.Z * givensRotation k i c' s'⟩ := by
    simp only [hessTriStep, Id.run_bind, Id.run_pure]
    rw [hg, hA1, hB1]
    simp only
    rw [hg', hB2, givensApplyRight_spec_of_forall_mem hki _ _ (List.nodup_finRange n)
      List.mem_finRange, givensApplyRight_spec_of_forall_mem hki _ _ (List.nodup_finRange n)
      List.mem_finRange, givensApplyRight_spec_of_forall_mem hki _ _ (List.nodup_finRange n)
      List.mem_finRange]
  rw [hrun]
  refine ⟨(h.rot_left hki hcs).rot_right hki hcs', ?_, ?_⟩
  · intro r p hpr
    have hpr' : (p : ℕ) < r := Fin.lt_def.1 hpr
    change (B₁ * givensRotation k i c' s') r p = 0
    have hB₁e : ∀ r' q, r' ≠ k → r' ≠ i → B₁ r' q = st.B r' q := fun r' q h1 h2 => by
      rw [hB₁, givensRotation_transpose_mul_apply hki]
      simp [h1, h2]
    rw [mul_givensRotation_apply hki]
    by_cases hpk : p = k
    · have hkr : (k : ℕ) < r := by rw [← hpk]; exact hpr'
      have hrk : r ≠ k := fun e => by rw [e] at hkr; omega
      simp only [hpk, ↓reduceIte]
      by_cases hri : r = i
      · rw [hri]
        linear_combination hz'
      · have hir : (i : ℕ) < r := by
          have : (r : ℕ) ≠ i := fun e => hri (Fin.ext e)
          omega
        rw [hB₁e r k hrk hri, hB₁e r i hrk hri, hBv r k hkr, hBv r i hir]
        ring
    · by_cases hpi : p = i
      · have hir : (i : ℕ) < r := by rw [← hpi]; exact hpr'
        have hrk : r ≠ k := fun e => by rw [e] at hir; omega
        have hri : r ≠ i := fun e => by rw [e] at hir; omega
        rw [hB₁e r k hrk hri, hB₁e r i hrk hri, hBv r k (by omega), hBv r i hir]
        simp [hpi, hki.symm]
      · simp only [hpk, hpi, ↓reduceIte]
        have hpk' : (p : ℕ) ≠ k := fun e => hpk (Fin.ext e)
        have hpi' : (p : ℕ) ≠ i := fun e => hpi (Fin.ext e)
        by_cases hrk : r = k
        · have h1 : st.B k p = 0 := hBv k p (by rw [← hrk]; exact hpr')
          have h2 : st.B i p = 0 := hBv i p (by
            have : (p : ℕ) < k := by rw [← hrk]; exact hpr'
            omega)
          rw [hrk, hB₁, givensRotation_transpose_mul_apply hki]
          simp [h1, h2]
        · by_cases hri : r = i
          · have h2 : st.B i p = 0 := hBv i p (by rw [← hri]; exact hpr')
            have h1 : st.B k p = 0 := hBv k p (by
              have : (p : ℕ) < i := by rw [← hri]; exact hpr'
              omega)
            rw [hri, hB₁, givensRotation_transpose_mul_apply hki]
            simp [h1, h2, hki.symm]
          · rw [hB₁e r p hrk hri]
            exact hBv r p hpr'
  · intro r q hqr hq
    change (A₁ * givensRotation k i c' s') r q = 0
    have hqk : q ≠ k := fun e => by rw [e] at hq; omega
    have hqi : q ≠ i := fun e => by rw [e] at hq; omega
    rw [mul_givensRotation_apply hki]
    simp only [hqk, hqi, ↓reduceIte, hA₁]
    rw [givensRotation_transpose_mul_apply hki]
    by_cases hrk : r = k
    · subst hrk
      have hq' : (q : ℕ) < j := by omega
      simp [hA _ q (by omega) (Or.inl hq'), hA i q (by omega) (Or.inl hq')]
    · by_cases hri : r = i
      · subst hri
        simp only [hrk, ↓reduceIte]
        rcases hq with hq' | ⟨hq', -⟩
        · simp [hA _ q (by omega) (Or.inl hq'), hA k q (by omega) (Or.inl hq')]
        · have hqj : q = j := Fin.ext hq'
          subst hqj
          linarith
      · simp only [hrk, hri, ↓reduceIte]
        refine hA r q hqr ?_
        rcases hq with hq' | ⟨hq', hr'⟩
        · exact Or.inl hq'
        · refine Or.inr ⟨hq', ?_⟩
          rcases lt_or_gt_of_ne (fun e : (r : ℕ) = i => hri (Fin.ext e)) with h1 | h1
          · exfalso; apply hrk; ext; simp [k]; omega
          · exact h1


/-- `HessCols` is monotone in the row bound. -/
theorem HessCols.mono {A : Matrix (Fin n) (Fin n) ℝ} {j b b' : ℕ} (h : HessCols A j b)
    (hb : b ≤ b') : HessCols A j b' := fun r c hrc hc =>
  h r c hrc (hc.imp_right fun ⟨h1, h2⟩ => ⟨h1, lt_of_le_of_lt hb h2⟩)

/-- A column cleared below its subdiagonal extends the Hessenberg columns by one. -/
theorem HessCols.succ {A : Matrix (Fin n) (Fin n) ℝ} {j : ℕ} (h : HessCols A j (j + 1)) :
    HessCols A (j + 1) (n - 1) := fun r c hrc hc => by
  rcases hc with hc | ⟨-, hr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
    · exact h r c hrc (Or.inl hc)
    · exact h r c hrc (Or.inr ⟨hc, by omega⟩)
  · exact absurd r.isLt (by omega)

/-- The inner loop of Algorithm 7.7.1 for column `j`. -/
theorem hessTri_inner_spec {st : QZArrays n} (h : st.IsEquiv A₀ B₀)
    (hB : st.B.IsUpperTriangular) (j : Fin n) (hA : HessCols st.A j (n - 1)) :
    let st' := Id.run ((List.finRange n).reverse.foldlM (fun st (i : Fin n) =>
      if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st) st)
    st'.IsEquiv A₀ B₀ ∧ st'.B.IsUpperTriangular ∧ HessCols st'.A (j + 1) (n - 1) := by
  intro st'
  have key := foldl_induction_getElem (List.finRange n).reverse
    (fun st (i : Fin n) => Id.run (if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st))
    (fun q st => st.IsEquiv A₀ B₀ ∧ st.B.IsUpperTriangular ∧
      HessCols st.A j (max (n - 1 - q) (j + 1))) st
    ⟨h, hB, hA.mono (by omega)⟩ (by
      intro q hq s ⟨hs, hsB, hsA⟩
      have hq' : q < n := by simpa using hq
      have hval : (((List.finRange n).reverse)[q] : ℕ) = n - 1 - q := by
        simp [List.getElem_reverse]
      by_cases hji : (j : ℕ) + 2 ≤ ((List.finRange n).reverse)[q]
      · simp only [hji, ↓reduceIte]
        rw [hval] at hji
        have hmax : max (n - 1 - q) (j + 1) = ((List.finRange n).reverse)[q] := by
          rw [hval]; omega
        obtain ⟨h1, h2, h3⟩ := hessTriStep_spec hs hsB (by rw [hval]; exact hji) (hmax ▸ hsA)
        refine ⟨h1, h2, h3.mono ?_⟩
        rw [hval]
        omega
      · simp only [hji, ↓reduceIte, Id.run_pure]
        rw [hval] at hji
        exact ⟨hs, hsB, hsA.mono (by omega)⟩)
  have hst' : st' = List.foldl
      (fun st (i : Fin n) => Id.run (if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st))
      st (List.finRange n).reverse := by
    simp only [st', List.idRun_foldlM]
  rw [hst']
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨h1, h2, HessCols.succ (h3.mono ?_)⟩
  simp only [List.length_reverse, List.length_finRange]
  omega

/-- **Algorithm 7.7.1, exact semantics**: `(A', B', Q, Z) = Id.run (algorithm_7_7_1 pure A B)` has
`Q`, `Z` orthogonal, `A' = Qᵀ A Z` upper Hessenberg and `B' = Qᵀ B Z` upper triangular. -/
theorem algorithm_7_7_1_spec (A B : Matrix (Fin n) (Fin n) ℝ) :
    (Id.run (algorithm_7_7_1 pure A B)).Q ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (algorithm_7_7_1 pure A B)).Z ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (algorithm_7_7_1 pure A B)).A =
        (Id.run (algorithm_7_7_1 pure A B)).Qᵀ * A * (Id.run (algorithm_7_7_1 pure A B)).Z ∧
      (Id.run (algorithm_7_7_1 pure A B)).B =
        (Id.run (algorithm_7_7_1 pure A B)).Qᵀ * B * (Id.run (algorithm_7_7_1 pure A B)).Z ∧
      (Id.run (algorithm_7_7_1 pure A B)).A.IsUpperHessenberg ∧
      (Id.run (algorithm_7_7_1 pure A B)).B.IsUpperTriangular := by
  set qr := Id.run (algorithm_5_2_1 pure B) with hqr
  have hQR := (algorithm_5_2_1_spec le_rfl B).1
  rw [← hqr] at hQR
  set Q₀ := factoredQ qr.2 qr.1 with hQ₀
  have hQ₀o : Q₀ ∈ orthogonalGroup (Fin n) ℝ := hQR.mem_unitaryGroup
  have hQ₀t : Q₀ᵀ * Q₀ = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hQ₀o
  have hA₁ : Id.run ((List.finRange n).foldlM (fun A j =>
      householderApplyLeft pure (storedHouseholderVec qr.1 j) (qr.2 j) (indexFrom n j)
        (List.finRange n) A) A) = Q₀ᵀ * A := by
    rw [List.idRun_foldlM]
    have hf : (fun (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) =>
        Id.run (householderApplyLeft pure (storedHouseholderVec qr.1 j) (qr.2 j) (indexFrom n j)
          (List.finRange n) A)) = fun A j =>
          (1 - qr.2 j • vecMulVec (storedHouseholderVec qr.1 j) (storedHouseholderVec qr.1 j)) *
            A := by
      funext A j
      exact householderApplyLeft_spec_of_forall_mem (nodup_indexFrom n j) (List.nodup_finRange n)
        List.mem_finRange (fun i hi => storedHouseholderVec_eq_zero qr.1 j hi) _ A
    rw [hf, foldl_mul_eq_transpose_prod_mul _
      (fun j => transpose_one_sub_smul_vecMulVec _ _),
      hQ₀, factoredQ_eq_prod]
  have hQ : Id.run (backwardAccumulation pure (storedReflectors qr.1 qr.2)) = Q₀ :=
    backwardAccumulation_spec _
  have hR : upperPart qr.1 = Q₀ᵀ * B := by
    rw [← hQR.mul_eq, ← Matrix.mul_assoc, hQ₀t, Matrix.one_mul]
  set st₀ : QZArrays n := ⟨Q₀ᵀ * A, upperPart qr.1, Q₀, 1⟩ with hst₀
  have h0 : st₀.IsEquiv A B := ⟨hQ₀o, one_mem _, by simp [st₀], by simp [st₀, hR]⟩
  have h0B : st₀.B.IsUpperTriangular := fun i j hij => hQR.apply_eq_zero i j hij
  have hrun : Id.run (algorithm_7_7_1 pure A B) = List.foldl (fun st (j : Fin n) =>
      Id.run ((List.finRange n).reverse.foldlM (fun st (i : Fin n) =>
        if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st) st)) st₀
        (List.finRange n) := by
    simp only [algorithm_7_7_1, Id.run_bind]
    rw [← hqr, hA₁, hQ, List.idRun_foldlM]
  have key := foldl_induction_getElem (List.finRange n) (fun st (j : Fin n) =>
      Id.run ((List.finRange n).reverse.foldlM (fun st (i : Fin n) =>
        if (j : ℕ) + 2 ≤ i then hessTriStep pure j i st else pure st) st))
    (fun p st => st.IsEquiv A B ∧ st.B.IsUpperTriangular ∧ HessCols st.A p (n - 1)) st₀
    ⟨h0, h0B, fun r c _ hc => by rcases hc with hc | ⟨hc, hr⟩ <;> omega⟩ (by
      intro p hp s ⟨hs, hsB, hsA⟩
      have hv : (((List.finRange n)[p]) : ℕ) = p := by simp
      obtain ⟨h1, h2, h3⟩ := hessTri_inner_spec hs hsB ((List.finRange n)[p])
        (by rw [hv]; exact hsA)
      have e : p + 1 = ((List.finRange n)[p] : ℕ) + 1 := by rw [hv]
      exact ⟨h1, h2, by rw [e]; exact h3⟩)
  rw [hrun]
  obtain ⟨⟨hQo, hZo, hAe, hBe⟩, hBt, hAh⟩ := key
  refine ⟨hQo, hZo, hAe, hBe, fun r c ⟨k, hck, hkr⟩ => hAh r c ?_ (Or.inl ?_), hBt⟩
  · have := Fin.lt_def.1 hck; have := Fin.lt_def.1 hkr; omega
  · simp

end HessTri

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

section Programs

open GolubVanLoan.Chapter05

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- A column rotation in the columns `(l, m)` zeroing `A(t, l)`: `[c, s] = givens(-A(t, m),
A(t, l))` (the negation exact) and `A = A G`, `B = B G`, `Z = Z G` for
`G = G(l, m, θ)` on all rows — the step of Algorithm 7.7.1 that restores `B`, here zeroing an
entry of `A`. -/
noncomputable def qzColumnZero (l m t : Fin n) (st : QZArrays n) : M (QZArrays n) := do
  let g ← algorithm_5_1_3 rnd (-st.A t m) (st.A t l)
  let A ← givensApplyRight rnd l m g.1 g.2 (List.finRange n) st.A
  let B ← givensApplyRight rnd l m g.1 g.2 (List.finRange n) st.B
  let Z ← givensApplyRight rnd l m g.1 g.2 (List.finRange n) st.Z
  pure ⟨A, B, st.Q, Z⟩

/-- One step of the zero chase of §7.7.5: the row rotation `Q_{j,j+1}` in the rows `(j, j+1)`
that zeroes `b_{j+1,j+1}` (`[c, s] = givens(b_{j,j+1}, b_{j+1,j+1})`, applied to `A`, `B` on all
columns and to `Q`), then, if `j` is not the first index `p` of the block, the column rotation
`Z_{j-1,j}` that zeroes the fill-in `a_{j+1,j-1}`. -/
noncomputable def qzZeroChaseStep (p : ℕ) (j j₁ : Fin n) (st : QZArrays n) : M (QZArrays n) := do
  let g ← algorithm_5_1_3 rnd (st.B j j₁) (st.B j₁ j₁)
  let A ← givensApplyLeft rnd j j₁ g.1 g.2 (List.finRange n) st.A
  let B ← givensApplyLeft rnd j j₁ g.1 g.2 (List.finRange n) st.B
  let Q ← givensApplyRight rnd j j₁ g.1 g.2 (List.finRange n) st.Q
  if p < (j : ℕ) then
    qzColumnZero rnd ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ j j₁ ⟨A, B, Q, st.Z⟩
  else pure ⟨A, B, Q, st.Z⟩

/-- **§7.7.5, zero chasing**: "if `b_kk = 0` for some `k`, then it is possible to introduce a zero
in `A`'s `(n, n-1)` position and thereby deflate … The zero on `B`'s diagonal can be 'pushed down'
to the `(n, n)` position": on the block of consecutive indices `p, …, r` (the book's display is
`p = 0`, `r = n - 1`; Algorithm 7.7.3 runs it on its unreduced block), with the zero at `k`: for
`j = k, …, r - 1` the rotations `Q_{j,j+1}ᵀ` (zeroing `b_{j+1,j+1}`) and, for `j > p`, `Z_{j-1,j}`
(zeroing the fill-in `a_{j+1,j-1}`); finally `Z_{r-1,r}`, zeroing `a_{r,r-1}`. All rotations are
applied to the whole arrays and accumulated into `Q` and `Z`. -/
noncomputable def qzZeroChase (p k r : ℕ) (st : QZArrays n) : M (QZArrays n) := do
  let st ← (List.finRange n).foldlM (fun st (j : Fin n) =>
    if h : k ≤ (j : ℕ) ∧ (j : ℕ) < r ∧ r < n then
      qzZeroChaseStep rnd p j ⟨(j : ℕ) + 1, by omega⟩ st
    else pure st) st
  if h : p < r ∧ r < n then
    qzColumnZero rnd ⟨r - 1, by omega⟩ ⟨r, h.2⟩ ⟨r, h.2⟩ st
  else pure st

end Programs

/-! ### §7.7.6 The QZ step -/

/-- The entry `(i, j)` of a matrix read on natural indices (a copy; `0` out of range). The QZ
programs address the neighbours of a block's corners with it. -/
def qzEntry (A : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) : ℝ :=
  if h : i < n ∧ j < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The state of the QZ step's loop: the arrays, the reflector data applied so far on each side
(convention 13) and the current `x, y, z`. -/
structure QZStepState (n : ℕ) where
  /-- The array overwritten by `Qᵀ A Z`. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The array overwritten by `Qᵀ B Z`. -/
  B : Matrix (Fin n) (Fin n) ℝ
  /-- The left reflector data, in order of application. -/
  dQ : List ((Fin n → ℝ) × ℝ)
  /-- The right reflector data, in order of application. -/
  dZ : List ((Fin n → ℝ) × ℝ)
  /-- The book's `x`. -/
  x : ℝ
  /-- The book's `y`. -/
  y : ℝ
  /-- The book's `z`. -/
  z : ℝ

section Programs

open GolubVanLoan.Chapter05

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The shift vector of the QZ step**: "Let `M = AB⁻¹` and compute `(M - aI)(M - bI)e₁ =
[x, y, z, 0, …, 0]ᵀ` where `a` and `b` are the eigenvalues of `M`'s lower 2-by-2" — on the block
`p, …, r` (0-based). "`v` can be calculated in `O(1)` flops": `M` is upper Hessenberg, and the
entries it needs (the leading `3 × 2` corner and the trailing `2 × 2` block) are row forward
substitutions `m_i B = a_i` over at most three columns,
```
m₁₁ = a₁₁/b₁₁,  m₂₁ = a₂₁/b₁₁,  m₁₂ = (a₁₂ - m₁₁ b₁₂)/b₂₂,  m₂₂ = (a₂₂ - m₂₁ b₁₂)/b₂₂,
m₃₂ = a₃₂/b₂₂,  e = m_{N-1,N-1},  f = m_{N-1,N},  g = m_{N,N-1},  h = m_{NN},
s = e + h,  t = e h - f g,
x = m₁₁² + m₁₂ m₂₁ - s m₁₁ + t,  y = m₂₁ (m₁₁ + m₂₂ - s),  z = m₂₁ m₃₂
```
(`a + b = s`, `ab = t`; for a `2 × 2` block `z` is `0`). Every operation is rounded. -/
noncomputable def qzShiftVector (p r : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) : M (ℝ × ℝ × ℝ) := do
  let a := qzEntry A
  let b := qzEntry B
  let m₁₁ ← rnd (a p p / b p p)
  let m₂₁ ← rnd (a (p + 1) p / b p p)
  let m₁₂ ← rnd ((← rnd (a p (p + 1) - (← rnd (m₁₁ * b p (p + 1))))) / b (p + 1) (p + 1))
  let m₂₂ ← rnd ((← rnd (a (p + 1) (p + 1) - (← rnd (m₂₁ * b p (p + 1))))) / b (p + 1) (p + 1))
  let μ ← if p + 2 ≤ r then rnd (a (r - 1) (r - 2) / b (r - 2) (r - 2)) else pure 0
  let e ← if p + 2 ≤ r then do
      rnd ((← rnd (a (r - 1) (r - 1) - (← rnd (μ * b (r - 2) (r - 1))))) / b (r - 1) (r - 1))
    else pure m₁₁
  let f ← if p + 2 ≤ r then do
      rnd ((← rnd ((← rnd (a (r - 1) r - (← rnd (μ * b (r - 2) r)))) -
        (← rnd (e * b (r - 1) r)))) / b r r)
    else pure m₁₂
  let g ← rnd (a r (r - 1) / b (r - 1) (r - 1))
  let h ← rnd ((← rnd (a r r - (← rnd (g * b (r - 1) r)))) / b r r)
  let s ← rnd (e + h)
  let t ← rnd ((← rnd (e * h)) - (← rnd (f * g)))
  let x ← rnd ((← rnd ((← rnd ((← rnd (m₁₁ * m₁₁)) + (← rnd (m₁₂ * m₂₁)))) -
    (← rnd (s * m₁₁)))) + t)
  let y ← rnd (m₂₁ * (← rnd ((← rnd (m₁₁ + m₂₂)) - s)))
  let z ← if p + 2 ≤ r then do rnd (m₂₁ * (← rnd (a (p + 2) (p + 1) / b (p + 1) (p + 1))))
    else pure 0
  pure (x, y, z)

/-- **The loop body of Algorithm 7.7.2** at the rows `j, j+1, j+2` (the book's `k, k+1, k+2`):
```
Find Householder Q_k so Q_k [x; y; z] = [*; 0; 0].
A = diag(I_{k-1}, Q_k, I_{n-k-2}) · A;  B = diag(I_{k-1}, Q_k, I_{n-k-2}) · B
Find Householder Z_{k1} so [b_{k+2,k} | b_{k+2,k+1} | b_{k+2,k+2}] Z_{k1} = [0 | 0 | *].
A = A · diag(I_{k-1}, Z_{k1}, I_{n-k-2});  B = B · diag(I_{k-1}, Z_{k1}, I_{n-k-2})
Find Householder Z_{k2} so [b_{k+1,k} | b_{k+1,k+1}] Z_{k2} = [0 | *].
A = A · diag(I_{k-1}, Z_{k2}, I_{n-k-1});  B = B · diag(I_{k-1}, Z_{k2}, I_{n-k-1})
x = a_{k+1,k};  y = a_{k+2,k};  if k < n - 2: z = a_{k+3,k}
```
`Q_k` is `house` on the list `[j, j+1, j+2]`; a Householder matrix on a row is `house` on the
reversed list (`[j+2, j+1, j]`, `[j+1, j]`), whose pivot is the last entry (§7.7.6's design,
report). The reflectors are applied to the whole arrays (`diag(I, ·, I)`) and recorded. -/
noncomputable def qzStep (r : ℕ) (j j₁ j₂ : Fin n) (st : QZStepState n) : M (QZStepState n) := do
  let u : Fin n → ℝ := fun i =>
    if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z else 0
  let q ← houseOn rnd [j, j₁, j₂] u
  let A ← householderApplyLeft rnd q.1 q.2 [j, j₁, j₂] (List.finRange n) st.A
  let B ← householderApplyLeft rnd q.1 q.2 [j, j₁, j₂] (List.finRange n) st.B
  let z₁ ← houseOn rnd [j₂, j₁, j] (B j₂)
  let A ← householderApplyRight rnd z₁.1 z₁.2 (List.finRange n) [j₂, j₁, j] A
  let B ← householderApplyRight rnd z₁.1 z₁.2 (List.finRange n) [j₂, j₁, j] B
  let z₂ ← houseOn rnd [j₁, j] (B j₁)
  let A ← householderApplyRight rnd z₂.1 z₂.2 (List.finRange n) [j₁, j] A
  let B ← householderApplyRight rnd z₂.1 z₂.2 (List.finRange n) [j₁, j] B
  pure ⟨A, B, st.dQ ++ [q], st.dZ ++ [z₁, z₂], A j₁ j, A j₂ j,
    if (j : ℕ) + 3 ≤ r then qzEntry A ((j : ℕ) + 3) j else st.z⟩

/-- **Algorithm 7.7.2 (The QZ Step)**: "Given an unreduced upper Hessenberg matrix `A ∈ ℝ^{n×n}`
and a nonsingular upper triangular matrix `B ∈ ℝ^{n×n}`, the following algorithm overwrites `A`
with the upper Hessenberg matrix `QᵀAZ` and `B` with the upper triangular matrix `QᵀBZ` where `Q`
and `Z` are orthogonal and `Q` has the same first column as the orthogonal similarity
transformation in Algorithm 7.5.1 when it is applied to `AB⁻¹`" — on the block of consecutive
indices `p, …, r` (`p < r < n`; the book's is `p = 0`, `r = n - 1`, and Algorithm 7.7.3 runs it on
its unreduced block `A₂₂`): `qzShiftVector`, the loop body `qzStep` for `k = 1:n-2`, then
```
Find Householder Q_{n-1} so Q_{n-1} [x; y] = [*; 0].
A = diag(I_{n-2}, Q_{n-1}) · A;  B = diag(I_{n-2}, Q_{n-1}) · B
Find Householder Z_{n-1} so [b_{n,n-1} | b_{nn}] Z_{n-1} = [0 | *].
A = A · diag(I_{n-2}, Z_{n-1});  B = B · diag(I_{n-2}, Z_{n-1})
```
The reflectors act on the whole arrays, so on a block this is the book's update
`A = diag(I_p, Q, I_q)ᵀ A diag(I_p, Z, I_q)` of Algorithm 7.7.3. Returns the arrays and the left
and right reflector data (`Q = householderProduct dQ`, `Z = householderProduct dZ`). -/
noncomputable def algorithm_7_7_2 (p r : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ) ×
      List ((Fin n → ℝ) × ℝ)) :=
  if hr : p < r ∧ r < n then do
    let v ← qzShiftVector rnd p r A B
    let st ← (List.finRange n).foldlM (fun st (j : Fin n) =>
      if h : p ≤ (j : ℕ) ∧ (j : ℕ) + 2 ≤ r then
        qzStep rnd r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st
      else pure st) (⟨A, B, [], [], v.1, v.2.1, v.2.2⟩ : QZStepState n)
    let r₁ : Fin n := ⟨r - 1, by omega⟩
    let r' : Fin n := ⟨r, hr.2⟩
    let q ← houseOn rnd [r₁, r'] (fun i => if i = r₁ then st.x else if i = r' then st.y else 0)
    let A ← householderApplyLeft rnd q.1 q.2 [r₁, r'] (List.finRange n) st.A
    let B ← householderApplyLeft rnd q.1 q.2 [r₁, r'] (List.finRange n) st.B
    let z ← houseOn rnd [r', r₁] (B r')
    let A ← householderApplyRight rnd z.1 z.2 (List.finRange n) [r', r₁] A
    let B ← householderApplyRight rnd z.1 z.2 (List.finRange n) [r', r₁] B
    pure (A, B, st.dQ ++ [q], st.dZ ++ [z])
  else pure (A, B, [], [])

end Programs

section ZeroChase

open GolubVanLoan.Chapter05

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- `qzEntry` at `Fin` indices is the entry. -/
theorem qzEntry_fin (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : qzEntry A i j = A i j := by
  simp [qzEntry]

/-- `qzEntry` in range is the entry. -/
theorem qzEntry_of_lt (A : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    qzEntry A i j = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [qzEntry, hi, hj]

/-- `qzEntry` out of range is `0`. -/
theorem qzEntry_of_not_lt (A : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (h : ¬ (i < n ∧ j < n)) :
    qzEntry A i j = 0 := by
  simp only [qzEntry]
  split_ifs
  rfl

/-- The exact run of a column rotation of the zero chase: a rotation with `c² + s² = 1` zeroing
`A(t, l)`, applied to `A`, `B` and `Z`. -/
theorem qzColumnZero_run {l m : Fin n} (hlm : l ≠ m) (t : Fin n) (st : QZArrays n) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ s * -st.A t m + c * st.A t l = 0 ∧
      Id.run (qzColumnZero pure l m t st) = ⟨st.A * givensRotation l m c s,
        st.B * givensRotation l m c s, st.Q, st.Z * givensRotation l m c s⟩ := by
  obtain ⟨c, s, hg, hcs, hz⟩ := givens_exact (-st.A t m) (st.A t l)
  refine ⟨c, s, hcs, hz, ?_⟩
  simp only [qzColumnZero, Id.run_bind, Id.run_pure]
  rw [hg]
  simp only [givensApplyRight_spec_of_forall_mem hlm _ _ (List.nodup_finRange n)
    List.mem_finRange]

/-- One step of the zero chase. -/
theorem qzZeroChaseStep_spec {p : ℕ} {j j₁ : Fin n} (hj : (j₁ : ℕ) = j + 1) (hpj : p ≤ j)
    {st : QZArrays n} (h : st.IsEquiv A₀ B₀) (hA : st.A.IsUpperHessenberg)
    (hB : st.B.IsUpperTriangular) (hBj : st.B j j = 0)
    (hp : 0 < p → qzEntry st.A p (p - 1) = 0) :
    (Id.run (qzZeroChaseStep pure p j j₁ st)).IsEquiv A₀ B₀ ∧
      (Id.run (qzZeroChaseStep pure p j j₁ st)).A.IsUpperHessenberg ∧
      (Id.run (qzZeroChaseStep pure p j j₁ st)).B.IsUpperTriangular ∧
      (Id.run (qzZeroChaseStep pure p j j₁ st)).B j₁ j₁ = 0 ∧
      (0 < p → qzEntry (Id.run (qzZeroChaseStep pure p j j₁ st)).A p (p - 1) = 0) ∧
      (∀ r c : Fin n, (j₁ : ℕ) < r → (j₁ : ℕ) ≤ c →
        (Id.run (qzZeroChaseStep pure p j j₁ st)).A r c = st.A r c) := by
  rw [isUpperHessenberg_iff_fin] at hA ⊢
  rw [isUpperTriangular_iff_fin] at hB ⊢
  have hjj : j ≠ j₁ := fun e => by rw [e] at hj; omega
  obtain ⟨c, s, hg, hcs, hz⟩ := givens_exact (st.B j j₁) (st.B j₁ j₁)
  set G := givensRotation j j₁ c s with hG
  set A₁ := Gᵀ * st.A with hA₁
  set B₁ := Gᵀ * st.B with hB₁
  have hA₁e : ∀ r q, A₁ r q = if r = j then c * st.A j q - s * st.A j₁ q
      else if r = j₁ then s * st.A j q + c * st.A j₁ q else st.A r q := fun r q =>
    givensRotation_transpose_mul_apply hjj c s st.A r q
  have hB₁e : ∀ r q, B₁ r q = if r = j then c * st.B j q - s * st.B j₁ q
      else if r = j₁ then s * st.B j q + c * st.B j₁ q else st.B r q := fun r q =>
    givensRotation_transpose_mul_apply hjj c s st.B r q
  have hst₁ : (⟨A₁, B₁, st.Q * G, st.Z⟩ : QZArrays n).IsEquiv A₀ B₀ := h.rot_left hjj hcs
  have hBjl : ∀ q : Fin n, (q : ℕ) ≤ j → st.B j q = 0 := fun q hq => by
    rcases Nat.lt_or_ge (q : ℕ) j with h1 | h1
    · exact hB j q h1
    · have : q = j := Fin.ext (by omega)
      rw [this, hBj]
  have hB₁t : ∀ r q : Fin n, (q : ℕ) < r → B₁ r q = 0 := by
    intro r q hqr
    rw [hB₁e]
    split_ifs with h1 h2
    · subst h1
      rw [hB r q hqr, hB j₁ q (by omega)]; ring
    · subst h2
      rw [hBjl q (by omega), hB r q hqr]; ring
    · exact hB r q hqr
  have hB₁jj : B₁ j j = 0 := by
    rw [hB₁e]; simp only [↓reduceIte]; rw [hBj, hB j₁ j (by omega)]; ring
  have hB₁j₁ : B₁ j₁ j₁ = 0 := by
    rw [hB₁e]; simp only [hjj.symm, ↓reduceIte]; linear_combination hz
  have hB₁jl : ∀ q : Fin n, (q : ℕ) ≤ j → B₁ j q = 0 := fun q hq => by
    rcases Nat.lt_or_ge (q : ℕ) j with h1 | h1
    · exact hB₁t j q h1
    · have : q = j := Fin.ext (by omega)
      rw [this, hB₁jj]
  have hA₁h : ∀ r q : Fin n, (q : ℕ) + 1 < r → ¬ ((r : ℕ) = j₁ ∧ (q : ℕ) + 1 = j) →
      A₁ r q = 0 := by
    intro r q hqr hne
    rw [hA₁e]
    split_ifs with h1 h2
    · subst h1
      rw [hA r q hqr, hA j₁ q (by omega)]; ring
    · subst h2
      rw [hA j q (by omega), hA r q hqr]; ring
    · exact hA r q hqr
  have hA₁out : ∀ r q : Fin n, r ≠ j → r ≠ j₁ → A₁ r q = st.A r q := fun r q h1 h2 => by
    rw [hA₁e]; simp [h1, h2]
  by_cases hpj' : p < (j : ℕ)
  · set l : Fin n := ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ with hl
    have hlv : (l : ℕ) = j - 1 := rfl
    have hlj : l ≠ j := fun e => by have := congrArg Fin.val e; simp [l] at this; omega
    obtain ⟨c', s', hcs', hz', hcz⟩ :=
      qzColumnZero_run hlj j₁ (⟨A₁, B₁, st.Q * G, st.Z⟩ : QZArrays n)
    have hrun : Id.run (qzZeroChaseStep pure p j j₁ st) =
        ⟨A₁ * givensRotation l j c' s', B₁ * givensRotation l j c' s', st.Q * G,
          st.Z * givensRotation l j c' s'⟩ := by
      simp only [qzZeroChaseStep, Id.run_bind]
      rw [hg]
      simp only [givensApplyLeft_spec_of_forall_mem hjj _ _ (List.nodup_finRange n)
        List.mem_finRange, givensApplyRight_spec_of_forall_mem hjj _ _ (List.nodup_finRange n)
        List.mem_finRange, hpj', ↓reduceIte]
      exact hcz
    rw [hrun]
    have hH : ∀ (Y : Matrix (Fin n) (Fin n) ℝ) r q, (Y * givensRotation l j c' s') r q =
        if q = l then c' * Y r l - s' * Y r j else if q = j then s' * Y r l + c' * Y r j
          else Y r q := fun Y r q => mul_givensRotation_apply hlj c' s' Y r q
    refine ⟨hst₁.rot_right hlj hcs', ?_, ?_, ?_, ?_, ?_⟩
    · intro r q hqr
      change (A₁ * givensRotation l j c' s') r q = 0
      rw [hH]
      split_ifs with h1 h2
      · subst h1
        by_cases hr : r = j₁
        · subst hr
          linear_combination hz'
        · rw [hA₁h r l hqr (fun ⟨e, _⟩ => hr (Fin.ext e)),
            hA₁h r j (by omega) (fun ⟨_, e⟩ => by omega)]
          ring
      · subst h2
        rw [hA₁h r l (by omega) (fun ⟨_, e⟩ => by omega), hA₁h r q hqr (fun ⟨_, e⟩ => by omega)]
        ring
      · exact hA₁h r q hqr (fun ⟨_, e⟩ => h1 (Fin.ext (by omega)))
    · intro r q hqr
      change (B₁ * givensRotation l j c' s') r q = 0
      rw [hH]
      split_ifs with h1 h2
      · subst h1
        rcases Nat.lt_or_ge (j : ℕ) r with h3 | h3
        · rw [hB₁t r l (by omega), hB₁t r j h3]; ring
        · have : r = j := Fin.ext (by omega)
          rw [this, hB₁jl l (by omega), hB₁jj]; ring
      · subst h2
        rw [hB₁t r l (by omega), hB₁t r q hqr]; ring
      · exact hB₁t r q hqr
    · change (B₁ * givensRotation l j c' s') j₁ j₁ = 0
      rw [hH]
      have h1 : j₁ ≠ l := fun e => by rw [e] at hj; omega
      simp only [h1, hjj.symm, ↓reduceIte]
      exact hB₁j₁
    · intro hp0
      have hpn : p < n := by omega
      rw [qzEntry_of_lt _ hpn (by omega)]
      change (A₁ * givensRotation l j c' s') _ _ = 0
      rw [hH]
      have h1 : (⟨p - 1, by omega⟩ : Fin n) ≠ l := fun e => by
        have := congrArg Fin.val e; simp [l] at this; omega
      have h2 : (⟨p - 1, by omega⟩ : Fin n) ≠ j := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp only [h1, h2, ↓reduceIte]
      have h3 : (⟨p, hpn⟩ : Fin n) ≠ j := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      have h4 : (⟨p, hpn⟩ : Fin n) ≠ j₁ := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      rw [hA₁out _ _ h3 h4, ← qzEntry_of_lt st.A hpn (by omega)]
      exact hp hp0
    · intro r q hr hq
      change (A₁ * givensRotation l j c' s') r q = st.A r q
      have h1 : q ≠ l := fun e => by rw [e] at hq; omega
      have h2 : q ≠ j := fun e => by rw [e] at hq; omega
      have h3 : r ≠ j := fun e => by rw [e] at hr; omega
      have h4 : r ≠ j₁ := fun e => by rw [e] at hr; omega
      rw [hH]
      simp only [h1, h2, ↓reduceIte]
      exact hA₁out r q h3 h4
  · have hpj'' : (j : ℕ) = p := by omega
    have hrun : Id.run (qzZeroChaseStep pure p j j₁ st) = ⟨A₁, B₁, st.Q * G, st.Z⟩ := by
      simp only [qzZeroChaseStep, Id.run_bind]
      rw [hg]
      simp only [givensApplyLeft_spec_of_forall_mem hjj _ _ (List.nodup_finRange n)
        List.mem_finRange, givensApplyRight_spec_of_forall_mem hjj _ _ (List.nodup_finRange n)
        List.mem_finRange, hpj', ↓reduceIte, Id.run_pure]
      rfl
    rw [hrun]
    -- the entry `A(p, p - 1)` vanishes, so does the only candidate fill-in `(j₁, j - 1)`
    have hbd : ∀ q : Fin n, (q : ℕ) + 1 = j → st.A j q = 0 := fun q hq => by
      have := hp (by omega)
      rw [qzEntry_of_lt _ (by omega) (by omega)] at this
      rw [← this]
      congr 1 <;> ext <;> simp <;> omega
    refine ⟨hst₁, ?_, hB₁t, hB₁j₁, ?_, ?_⟩
    · intro r q hqr
      by_cases hbad : (r : ℕ) = j₁ ∧ (q : ℕ) + 1 = j
      · obtain ⟨e1, e2⟩ := hbad
        have hr : r = j₁ := Fin.ext e1
        change A₁ r q = 0
        rw [hr, hA₁e]
        simp only [hjj.symm, ↓reduceIte]
        rw [hbd q e2, hA j₁ q (by omega)]
        ring
      · exact hA₁h r q hqr hbad
    · intro hp0
      rw [qzEntry_of_lt _ (by omega) (by omega)]
      change A₁ _ _ = 0
      have h3 : (⟨p, by omega⟩ : Fin n) = j := Fin.ext hpj''.symm
      rw [hA₁e]
      simp only [h3, ↓reduceIte]
      rw [hbd _ (by simp; omega), hA j₁ _ (by simp; omega)]
      ring
    · intro r q hr _
      exact hA₁out r q (fun e => by rw [e] at hr; omega) (fun e => by rw [e] at hr; omega)

end ZeroChase

section ZeroChaseSpec

open GolubVanLoan.Chapter05

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- **§7.7.5, "This zero-chasing technique is perfectly general and can be used to zero
`a_{n,n-1}` regardless of where the zero appears along `B`'s diagonal"**: on the block `p, …, r`
of a Hessenberg–triangular pair decoupled from the rest (`a_{p,p-1} = 0`, `a_{r+1,r} = 0`) with
`b_kk = 0` for some `p ≤ k ≤ r`, the zero chase keeps the equivalence `(A, B) = (Qᵀ A₀ Z,
Qᵀ B₀ Z)` with orthogonal `Q`, `Z` (`QZArrays.IsEquiv`), keeps `A` upper Hessenberg and `B` upper
triangular and the block decoupled, pushes the zero to `b_rr`, and zeroes `a_{r,r-1}` (for a block
of size at least two). With `p = 0`, `r = n - 1` and `Q = Z = I` on entry this is the book's
display: the output is `(Qᵀ A Z, Qᵀ B Z)` with `(Qᵀ A Z)_{n,n-1} = 0` and `(Qᵀ B Z)_{nn} = 0`. -/
theorem qzZeroChase_spec {p k r : ℕ} (hpk : p ≤ k) (hkr : k ≤ r) (hr : r < n)
    {st : QZArrays n} (h : st.IsEquiv A₀ B₀) (hA : st.A.IsUpperHessenberg)
    (hB : st.B.IsUpperTriangular) (hk : qzEntry st.B k k = 0)
    (hp : 0 < p → qzEntry st.A p (p - 1) = 0) (hr₁ : qzEntry st.A (r + 1) r = 0) :
    (Id.run (qzZeroChase pure p k r st)).IsEquiv A₀ B₀ ∧
      (Id.run (qzZeroChase pure p k r st)).A.IsUpperHessenberg ∧
      (Id.run (qzZeroChase pure p k r st)).B.IsUpperTriangular ∧
      qzEntry (Id.run (qzZeroChase pure p k r st)).B r r = 0 ∧
      (p < r → qzEntry (Id.run (qzZeroChase pure p k r st)).A r (r - 1) = 0) ∧
      (0 < p → qzEntry (Id.run (qzZeroChase pure p k r st)).A p (p - 1) = 0) ∧
      qzEntry (Id.run (qzZeroChase pure p k r st)).A (r + 1) r = 0 := by
  set f := fun (st : QZArrays n) (j : Fin n) => Id.run
    (if h : k ≤ (j : ℕ) ∧ (j : ℕ) < r ∧ r < n then
      qzZeroChaseStep pure p j ⟨(j : ℕ) + 1, by omega⟩ st
    else pure st) with hf
  have key := foldl_induction_getElem (List.finRange n) f
    (fun q st => st.IsEquiv A₀ B₀ ∧ st.A.IsUpperHessenberg ∧ st.B.IsUpperTriangular ∧
      qzEntry st.B (max k (min q r)) (max k (min q r)) = 0 ∧
      (0 < p → qzEntry st.A p (p - 1) = 0) ∧ qzEntry st.A (r + 1) r = 0) st
    ⟨h, hA, hB, by rwa [show max k (min 0 r) = k by omega], hp, hr₁⟩ (by
      intro q hq s ⟨hs, hsA, hsB, hsz, hsp, hsr⟩
      have hq' : q < n := by simpa using hq
      have hv : ((List.finRange n)[q] : ℕ) = q := by simp
      by_cases hg : k ≤ q ∧ q < r
      · have hg' : k ≤ ((List.finRange n)[q] : ℕ) ∧ ((List.finRange n)[q] : ℕ) < r ∧ r < n := by
          rw [hv]; exact ⟨hg.1, hg.2, hr⟩
        have hfq : f s (List.finRange n)[q] = Id.run (qzZeroChaseStep pure p
            (List.finRange n)[q] ⟨((List.finRange n)[q] : ℕ) + 1, by omega⟩ s) := by
          simp only [hf, hg', and_self, ↓reduceDIte]
        rw [hfq]
        have hz : max k (min q r) = q := by omega
        rw [hz, qzEntry_of_lt _ hq' hq'] at hsz
        have hBj : s.B (List.finRange n)[q] (List.finRange n)[q] = 0 := by
          rw [← hsz]; congr 1 <;> ext <;> simp
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := qzZeroChaseStep_spec (j := (List.finRange n)[q])
          (j₁ := ⟨((List.finRange n)[q] : ℕ) + 1, by omega⟩) rfl (by rw [hv]; omega) hs hsA hsB
          hBj hsp
        refine ⟨h1, h2, h3, ?_, h5, ?_⟩
        · rw [show max k (min (q + 1) r) = q + 1 by omega, qzEntry_of_lt _ (by omega) (by omega)]
          rw [← h4]; congr 1 <;> ext <;> simp
        · by_cases hr1 : r + 1 < n
          · rw [qzEntry_of_lt _ hr1 hr, h6 _ _ (by simp; omega) (by simp; omega),
              ← qzEntry_of_lt s.A hr1 hr]
            exact hsr
          · exact qzEntry_of_not_lt _ (by omega)
      · have hg' : ¬ (k ≤ ((List.finRange n)[q] : ℕ) ∧ ((List.finRange n)[q] : ℕ) < r ∧ r < n) := by
          rw [hv]; exact fun h => hg ⟨h.1, h.2.1⟩
        have hfq : f s (List.finRange n)[q] = s := by
          simp only [hf, hg', ↓reduceDIte, Id.run_pure]
        rw [hfq]
        refine ⟨hs, hsA, hsB, ?_, hsp, hsr⟩
        rwa [show max k (min (q + 1) r) = max k (min q r) by omega])
  have hrun : Id.run (qzZeroChase pure p k r st) = Id.run
      (if h : p < r ∧ r < n then
        qzColumnZero pure ⟨r - 1, by omega⟩ ⟨r, h.2⟩ ⟨r, h.2⟩ ((List.finRange n).foldl f st)
      else pure ((List.finRange n).foldl f st)) := by
    simp only [qzZeroChase, Id.run_bind, hf, List.idRun_foldlM]
  rw [hrun]
  simp only [List.length_finRange] at key
  obtain ⟨hs, hsA, hsB, hsz, hsp, hsr⟩ := key
  rw [show max k (min n r) = r by omega] at hsz
  set s := (List.finRange n).foldl f st with hs_def
  by_cases hpr : p < r
  · have hc : p < r ∧ r < n := ⟨hpr, hr⟩
    simp only [hc, and_self, ↓reduceDIte]
    set l : Fin n := ⟨r - 1, by omega⟩ with hl
    set m : Fin n := ⟨r, hr⟩ with hm
    have hlm : l ≠ m := fun e => by have := congrArg Fin.val e; simp [l, m] at this; omega
    obtain ⟨c, s', hcs, hz, hcz⟩ := qzColumnZero_run hlm m s
    rw [hcz]
    rw [isUpperHessenberg_iff_fin] at hsA ⊢
    rw [isUpperTriangular_iff_fin] at hsB ⊢
    have hH : ∀ (Y : Matrix (Fin n) (Fin n) ℝ) x y, (Y * givensRotation l m c s') x y =
        if y = l then c * Y x l - s' * Y x m else if y = m then s' * Y x l + c * Y x m
          else Y x y := fun Y x y => mul_givensRotation_apply hlm c s' Y x y
    have hBrr : s.B m m = 0 := by
      have := hsz; rwa [qzEntry_of_lt s.B hr hr] at this
    have hAr1 : ∀ h : r + 1 < n, s.A ⟨r + 1, h⟩ m = 0 := fun h1 => by
      have := hsr; rwa [qzEntry_of_lt s.A h1 hr] at this
    have hml : m ≠ l := hlm.symm
    have e1 : (⟨r - 1, (by omega : r - 1 < n)⟩ : Fin n) = l := rfl
    have e2 : (⟨r, hr⟩ : Fin n) = m := rfl
    refine ⟨hs.rot_right hlm hcs, ?_, ?_, ?_, fun _ => ?_, fun hp0 => ?_, ?_⟩
    · intro x y hxy
      simp only
      rw [hH]
      split_ifs with h1 h2
      · subst h1
        rw [hsA x l hxy]
        by_cases hx : (x : ℕ) = r + 1
        · have : x = ⟨r + 1, by omega⟩ := Fin.ext hx
          rw [this, hAr1]; ring
        · rw [hsA x m (by simp [m]; simp [l] at hxy; omega)]; ring
      · subst h2
        rw [hsA x l (by simp [l]; simp [m] at hxy; omega), hsA x m hxy]; ring
      · exact hsA x y hxy
    · intro x y hxy
      simp only
      rw [hH]
      split_ifs with h1 h2
      · subst h1
        rw [hsB x l hxy]
        by_cases hx : (x : ℕ) = r
        · have : x = m := Fin.ext hx
          rw [this, hBrr]; ring
        · rw [hsB x m (by simp [m]; simp [l] at hxy; omega)]; ring
      · subst h2
        rw [hsB x l (by simp [l]; simp [m] at hxy; omega), hsB x m hxy]; ring
      · exact hsB x y hxy
    · change qzEntry (s.B * givensRotation l m c s') r r = 0
      rw [qzEntry_of_lt (s.B * givensRotation l m c s') hr hr, hH, e2]
      simp only [hml, ↓reduceIte]
      rw [hsB m l (by simp [l, m]; omega), hBrr]
      ring
    · change qzEntry (s.A * givensRotation l m c s') r (r - 1) = 0
      rw [qzEntry_of_lt (s.A * givensRotation l m c s') hr (by omega), hH, e1, e2]
      simp only [↓reduceIte]
      linear_combination hz
    · change qzEntry (s.A * givensRotation l m c s') p (p - 1) = 0
      rw [qzEntry_of_lt (s.A * givensRotation l m c s') (by omega) (by omega), hH]
      have h1 : (⟨p - 1, by omega⟩ : Fin n) ≠ l := fun e => by
        have := congrArg Fin.val e; simp [l] at this; omega
      have h2 : (⟨p - 1, by omega⟩ : Fin n) ≠ m := fun e => by
        have := congrArg Fin.val e; simp [m] at this; omega
      simp only [h1, h2, ↓reduceIte]
      rw [← qzEntry_of_lt s.A (by omega) (by omega)]
      exact hsp hp0
    · by_cases hr1 : r + 1 < n
      · change qzEntry (s.A * givensRotation l m c s') (r + 1) r = 0
        rw [qzEntry_of_lt (s.A * givensRotation l m c s') hr1 hr, hH, e2]
        simp only [hml, ↓reduceIte]
        rw [hsA _ l (by simp [l]; omega), hAr1 hr1]
        ring
      · exact qzEntry_of_not_lt _ (by omega)
  · have hc : ¬ (p < r ∧ r < n) := fun h => hpr h.1
    simp only [hc, ↓reduceDIte, Id.run_pure]
    exact ⟨hs, hsA, hsB, hsz, fun h => absurd h hpr, hsp, hsr⟩

end ZeroChaseSpec

/-! ### §7.7.7 The overall QZ process -/

/-- The trailing block from index `s` on is upper quasi-triangular and decoupled, for an upper
Hessenberg array: `a_{s,s-1} = 0` (or `s = 0`), and no two consecutive subdiagonal entries of the
block are nonzero (its diagonal blocks have size one or two). -/
def qzTrailingQuasi (A : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) : Prop :=
  (s = 0 ∨ qzEntry A s (s - 1) = 0) ∧
    ∀ i < n, s < i → i + 1 < n → qzEntry A i (i - 1) = 0 ∨ qzEntry A (i + 1) i = 0

/-- The block `r - d + 1, …, r` has nonzero subdiagonal entries (it is unreduced). -/
def qzUnreducedTail (A : Matrix (Fin n) (Fin n) ℝ) (r d : ℕ) : Prop :=
  ∀ i ≤ r, r - d < i → qzEntry A i (i - 1) ≠ 0

section Programs

open GolubVanLoan.Chapter05

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The deflation sweep of Algorithm 7.7.3**: "Set to zero subdiagonal entries that satisfy
`|a_{i,i-1}| ≤ ε(|a_{i-1,i-1}| + |a_ii|)`", with the right side rounded (`fl(ε · fl(|·| + |·|))`)
and `|·|` and the comparison exact (convention 1). -/
noncomputable def qzDeflate (ε : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun A (i : Fin n) =>
    if h : 0 < (i : ℕ) then do
      let i₀ : Fin n := ⟨(i : ℕ) - 1, by omega⟩
      let t ← rnd (ε * (← rnd (|A i₀ i₀| + |A i i|)))
      if |A i i₀| ≤ t then pure (of fun a b => if a = i ∧ b = i₀ then 0 else A a b)
      else pure A
    else pure A) A

open Classical in
/-- **One pass of Algorithm 7.7.3's `until q = n` loop** (a finished state is kept): deflate;
"find the largest nonnegative `q` and the smallest nonnegative `p` such that
`A = [A₁₁ A₁₂ A₁₃; 0 A₂₂ A₂₃; 0 0 A₃₃]` (sizes `p, n-p-q, q`) … `A₃₃` is upper quasi-triangular and
`A₂₂` is upper Hessenberg and unreduced" (`Nat.findGreatest` over `qzTrailingQuasi` and
`qzUnreducedTail`); if `q = n` the state is finished; else, on the block `p, …, r = n-q-1`: "if
`B₂₂` is singular, zero `a_{n-q,n-q-1}`" (the zero chase from the last zero on the block's diagonal
of `B`, an exact test), "else apply Algorithm 7.7.2 to `A₂₂` and `B₂₂` and update" (the reflector
data accumulated into `Q` and `Z` with `householderApplyRight` on the block's columns). -/
noncomputable def qzPass (ε : ℝ) (st : QZArrays n × Bool) : M (QZArrays n × Bool) :=
  if st.2 then pure st else do
    let A ← qzDeflate rnd ε st.1.A
    let q := Nat.findGreatest (fun q => qzTrailingQuasi A (n - q)) n
    if q = n then pure (⟨A, st.1.B, st.1.Q, st.1.Z⟩, true) else do
      let r := n - q - 1
      let p := r - Nat.findGreatest (fun d => qzUnreducedTail A r d) r
      let blk := (List.finRange n).filter fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r
      match (blk.filter fun i => st.1.B i i = 0).getLast? with
      | some k => do
        let st' ← qzZeroChase rnd p k r ⟨A, st.1.B, st.1.Q, st.1.Z⟩
        pure (st', false)
      | none => do
        let out ← algorithm_7_7_2 rnd p r A st.1.B
        let Q ← out.2.2.1.foldlM (fun Q d =>
          householderApplyRight rnd d.1 d.2 (List.finRange n) blk Q) st.1.Q
        let Z ← out.2.2.2.foldlM (fun Z d =>
          householderApplyRight rnd d.1 d.2 (List.finRange n) blk Z) st.1.Z
        pure (⟨out.1, out.2.1, Q, Z⟩, false)

/-- **Algorithm 7.7.3 (the QZ algorithm, Moler–Stewart)**: "Given `A ∈ ℝ^{n×n}` and
`B ∈ ℝ^{n×n}`, the following algorithm computes orthogonal `Q` and `Z` such that `QᵀAZ = T` is
upper quasi-triangular and `QᵀBZ = S` is upper triangular. `A` is overwritten by `T` and `B` by
`S`":
```
Using Algorithm 7.7.1, overwrite A with QᵀAZ (upper Hessenberg) and B with QᵀBZ (upper triangular).
until q = n
    (one `qzPass`)
end
```
The `until` loop is at most `fuel` passes (convention 3); the result is `(T, S, Q, Z)` and the
flag `done` (`q = n` was reached). -/
noncomputable def algorithm_7_7_3 (ε : ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ) :
    M (QZArrays n × Bool) := do
  let st ← algorithm_7_7_1 rnd A B
  (List.range fuel).foldlM (fun st _ => qzPass rnd ε st) (st, false)

end Programs

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

/-! ### §7.7.9 The polynomial eigenvalue problem: the linearization (7.7.6) -/

section Linearization

variable {e : ℕ}

/-- **The `λ`-matrices of §7.7.9** `P_k(λ) = A_k + λ A_{k+1} + ⋯ + λ^{d-k} A_d` for
`A₀, …, A_d` (`A : Fin (d + 1) → ℂ^{n×n}`); `P₀(λ) = P(λ)` is (7.7.4), and `P_k = 0` for
`k > d`. -/
noncomputable def lambdaTail {d : ℕ} (A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (l : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j : Fin (d + 1), if k ≤ (j : ℕ) then l ^ ((j : ℕ) - k) • A j else 0

/-- "`P_k(λ) = A_k + λ P_{k+1}(λ)`" (§7.7.9). -/
theorem lambdaTail_eq_add {d : ℕ} (A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) {k : ℕ}
    (hk : k < d + 1) (l : ℂ) :
    lambdaTail A k l = A ⟨k, hk⟩ + l • lambdaTail A (k + 1) l := by
  have h : ∀ j : Fin (d + 1), (if k ≤ (j : ℕ) then l ^ ((j : ℕ) - k) • A j else 0) =
      (if j = ⟨k, hk⟩ then A j else 0) +
        l • (if k + 1 ≤ (j : ℕ) then l ^ ((j : ℕ) - (k + 1)) • A j else 0) := by
    intro j
    by_cases hj : j = ⟨k, hk⟩
    · subst hj
      simp
    · have hj' : (j : ℕ) ≠ k := fun e => hj (Fin.ext e)
      by_cases hkj : k + 1 ≤ (j : ℕ)
      · have hkj' : k ≤ (j : ℕ) := by omega
        simp only [hkj', hj, hkj, ↓reduceIte, zero_add, smul_smul, ← pow_succ']
        congr 2
        omega
      · have hkj' : ¬ k ≤ (j : ℕ) := by omega
        simp [hkj', hj, hkj]
  simp only [lambdaTail, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, Finset.smul_sum]

/-- `P_d(λ) = A_d`. -/
theorem lambdaTail_self {d : ℕ} (A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    lambdaTail A d l = A (Fin.last d) := by
  rw [lambdaTail, Finset.sum_eq_single (Fin.last d)]
  · simp
  · intro j _ hj
    have : ¬ d ≤ (j : ℕ) := fun h =>
      hj (Fin.ext (le_antisymm (Nat.lt_succ_iff.1 j.isLt) h))
    simp [this]
  · simp

/-- The coefficient `A_k` read on a natural index (`0` beyond the degree). -/
private noncomputable def coeffAt {d : ℕ} (A : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  if h : k < d + 1 then A ⟨k, h⟩ else 0

/-- A sum over `Fin m` of a term selected by the value of the index. -/
private theorem sum_ite_val_eq {X : Type*} [AddCommMonoid X] (m t : ℕ) (Y : X) :
    (∑ b : Fin m, if (b : ℕ) = t then Y else 0) = if t < m then Y else 0 := by
  split_ifs with ht
  · rw [Finset.sum_eq_single ⟨t, ht⟩]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ t := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    have : (b : ℕ) ≠ t := fun h => ht (h ▸ b.isLt)
    simp [this]

/-- The blocks of `S(λ)`: `I` on the diagonal, `-λ I` on the superdiagonal. -/
private def sBlocks (l : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (a : ℕ) = b then 1 else if (b : ℕ) = a + 1 then -(l • 1) else 0

/-- The blocks of `diag(P(λ), I_{(d-1)n})`. -/
private noncomputable def dBlocks (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (a : ℕ) = b then (if (a : ℕ) = 0 then lambdaTail A 0 l else 1) else 0

/-- The blocks of `T(λ)`: first block row `[0 ⋯ 0 I]`, `-I` on the subdiagonal, last block
column `[I; P₁(λ); …; P_{d-1}(λ)]`. -/
private noncomputable def tBlocks (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (b : ℕ) = e then (if (a : ℕ) = 0 then 1 else lambdaTail A a l)
    else if (a : ℕ) = b + 1 then -1 else 0

/-- The blocks of `L(λ)`, written as `L₀ + λ L₁`. -/
private def lBlocks (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => (if (b : ℕ) = e then A a.castSucc else if (a : ℕ) = b + 1 then -1 else 0) +
    l • (if (a : ℕ) = b then (if (a : ℕ) = e then A (Fin.last (e + 1)) else 1) else 0)

/-- **`S(λ)` of (7.7.6)** (`d = e + 1` block rows of size `n`, on `Fin d × Fin n`): identity blocks
on the diagonal, `-λ I_n` on the block superdiagonal. -/
def linearizationS (l : ℂ) : Matrix (Fin (e + 1) × Fin n) (Fin (e + 1) × Fin n) ℂ :=
  comp _ _ _ _ ℂ (sBlocks l)

/-- **`diag(P(λ), I_{(d-1)n})` of (7.7.6)**. -/
noncomputable def linearizationDiag (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1) × Fin n) (Fin (e + 1) × Fin n) ℂ :=
  comp _ _ _ _ ℂ (dBlocks A l)

/-- **`T(λ)` of (7.7.6)**: first block row `[0 ⋯ 0 I]`, `-I_n` on the block subdiagonal, last
block column `[I; P₁(λ); …; P_{d-1}(λ)]`. -/
noncomputable def linearizationT (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1) × Fin n) (Fin (e + 1) × Fin n) ℂ :=
  comp _ _ _ _ ℂ (tBlocks A l)

/-- **The companion-form pencil `L(λ)` of (7.7.6)**: block rows `[λI 0 ⋯ A₀]`,
`[-I λI ⋯ A₁]`, …, `[0 ⋯ -I, A_{d-1} + λ A_d]`, i.e. `L₀ + λ L₁` with `L₀` the `-I` subdiagonal
and last block column `[A₀; …; A_{d-1}]`, `L₁ = diag(I, …, I, A_d)`. -/
def linearizationPencil (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1) × Fin n) (Fin (e + 1) × Fin n) ℂ :=
  comp _ _ _ _ ℂ (lBlocks A l)

/-- The block identity behind (7.7.6). -/
private theorem blocks_mul (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    sBlocks l * dBlocks A l * tBlocks A l = lBlocks A l := by
  refine Matrix.ext fun a c => ?_
  have hSD : ∀ b, (sBlocks (n := n) (e := e) l * dBlocks A l) a b =
      sBlocks l a b * dBlocks A l b b := by
    intro b
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · intro b' _ hb'
      have : (b' : ℕ) ≠ b := fun h => hb' (Fin.ext h)
      simp [dBlocks, this]
    · simp
  set K : Matrix (Fin n) (Fin n) ℂ := if (c : ℕ) = e then lambdaTail A (a + 1) l
    else if (a : ℕ) = c then -1 else 0 with hK
  have hterm : ∀ b : Fin (e + 1), sBlocks l a b * dBlocks A l b b * tBlocks A l b c =
      (if b = a then dBlocks A l a a * tBlocks A l a c else 0) +
        (if (b : ℕ) = a + 1 then -(l • K) else 0) := by
    intro b
    by_cases hba : b = a
    · subst hba
      simp [sBlocks]
    · have hba' : (b : ℕ) ≠ a := fun h => hba (Fin.ext h)
      by_cases hb1 : (b : ℕ) = a + 1
      · have h1 : ¬ (a : ℕ) = a + 1 := by omega
        have h2 : ¬ (a : ℕ) + 1 = 0 := by omega
        have h3 : ((a : ℕ) + 1 = (c : ℕ) + 1) ↔ (a : ℕ) = c := by omega
        simp only [sBlocks, dBlocks, tBlocks, of_apply, hba, hb1, h1, h2, h3, ↓reduceIte,
          zero_add, K]
        split_ifs <;> simp
      · have hab : (a : ℕ) ≠ b := by omega
        simp [sBlocks, hba, hab, hb1]
  rw [Matrix.mul_apply]
  simp_rw [hSD]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_add_distrib, Finset.sum_ite_eq',
    sum_ite_val_eq]
  have hAa : A a.castSucc = coeffAt A a := by simp [coeffAt, Fin.castSucc, Fin.castAdd, Fin.castLE]
  simp only [Finset.mem_univ, ↓reduceIte, dBlocks, tBlocks, lBlocks, of_apply, K, hAa]
  have hrec : ∀ k ≤ e, lambdaTail A k l = coeffAt A k + l • lambdaTail A (k + 1) l :=
    fun k hk => by rw [lambdaTail_eq_add A (by omega)]; simp [coeffAt, show k < e + 2 by omega]
  have hlast : lambdaTail A (e + 1) l = A (Fin.last (e + 1)) := lambdaTail_self A l
  have hae := Nat.lt_succ_iff.1 a.isLt
  have hce := Nat.lt_succ_iff.1 c.isLt
  generalize (a : ℕ) = x at hae ⊢
  generalize (c : ℕ) = y at hce ⊢
  by_cases hy : y = e
  · subst hy
    by_cases hx0 : x = 0
    · subst hx0
      by_cases he : y = 0
      · subst he
        simp [hrec 0 le_rfl, hlast]
      · have h1 : 0 < y := Nat.pos_of_ne_zero he
        simp [Ne.symm he, h1, hrec 0 (Nat.zero_le _)]
    · by_cases hxe : x = y
      · subst hxe
        simp [hx0, hrec x le_rfl, hlast]
      · have h1 : x + 1 < y + 1 := by omega
        simp [hx0, hxe, h1, hrec x hae]
  · by_cases hxy : x = y
    · subst hxy
      have h1 : x + 1 < e + 1 := by omega
      simp [hy, h1]
    · by_cases hx0 : x = 0
      · subst hx0
        simp [hy, hxy]
      · simp [hy, hxy, hx0]

/-- A block matrix that is block upper triangular with identity diagonal blocks has
determinant `1`. -/
private theorem det_comp_eq_one
    {X : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ)}
    (hX : ∀ a b, b < a → X a b = 0) (hd : ∀ a, X a a = 1) :
    (comp _ _ _ _ ℂ X).det = 1 := by
  have hbt : (comp _ _ _ _ ℂ X).BlockTriangular Prod.fst := by
    intro i j hij
    simp [hX _ _ hij]
  rw [hbt.det]
  refine Finset.prod_eq_one fun k _ => ?_
  have h1 : (comp _ _ _ _ ℂ X).toSquareBlock Prod.fst k = 1 := by
    ext ⟨⟨a, i⟩, ha⟩ ⟨⟨b, j⟩, hb⟩
    simp only at ha hb
    subst ha hb
    simp only [toSquareBlock, toSquareBlockProp, toBlock, submatrix_apply, comp_apply, hd,
      one_apply, Subtype.mk.injEq, Prod.mk.injEq, true_and]
  rw [h1, det_one]

/-- The constant factor of `T(λ)`: `I` in block `(0, d-1)` and `-I` on the block subdiagonal. -/
private def t0Blocks : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (b : ℕ) = e then (if (a : ℕ) = 0 then 1 else 0)
    else if (a : ℕ) = b + 1 then -1 else 0

/-- The unit upper triangular factor of `T(λ)`: `T(λ) = T₀ V(λ)`. -/
private noncomputable def vBlocks (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ) :=
  of fun a b => if (a : ℕ) = b then 1 else if (b : ℕ) = e then -lambdaTail A (a + 1) l else 0

/-- A sum over `Fin m` whose left factor is supported at one index value. -/
private theorem sum_single_mul_left {X : Type*} [NonUnitalNonAssocSemiring X] {m t : ℕ}
    (ht : t < m) (x : X) (g : Fin m → X) :
    ∑ b : Fin m, (if (b : ℕ) = t then x else 0) * g b = x * g ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ t := fun h => hb (Fin.ext h)
    simp [this]
  · simp

/-- The rows of `T₀`: row `a` has its one nonzero block in column `a - 1` (`d - 1` for
`a = 0`). -/
private theorem t0Blocks_row (a b : Fin (e + 1)) :
    (t0Blocks : Matrix _ _ (Matrix (Fin n) (Fin n) ℂ)) a b =
      if (b : ℕ) = (if (a : ℕ) = 0 then e else (a : ℕ) - 1) then
        (if (a : ℕ) = 0 then 1 else -1) else 0 := by
  have hb := b.isLt
  have ha := a.isLt
  simp only [t0Blocks, of_apply]
  split_ifs <;> first | rfl | omega

/-- The columns of `T₀`: column `b` has its one nonzero block in row `b + 1` (`0` for
`b = d - 1`). -/
private theorem t0Blocks_col (a b : Fin (e + 1)) :
    (t0Blocks : Matrix _ _ (Matrix (Fin n) (Fin n) ℂ)) a b =
      if (a : ℕ) = (if (b : ℕ) = e then 0 else (b : ℕ) + 1) then
        (if (b : ℕ) = e then 1 else -1) else 0 := by
  have hb := b.isLt
  have ha := a.isLt
  simp only [t0Blocks, of_apply]
  split_ifs <;> rfl

private theorem tBlocks_eq_mul (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    tBlocks A l = t0Blocks * vBlocks A l := by
  refine Matrix.ext fun a c => ?_
  have ha := a.isLt
  have hc := c.isLt
  have hτ : (if (a : ℕ) = 0 then e else (a : ℕ) - 1) < e + 1 := by split_ifs <;> omega
  rw [Matrix.mul_apply]
  simp_rw [t0Blocks_row a]
  rw [sum_single_mul_left hτ]
  simp only [tBlocks, vBlocks, of_apply]
  by_cases ha0 : (a : ℕ) = 0
  · by_cases hce : (c : ℕ) = e
    · simp [ha0, hce]
    · have : (e : ℕ) ≠ c := fun h => hce h.symm
      simp [ha0, hce, this]
  · by_cases hce : (c : ℕ) = e
    · have : (a : ℕ) - 1 ≠ e := by omega
      have h1 : (a : ℕ) - 1 + 1 = a := by omega
      simp [ha0, hce, this, h1]
    · have h1 : ((a : ℕ) - 1 = c) ↔ ((a : ℕ) = c + 1) := by omega
      simp only [ha0, hce, ↓reduceIte, h1]
      split_ifs <;> simp

/-- The block transpose of `T₀` is its inverse. -/
private theorem t0Blocks_transpose_mul :
    (of fun a b => (t0Blocks : Matrix _ _ (Matrix (Fin n) (Fin n) ℂ)) b a) * t0Blocks =
      (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ)) := by
  refine Matrix.ext fun a c => ?_
  have ha := a.isLt
  have hc := c.isLt
  have hσ : (if (a : ℕ) = e then 0 else (a : ℕ) + 1) < e + 1 := by split_ifs <;> omega
  rw [Matrix.mul_apply]
  simp only [of_apply]
  simp_rw [t0Blocks_col _ a]
  rw [sum_single_mul_left hσ, t0Blocks_col]
  simp only
  by_cases hac : a = c
  · subst hac
    split_ifs <;> first | (exfalso; omega) | simp
  · have hac' : (a : ℕ) ≠ c := fun h => hac (Fin.ext h)
    rw [one_apply_ne hac]
    split_ifs <;> first | (exfalso; omega) | simp

/-- **(7.7.6), the linearization of a polynomial eigenvalue problem** (§7.7.9): for
`A₀, …, A_d ∈ ℂ^{n×n}` (`d = e + 1 ≥ 1`), `P(λ) = A₀ + λ A₁ + ⋯ + λ^d A_d` and every `λ`,
`S(λ) [P(λ) 0; 0 I_{(d-1)n}] T(λ) = L(λ)` with the companion-form pencil `L(λ)` of unit degree,
and `S(λ)`, `T(λ)` have constant nonzero determinants: `det S(λ) = 1` and `det T(λ) = ±1`,
independent of `λ` — "`L(λ)` is a linearization of `P(λ)`". The book's two displayed steps are
the cases `d = 2, 3` of the block identity. -/
theorem equation_7_7_6 (A : Fin (e + 2) → Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    linearizationS l * linearizationDiag A l * linearizationT A l = linearizationPencil A l ∧
      (linearizationS (n := n) (e := e) l).det = 1 ∧
      ((linearizationT A l).det = 1 ∨ (linearizationT A l).det = -1) ∧
      ∀ l', (linearizationT A l').det = (linearizationT A l).det := by
  have hmul : ∀ X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) (Matrix (Fin n) (Fin n) ℂ),
      comp _ _ _ _ ℂ (X * Y) = comp _ _ _ _ ℂ X * comp _ _ _ _ ℂ Y := fun X Y =>
    (compRingEquiv (Fin (e + 1)) (Fin n) ℂ).map_mul X Y
  have hT : ∀ l', (linearizationT A l').det =
      (comp _ _ _ _ ℂ (t0Blocks (n := n) (e := e))).det := by
    intro l'
    rw [linearizationT, tBlocks_eq_mul, hmul, det_mul,
      det_comp_eq_one (X := vBlocks A l') _ _, mul_one]
    · intro a b hab
      have : (a : ℕ) ≠ b := fun h => (Fin.ne_of_gt hab) (Fin.ext h)
      have hb : (b : ℕ) ≠ e := by have := a.isLt; have := Fin.lt_def.1 hab; omega
      simp [vBlocks, this, hb]
    · intro a
      simp [vBlocks]
  refine ⟨?_, ?_, ?_, fun l' => by rw [hT, hT]⟩
  · rw [linearizationS, linearizationDiag, linearizationT, linearizationPencil, ← hmul, ← hmul,
      blocks_mul]
  · refine det_comp_eq_one (fun a b hab => ?_) fun a => ?_
    · have h1 : (a : ℕ) ≠ b := fun h => (Fin.ne_of_gt hab) (Fin.ext h)
      have h2 : (b : ℕ) ≠ a + 1 := by have := Fin.lt_def.1 hab; omega
      simp [sBlocks, h1, h2]
    · simp [sBlocks]
  · rw [hT]
    have htr : comp _ _ _ _ ℂ
        (of fun a b => (t0Blocks (n := n) (e := e)) b a) =
        (comp _ _ _ _ ℂ (t0Blocks (n := n) (e := e)))ᵀ := by
      ext ⟨a, i⟩ ⟨b, j⟩
      simp only [comp_apply, of_apply, transpose_apply, t0Blocks]
      split_ifs <;> simp [one_apply, eq_comm]
    have h1 := congrArg det (congrArg (comp _ _ _ _ ℂ) (t0Blocks_transpose_mul (n := n) (e := e)))
    rw [hmul, htr, det_mul, det_transpose, Matrix.comp_one, det_one] at h1
    exact mul_self_eq_one_iff.1 h1

end Linearization


/-! ### §7.7.6–§7.7.7 The QZ step and the QZ algorithm: exact semantics -/

section Reflectors

open GolubVanLoan.Chapter05

/-- The entries of `(I - β v vᵀ) M`. -/
private theorem refl_mul_apply (β : ℝ) (v : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i q : Fin n) :
    ((1 - β • vecMulVec v v) * M) i q = M i q - β * v i * ∑ l, v l * M l q := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    mul_apply, smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [vecMulVec_apply]
  ring

/-- The entries of `M (I - β v vᵀ)`. -/
private theorem mul_refl_apply (β : ℝ) (v : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i q : Fin n) :
    (M * (1 - β • vecMulVec v v)) i q = M i q - β * v q * ∑ l, M i l * v l := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.sub_apply, Matrix.smul_apply,
    mul_apply, smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [vecMulVec_apply]
  ring

variable {o : List (Fin n)} {v : Fin n → ℝ}

/-- A reflector supported on `o` does not change the rows outside `o`. -/
private theorem refl_mul_apply_of_not_mem (hv : ∀ l, l ∉ o → v l = 0) (β : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) {i : Fin n} (hi : i ∉ o) (q : Fin n) :
    ((1 - β • vecMulVec v v) * M) i q = M i q := by
  rw [refl_mul_apply, hv i hi]; ring

/-- A reflector supported on `o` does not change a column that vanishes on `o`. -/
private theorem refl_mul_apply_of_col (hv : ∀ l, l ∉ o → v l = 0) (β : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) {q : Fin n} (hM : ∀ l ∈ o, M l q = 0) (i : Fin n) :
    ((1 - β • vecMulVec v v) * M) i q = M i q := by
  rw [refl_mul_apply, Finset.sum_eq_zero fun l _ => ?_]
  · ring
  · by_cases hl : l ∈ o
    · rw [hM l hl, mul_zero]
    · rw [hv l hl, zero_mul]

/-- A reflector supported on `o` does not change the columns outside `o`. -/
private theorem mul_refl_apply_of_not_mem (hv : ∀ l, l ∉ o → v l = 0) (β : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) {q : Fin n} (hq : q ∉ o) :
    (M * (1 - β • vecMulVec v v)) i q = M i q := by
  rw [mul_refl_apply, hv q hq]; ring

/-- A reflector supported on `o` does not change a row that vanishes on `o`. -/
private theorem mul_refl_apply_of_row (hv : ∀ l, l ∉ o → v l = 0) (β : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) {i : Fin n} (hM : ∀ l ∈ o, M i l = 0) (q : Fin n) :
    (M * (1 - β • vecMulVec v v)) i q = M i q := by
  rw [mul_refl_apply, Finset.sum_eq_zero fun l _ => ?_]
  · ring
  · by_cases hl : l ∈ o
    · rw [hM l hl, zero_mul]
    · rw [hv l hl, mul_zero]

/-- On `o`, a reflector supported on `o` sees a column only through its entries on `o`. -/
private theorem refl_mul_apply_eq (hv : ∀ l, l ∉ o → v l = 0) (β : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) {q : Fin n} (hMu : ∀ l ∈ o, M l q = u l) {i : Fin n} (hi : i ∈ o) :
    ((1 - β • vecMulVec v v) * M) i q = ((1 - β • vecMulVec v v) *ᵥ u) i := by
  rw [refl_mul_apply, FloatingPoint.one_sub_smul_vecMulVec_mulVec_apply, hMu i hi]
  congr 2
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ o
  · rw [hMu l hl]
  · rw [hv l hl, zero_mul, zero_mul]

/-- Right multiplication by a reflector acts on each row as the (symmetric) reflector. -/
private theorem mul_refl_apply_eq (β : ℝ) (v : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i q : Fin n) :
    (M * (1 - β • vecMulVec v v)) i q = ((1 - β • vecMulVec v v) *ᵥ M i) q := by
  rw [mul_refl_apply, FloatingPoint.one_sub_smul_vecMulVec_mulVec_apply]
  simp only [dotProduct]
  congr 2
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The exact output of `house` on an index list: supported on the list, the `β` dichotomy, and
the reflector maps `x` to a multiple of `e_head` on the list. -/
private theorem houseOn_exact {o : List (Fin n)} (ho : o.Nodup) (hne : o ≠ []) (x : Fin n → ℝ) :
    (∀ l, l ∉ o → (Id.run (houseOn pure o x)).1 l = 0) ∧
      ((Id.run (houseOn pure o x)).2 = 0 ∨
        (Id.run (houseOn pure o x)).2 *
          ((Id.run (houseOn pure o x)).1 ⬝ᵥ (Id.run (houseOn pure o x)).1) = 2) ∧
      ∀ i ∈ o, i ≠ o.head hne → ((1 - (Id.run (houseOn pure o x)).2 •
        vecMulVec (Id.run (houseOn pure o x)).1 (Id.run (houseOn pure o x)).1) *ᵥ x) i = 0 := by
  obtain ⟨-, hout, hβ, -, hmul⟩ := houseOn_spec ho hne x
  refine ⟨hout, hβ, fun i hi hih => ?_⟩
  rw [hmul]
  simp [hih, hi]

private theorem nodup_three {a b c : Fin n} (h1 : (a : ℕ) ≠ b) (h2 : (a : ℕ) ≠ c)
    (h3 : (b : ℕ) ≠ c) :
    [a, b, c].Nodup := by
  refine List.nodup_cons.2 ⟨fun h => ?_, List.nodup_cons.2 ⟨fun h => ?_, List.nodup_singleton _⟩⟩
  · rcases List.mem_cons.1 h with h | h
    · exact h1 (congrArg Fin.val h)
    · exact h2 (congrArg Fin.val (List.mem_singleton.1 h))
  · exact h3 (congrArg Fin.val (List.mem_singleton.1 h))

private theorem nodup_two {a b : Fin n} (h1 : (a : ℕ) ≠ b) : [a, b].Nodup :=
  List.nodup_cons.2 ⟨by simpa [Fin.ext_iff] using h1, List.nodup_singleton _⟩

end Reflectors

section QZStepInvariant

open GolubVanLoan.Chapter05

/-- The loop invariant of the QZ step on the block `p, …, r`, before the step at `j`: the
equivalence with the reflector data, the `β` dichotomy and support of the data, the bulge of `A`
(only at `(j+1, j-1)`, `(j+2, j-1)`, `(j+2, j)` once `j > p`), `B` upper triangular, the block
decoupled from column `p - 1` and row `r + 1`, the current `x, y, z` read from column `j - 1`,
the initial state at `j = p`, and the first left reflector. -/
private structure QZStepInv (A₀ B₀ : Matrix (Fin n) (Fin n) ℝ) (p r j : ℕ) (x₀ y₀ z₀ : ℝ)
    (st : QZStepState n) : Prop where
  eqA : st.A = (householderProduct st.dQ)ᵀ * A₀ * householderProduct st.dZ
  eqB : st.B = (householderProduct st.dQ)ᵀ * B₀ * householderProduct st.dZ
  betaQ : ∀ d ∈ st.dQ, d.2 = 0 ∨ d.2 * (d.1 ⬝ᵥ d.1) = 2
  betaZ : ∀ d ∈ st.dZ, d.2 = 0 ∨ d.2 * (d.1 ⬝ᵥ d.1) = 2
  suppQ : ∀ d ∈ st.dQ, ∀ l : Fin n, ((l : ℕ) < p ∨ r < l) → d.1 l = 0
  suppZ : ∀ d ∈ st.dZ, ∀ l : Fin n, ((l : ℕ) < p ∨ r < l) → d.1 l = 0
  bulge : ∀ i c : Fin n, (c : ℕ) + 1 < i → ¬ (p < j ∧ (((i : ℕ) = j + 1 ∧ (c : ℕ) + 1 = j) ∨
    ((i : ℕ) = j + 2 ∧ (c : ℕ) + 1 = j) ∨ ((i : ℕ) = j + 2 ∧ (c : ℕ) = j))) → st.A i c = 0
  tri : ∀ i c : Fin n, (c : ℕ) < i → st.B i c = 0
  col : ∀ i c : Fin n, 0 < p → (c : ℕ) + 1 = p → p ≤ (i : ℕ) → st.A i c = 0
  row : ∀ i c : Fin n, (i : ℕ) = r + 1 → (c : ℕ) ≤ r → st.A i c = 0
  xyz : ∀ i c : Fin n, p < j → (c : ℕ) + 1 = j →
    ((i : ℕ) = j → st.x = st.A i c) ∧ ((i : ℕ) = j + 1 → st.y = st.A i c) ∧
      ((i : ℕ) = j + 2 → j + 2 ≤ r → st.z = st.A i c)
  init : j = p → st.dQ = [] ∧ st.x = x₀ ∧ st.y = y₀ ∧ st.z = z₀
  first : p < j → ∃ d₀ rest, st.dQ = d₀ :: rest ∧ (∀ l : Fin n, (l : ℕ) ≠ p →
      ((1 - d₀.2 • vecMulVec d₀.1 d₀.1) *ᵥ fun i : Fin n => if (i : ℕ) = p then x₀ else
        if (i : ℕ) = p + 1 then y₀ else if (i : ℕ) = p + 2 then z₀ else 0) l = 0) ∧
      ∀ d ∈ rest, ∀ l : Fin n, (l : ℕ) = p → d.1 l = 0

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

set_option maxHeartbeats 1000000 in
-- the three reflector updates of one bulge-chasing step are checked entry by entry
/-- One step of the QZ step's loop keeps the invariant, moving the bulge from `j` to `j + 1`. -/
private theorem qzStep_inv {p r : ℕ} (hr : r < n) {x₀ y₀ z₀ : ℝ} {j : Fin n} (hpj : p ≤ j)
    (hjr : (j : ℕ) + 2 ≤ r) {st : QZStepState n}
    (h : QZStepInv A₀ B₀ p r j x₀ y₀ z₀ st) :
    QZStepInv A₀ B₀ p r (j + 1) x₀ y₀ z₀
      (Id.run (qzStep pure r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st)) := by
  set j₁ : Fin n := ⟨(j : ℕ) + 1, by omega⟩ with hj₁
  set j₂ : Fin n := ⟨(j : ℕ) + 2, by omega⟩ with hj₂
  have hj₁v : (j₁ : ℕ) = j + 1 := rfl
  have hj₂v : (j₂ : ℕ) = j + 2 := rfl
  have hmem : ∀ i : Fin n, i ∈ [j, j₁, j₂] ↔
      ((i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hj₁v,
      hj₂v]
  have hmem' : ∀ i : Fin n, i ∈ [j₂, j₁, j] ↔
      ((i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hj₁v,
      hj₂v]
    omega
  have hmem₃ : ∀ i : Fin n, i ∈ [j₁, j] ↔ ((i : ℕ) = j ∨ (i : ℕ) = j + 1) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hj₁v]
    omega
  have hnd : [j, j₁, j₂].Nodup := nodup_three (by omega) (by omega) (by omega)
  have hnd' : [j₂, j₁, j].Nodup := nodup_three (by omega) (by omega) (by omega)
  have hnd₃ : [j₁, j].Nodup := nodup_two (by omega)
  -- the first reflector `Q_k`
  obtain ⟨hq0, hqβ, hqz⟩ := houseOn_exact hnd (List.cons_ne_nil _ _) (fun i =>
    if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z else 0)
  set q := Id.run (houseOn pure [j, j₁, j₂] (fun i =>
    if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z else 0)) with hq
  set P₁ : Matrix (Fin n) (Fin n) ℝ := 1 - q.2 • vecMulVec q.1 q.1 with hP₁
  set A₁ := P₁ * st.A with hA₁
  set B₁ := P₁ * st.B with hB₁
  -- the reflector `Z_{k1}`
  obtain ⟨hz0, hzβ, hzz⟩ := houseOn_exact hnd' (List.cons_ne_nil _ _) (B₁ j₂)
  set z₁ := Id.run (houseOn pure [j₂, j₁, j] (B₁ j₂)) with hz₁
  set P₂ : Matrix (Fin n) (Fin n) ℝ := 1 - z₁.2 • vecMulVec z₁.1 z₁.1 with hP₂
  set A₂ := A₁ * P₂ with hA₂
  set B₂ := B₁ * P₂ with hB₂
  -- the reflector `Z_{k2}`
  obtain ⟨hw0, hwβ, hwz⟩ := houseOn_exact hnd₃ (List.cons_ne_nil _ _) (B₂ j₁)
  set z₂ := Id.run (houseOn pure [j₁, j] (B₂ j₁)) with hz₂
  set P₃ : Matrix (Fin n) (Fin n) ℝ := 1 - z₂.2 • vecMulVec z₂.1 z₂.1 with hP₃
  set A₃ := A₂ * P₃ with hA₃
  set B₃ := B₂ * P₃ with hB₃
  have hrun : Id.run (qzStep pure r j j₁ j₂ st) = ⟨A₃, B₃, st.dQ ++ [q], st.dZ ++ [z₁, z₂],
      A₃ j₁ j, A₃ j₂ j, if (j : ℕ) + 3 ≤ r then qzEntry A₃ ((j : ℕ) + 3) j else st.z⟩ := by
    simp only [qzStep, Id.run_bind, Id.run_pure]
    rw [← hq, householderApplyLeft_spec_of_forall_mem hnd (List.nodup_finRange n)
      List.mem_finRange hq0, householderApplyLeft_spec_of_forall_mem hnd
      (List.nodup_finRange n) List.mem_finRange hq0, ← hP₁, ← hA₁, ← hB₁, ← hz₁,
      householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd' List.mem_finRange
      hz0, householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd'
      List.mem_finRange hz0, ← hP₂, ← hA₂, ← hB₂, ← hz₂,
      householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd₃ List.mem_finRange
      hw0, householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd₃
      List.mem_finRange hw0]
  rw [hrun]
  have hjpos : p < (j : ℕ) + 1 := by omega
  -- the columns and rows of the reflectors
  have hq0' : ∀ l : Fin n, ¬ ((l : ℕ) = j ∨ (l : ℕ) = j + 1 ∨ (l : ℕ) = j + 2) → q.1 l = 0 :=
    fun l hl => hq0 l ((hmem l).not.2 hl)
  have hz0' : ∀ l : Fin n, ¬ ((l : ℕ) = j ∨ (l : ℕ) = j + 1 ∨ (l : ℕ) = j + 2) → z₁.1 l = 0 :=
    fun l hl => hz0 l ((hmem' l).not.2 hl)
  have hw0' : ∀ l : Fin n, ¬ ((l : ℕ) = j ∨ (l : ℕ) = j + 1) → z₂.1 l = 0 :=
    fun l hl => hw0 l ((hmem₃ l).not.2 hl)
  -- `A₁`: the bulge column `j - 1` is cleared, a fill-in may appear at `(j + 2, j)`
  have hA₁z : ∀ i c : Fin n, (c : ℕ) + 1 < i → ¬ ((i : ℕ) = j + 2 ∧ (c : ℕ) = j) →
      A₁ i c = 0 := by
    intro i c hic hne
    by_cases hio : (i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2
    · by_cases hcj : (c : ℕ) + 1 = j
      · by_cases hpj' : p < (j : ℕ)
        · -- the reflector clears the column `j - 1` below its first entry
          have hcol : ∀ l ∈ [j, j₁, j₂], st.A l c = (fun i =>
              if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z else 0) l := by
            intro l hl
            obtain ⟨hx, hy, hz⟩ := h.xyz l c hpj' hcj
            rw [hmem] at hl
            rcases hl with hl | hl | hl
            · have : l = j := Fin.ext hl
              subst this
              simp [hx rfl]
            · have : l = j₁ := Fin.ext hl
              subst this
              have hne : j₁ ≠ j := fun e => by rw [e] at hj₁v; omega
              simp [hne, hy hj₁v]
            · have : l = j₂ := Fin.ext hl
              subst this
              have hne : j₂ ≠ j := fun e => by rw [e] at hj₂v; omega
              have hne' : j₂ ≠ j₁ := fun e => by rw [e] at hj₂v; omega
              simp [hne, hne', hz hj₂v hjr]
          rw [hA₁, refl_mul_apply_eq hq0 _ _ _ hcol ((hmem i).2 hio)]
          exact hqz i ((hmem i).2 hio) (fun e => by rw [e, List.head_cons] at hic; omega)
        · -- `j = p`: the column `p - 1` vanishes on the block
          have hp0 : 0 < p := by omega
          have hcol : ∀ l ∈ [j, j₁, j₂], st.A l c = 0 := fun l hl => by
            rw [hmem] at hl
            exact h.col l c hp0 (by omega) (by omega)
          rw [hA₁, refl_mul_apply_of_col hq0 _ _ hcol]
          exact h.col i c hp0 (by omega) (by omega)
      · have hcol : ∀ l ∈ [j, j₁, j₂], st.A l c = 0 := fun l hl => by
          rw [hmem] at hl
          exact h.bulge l c (by omega) (by omega)
        rw [hA₁, refl_mul_apply_of_col hq0 _ _ hcol]
        exact h.bulge i c hic (by omega)
    · rw [hA₁, refl_mul_apply_of_not_mem hq0 _ _ ((hmem i).not.2 hio)]
      exact h.bulge i c hic (by omega)
  -- `B₁`: upper triangular except in the rows `j + 1, j + 2`, columns `j, j + 1`
  have hB₁z : ∀ i c : Fin n, (c : ℕ) < i →
      ¬ (((i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2) ∧ ((c : ℕ) = j ∨ (c : ℕ) = j + 1)) → B₁ i c = 0 := by
    intro i c hic hne
    by_cases hio : (i : ℕ) = j ∨ (i : ℕ) = j + 1 ∨ (i : ℕ) = j + 2
    · have hcol : ∀ l ∈ [j, j₁, j₂], st.B l c = 0 := fun l hl => by
        rw [hmem] at hl
        exact h.tri l c (by omega)
      rw [hB₁, refl_mul_apply_of_col hq0 _ _ hcol]
      exact h.tri i c hic
    · rw [hB₁, refl_mul_apply_of_not_mem hq0 _ _ ((hmem i).not.2 hio)]
      exact h.tri i c hic
  -- `B₂`: only `(j + 1, j)` below the diagonal
  have hB₂z : ∀ i c : Fin n, (c : ℕ) < i → ¬ ((i : ℕ) = j + 1 ∧ (c : ℕ) = j) → B₂ i c = 0 := by
    intro i c hic hne
    by_cases hco : (c : ℕ) = j ∨ (c : ℕ) = j + 1 ∨ (c : ℕ) = j + 2
    · by_cases hi2 : (i : ℕ) = j + 2
      · have hi : i = j₂ := Fin.ext hi2
        subst hi
        rw [hB₂, mul_refl_apply_eq]
        exact hzz c ((hmem' c).2 hco) (fun e => by rw [e, List.head_cons] at hic; omega)
      · have hrow : ∀ l ∈ [j₂, j₁, j], B₁ i l = 0 := fun l hl => by
          rw [hmem'] at hl
          exact hB₁z i l (by omega) (by omega)
        rw [hB₂, mul_refl_apply_of_row hz0 _ _ hrow]
        exact hB₁z i c hic (by omega)
    · rw [hB₂, mul_refl_apply_of_not_mem hz0 _ _ _ ((hmem' c).not.2 hco)]
      exact hB₁z i c hic (by omega)
  -- `A₂`: the bulge moves to `(j + 2, j)`, `(j + 3, j)`, `(j + 3, j + 1)`
  have hA₂z : ∀ i c : Fin n, (c : ℕ) + 1 < i → ¬ (((i : ℕ) = j + 2 ∧ (c : ℕ) = j) ∨
      ((i : ℕ) = j + 3 ∧ ((c : ℕ) = j ∨ (c : ℕ) = j + 1))) → A₂ i c = 0 := by
    intro i c hic hne
    by_cases hco : (c : ℕ) = j ∨ (c : ℕ) = j + 1 ∨ (c : ℕ) = j + 2
    · have hrow : ∀ l ∈ [j₂, j₁, j], A₁ i l = 0 := fun l hl => by
        rw [hmem'] at hl
        exact hA₁z i l (by omega) (by omega)
      rw [hA₂, mul_refl_apply_of_row hz0 _ _ hrow]
      exact hA₁z i c hic (by omega)
    · rw [hA₂, mul_refl_apply_of_not_mem hz0 _ _ _ ((hmem' c).not.2 hco)]
      exact hA₁z i c hic (by omega)
  -- `B₃` is upper triangular
  have hB₃z : ∀ i c : Fin n, (c : ℕ) < i → B₃ i c = 0 := by
    intro i c hic
    by_cases hco : (c : ℕ) = j ∨ (c : ℕ) = j + 1
    · by_cases hi1 : (i : ℕ) = j + 1
      · have hi : i = j₁ := Fin.ext hi1
        subst hi
        rw [hB₃, mul_refl_apply_eq]
        exact hwz c ((hmem₃ c).2 hco) (fun e => by rw [e, List.head_cons] at hic; omega)
      · have hrow : ∀ l ∈ [j₁, j], B₂ i l = 0 := fun l hl => by
          rw [hmem₃] at hl
          exact hB₂z i l (by omega) (by omega)
        rw [hB₃, mul_refl_apply_of_row hw0 _ _ hrow]
        exact hB₂z i c hic (by omega)
    · rw [hB₃, mul_refl_apply_of_not_mem hw0 _ _ _ ((hmem₃ c).not.2 hco)]
      exact hB₂z i c hic (by omega)
  -- `A₃` keeps the new bulge
  have hA₃z : ∀ i c : Fin n, (c : ℕ) + 1 < i → ¬ (((i : ℕ) = j + 2 ∧ (c : ℕ) = j) ∨
      ((i : ℕ) = j + 3 ∧ ((c : ℕ) = j ∨ (c : ℕ) = j + 1))) → A₃ i c = 0 := by
    intro i c hic hne
    by_cases hco : (c : ℕ) = j ∨ (c : ℕ) = j + 1
    · have hrow : ∀ l ∈ [j₁, j], A₂ i l = 0 := fun l hl => by
        rw [hmem₃] at hl
        exact hA₂z i l (by omega) (by omega)
      rw [hA₃, mul_refl_apply_of_row hw0 _ _ hrow]
      exact hA₂z i c hic (by omega)
    · rw [hA₃, mul_refl_apply_of_not_mem hw0 _ _ _ ((hmem₃ c).not.2 hco)]
      exact hA₂z i c hic (by omega)
  -- the decoupling of column `p - 1` and row `r + 1`
  have hcol₃ : ∀ i c : Fin n, 0 < p → (c : ℕ) + 1 = p → p ≤ (i : ℕ) → A₃ i c = 0 := by
    intro i c hp0 hc hi
    have hco : ¬ ((c : ℕ) = j ∨ (c : ℕ) = j + 1 ∨ (c : ℕ) = j + 2) := by omega
    have hco₃ : ¬ ((c : ℕ) = j ∨ (c : ℕ) = j + 1) := by omega
    rw [hA₃, mul_refl_apply_of_not_mem hw0 _ _ _ ((hmem₃ c).not.2 hco₃), hA₂,
      mul_refl_apply_of_not_mem hz0 _ _ _ ((hmem' c).not.2 hco), hA₁,
      refl_mul_apply_of_col hq0 _ _ (fun l hl => by
        rw [hmem] at hl; exact h.col l c hp0 hc (by omega))]
    exact h.col i c hp0 hc hi
  have hrowA₁ : ∀ i c : Fin n, (i : ℕ) = r + 1 → (c : ℕ) ≤ r → A₁ i c = 0 := by
    intro i c hi hc
    rw [hA₁, refl_mul_apply_of_not_mem hq0 _ _ ((hmem i).not.2 (by omega))]
    exact h.row i c hi hc
  have hrowA₂ : ∀ i c : Fin n, (i : ℕ) = r + 1 → (c : ℕ) ≤ r → A₂ i c = 0 := by
    intro i c hi hc
    rw [hA₂, mul_refl_apply_of_row hz0 _ _ (fun l hl => by
      rw [hmem'] at hl; exact hrowA₁ i l hi (by omega))]
    exact hrowA₁ i c hi hc
  have hrow₃ : ∀ i c : Fin n, (i : ℕ) = r + 1 → (c : ℕ) ≤ r → A₃ i c = 0 := by
    intro i c hi hc
    rw [hA₃, mul_refl_apply_of_row hw0 _ _ (fun l hl => by
      rw [hmem₃] at hl; exact hrowA₂ i l hi (by omega))]
    exact hrowA₂ i c hi hc
  -- the reflector products
  have hsym : ∀ d : (Fin n → ℝ) × ℝ, (1 - d.2 • vecMulVec d.1 d.1)ᵀ = 1 - d.2 • vecMulVec d.1 d.1 :=
    fun d => transpose_one_sub_smul_vecMulVec _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hB₃z, hcol₃, hrow₃, ?_, fun e => by omega, ?_⟩
  · -- `eqA`
    simp only
    rw [householderProduct_concat, show st.dZ ++ [z₁, z₂] = (st.dZ ++ [z₁]) ++ [z₂] by simp,
      householderProduct_concat, householderProduct_concat, transpose_mul, hsym, hA₃, hA₂, hA₁,
      h.eqA]
    simp only [hP₁, hP₂, hP₃, Matrix.mul_assoc]
  · simp only
    rw [householderProduct_concat, show st.dZ ++ [z₁, z₂] = (st.dZ ++ [z₁]) ++ [z₂] by simp,
      householderProduct_concat, householderProduct_concat, transpose_mul, hsym, hB₃, hB₂, hB₁,
      h.eqB]
    simp only [hP₁, hP₂, hP₃, Matrix.mul_assoc]
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.betaQ d hd
    · rw [List.mem_singleton.1 hd]; exact hqβ
  · intro d hd
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd
    · exact h.betaZ d hd
    · rw [hd]; exact hzβ
    · rw [hd]; exact hwβ
  · intro d hd l hl
    rcases List.mem_append.1 hd with hd | hd
    · exact h.suppQ d hd l hl
    · rw [List.mem_singleton.1 hd]; exact hq0' l (by omega)
  · intro d hd l hl
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd
    · exact h.suppZ d hd l hl
    · rw [hd]; exact hz0' l (by omega)
    · rw [hd]; exact hw0' l (by omega)
  · -- the new bulge
    intro i c hic hne
    exact hA₃z i c hic (by push_cast at hne; omega)
  · -- `x, y, z` for the next step
    intro i c _ hc
    push_cast at hc ⊢
    have hcj : c = j := Fin.ext (by omega)
    subst hcj
    refine ⟨fun hi => ?_, fun hi => ?_, fun hi hir => ?_⟩
    · congr 1
      exact Fin.ext (by omega)
    · congr 1
      exact Fin.ext (by omega)
    · simp only [show (c : ℕ) + 3 ≤ r by omega, ↓reduceIte]
      rw [qzEntry_of_lt A₃ (by omega) c.isLt]
      congr 1
      exact Fin.ext (by simp; omega)
  · -- the first reflector
    intro _
    by_cases hjp : (j : ℕ) = p
    · obtain ⟨hdQ, hx, hy, hz⟩ := h.init hjp
      refine ⟨q, [], by simp [hdQ], fun l hl => ?_, by simp⟩
      have hu : (fun i : Fin n => if (i : ℕ) = p then x₀ else if (i : ℕ) = p + 1 then y₀
          else if (i : ℕ) = p + 2 then z₀ else 0) =
          fun i => if i = j then st.x else if i = j₁ then st.y else if i = j₂ then st.z
            else 0 := by
        funext i
        simp only [Fin.ext_iff, hj₁v, hj₂v, hjp, hx, hy, hz]
      rw [hu]
      by_cases hlo : (l : ℕ) = j ∨ (l : ℕ) = j + 1 ∨ (l : ℕ) = j + 2
      · exact hqz l ((hmem l).2 hlo) (fun e => by rw [e, List.head_cons] at hl; omega)
      · rw [FloatingPoint.one_sub_smul_vecMulVec_mulVec_apply, hq0' l hlo]
        have h1 : l ≠ j := fun e => by rw [e] at hlo; omega
        have h2 : l ≠ j₁ := fun e => by rw [e] at hlo; omega
        have h3 : l ≠ j₂ := fun e => by rw [e] at hlo; omega
        simp [h1, h2, h3]
    · obtain ⟨d₀, rest, hdQ, hd₀, hrest⟩ := h.first (by omega)
      refine ⟨d₀, rest ++ [q], by simp [hdQ], hd₀, fun d hd l hl => ?_⟩
      rcases List.mem_append.1 hd with hd | hd
      · exact hrest d hd l hl
      · rw [List.mem_singleton.1 hd]; exact hq0' l (by omega)

end QZStepInvariant

section QZStepSpec

open GolubVanLoan.Chapter05

variable {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ}

/-- The invariant of the QZ step holds before its loop. -/
private theorem qzStepInv_init {p r : ℕ} (hr : r < n) {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsUpperHessenberg) (hB : B.IsUpperTriangular)
    (hp : 0 < p → qzEntry A p (p - 1) = 0) (hr₁ : qzEntry A (r + 1) r = 0) (x₀ y₀ z₀ : ℝ) :
    QZStepInv A B p r p x₀ y₀ z₀ ⟨A, B, [], [], x₀, y₀, z₀⟩ := by
  rw [isUpperHessenberg_iff_fin] at hA
  rw [isUpperTriangular_iff_fin] at hB
  refine ⟨by simp [householderProduct_nil], by simp [householderProduct_nil], by simp, by simp,
    by simp, by simp, fun i c hic _ => hA i c hic, hB, fun i c hp0 hc hi => ?_,
    fun i c hi hc => ?_, fun _ _ h => absurd h (lt_irrefl p), fun _ => ⟨rfl, rfl, rfl, rfl⟩,
    fun h => absurd h (lt_irrefl p)⟩
  · by_cases hip : (i : ℕ) = p
    · have := hp hp0
      rw [qzEntry_of_lt A (by omega) (by omega)] at this
      convert this using 2 <;> exact Fin.ext (by simp; omega)
    · exact hA i c (by omega)
  · by_cases hcr : (c : ℕ) = r
    · rw [qzEntry_of_lt A (by omega) (by omega)] at hr₁
      convert hr₁ using 2 <;> exact Fin.ext (by simp; omega)
    · exact hA i c (by omega)

/-- The loop of the QZ step keeps the invariant; after it the bulge sits at `j = r - 1`. -/
private theorem qzLoop_inv {p r : ℕ} (hpr : p < r) (hr : r < n) {x₀ y₀ z₀ : ℝ}
    {st : QZStepState n} (h : QZStepInv A₀ B₀ p r p x₀ y₀ z₀ st) :
    QZStepInv A₀ B₀ p r (r - 1) x₀ y₀ z₀
      ((List.finRange n).foldl (fun st (j : Fin n) =>
        Id.run (if h : p ≤ (j : ℕ) ∧ (j : ℕ) + 2 ≤ r then
          qzStep pure r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st
        else pure st)) st) := by
  have key := foldl_induction_getElem (List.finRange n) (fun st (j : Fin n) =>
      Id.run (if h : p ≤ (j : ℕ) ∧ (j : ℕ) + 2 ≤ r then
        qzStep pure r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st
      else pure st))
    (fun t st => QZStepInv A₀ B₀ p r (min (max t p) (r - 1)) x₀ y₀ z₀ st) st
    (by rwa [show min (max 0 p) (r - 1) = p by omega]) fun t ht st hst => ?_
  · rwa [List.length_finRange, show min (max n p) (r - 1) = r - 1 by omega] at key
  · have hjt : ((List.finRange n)[t] : ℕ) = t := by simp
    by_cases hc : p ≤ ((List.finRange n)[t] : ℕ) ∧ ((List.finRange n)[t] : ℕ) + 2 ≤ r
    · simp only [hc, and_self, ↓reduceDIte]
      have := qzStep_inv hr hc.1 hc.2
        (by rwa [show min (max t p) (r - 1) = ((List.finRange n)[t] : ℕ) by omega] at hst)
      rwa [show min (max (t + 1) p) (r - 1) = ((List.finRange n)[t] : ℕ) + 1 by omega]
    · simp only [hc, ↓reduceDIte, Id.run_pure]
      rwa [show min (max (t + 1) p) (r - 1) = min (max t p) (r - 1) by omega]

/-- The state after the loop of Algorithm 7.7.2, exact arithmetic. -/
private noncomputable def qzLoopState (p : ℕ) {r : ℕ} (hr : r < n)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    QZStepState n :=
  (List.finRange n).foldl (fun st (j : Fin n) =>
    Id.run (if h : p ≤ (j : ℕ) ∧ (j : ℕ) + 2 ≤ r then
      qzStep pure r j ⟨(j : ℕ) + 1, by omega⟩ ⟨(j : ℕ) + 2, by omega⟩ st
    else pure st))
    ⟨A, B, [], [], (Id.run (qzShiftVector pure p r A B)).1,
      (Id.run (qzShiftVector pure p r A B)).2.1, (Id.run (qzShiftVector pure p r A B)).2.2⟩

/-- The unfolded exact run of Algorithm 7.7.2. -/
private theorem algorithm_7_7_2_pure {p r : ℕ} (hpr : p < r) (hr : r < n)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_7_7_2 pure p r A B) =
      let st := qzLoopState p hr A B
      let r₁ : Fin n := ⟨r - 1, by omega⟩
      let r' : Fin n := ⟨r, hr⟩
      let q := Id.run (houseOn pure [r₁, r'] fun i => if i = r₁ then st.x else if i = r' then st.y
        else 0)
      let A₁ := (1 - q.2 • vecMulVec q.1 q.1) * st.A
      let B₁ := (1 - q.2 • vecMulVec q.1 q.1) * st.B
      let z := Id.run (houseOn pure [r', r₁] (B₁ r'))
      ((A₁ * (1 - z.2 • vecMulVec z.1 z.1)), B₁ * (1 - z.2 • vecMulVec z.1 z.1), st.dQ ++ [q],
        st.dZ ++ [z]) := by
  have hr₁r : (⟨r - 1, by omega⟩ : Fin n) ≠ ⟨r, hr⟩ := fun e => by
    have := congrArg Fin.val e; simp at this; omega
  have hnd : [(⟨r - 1, by omega⟩ : Fin n), ⟨r, hr⟩].Nodup := nodup_two (by simp; omega)
  have hnd' : [(⟨r, hr⟩ : Fin n), ⟨r - 1, by omega⟩].Nodup := nodup_two (by simp; omega)
  simp only [algorithm_7_7_2, qzLoopState, hpr, hr, and_self, ↓reduceDIte, Id.run_bind,
    Id.run_pure, List.idRun_foldlM]
  rw [householderApplyLeft_spec_of_forall_mem hnd (List.nodup_finRange n) List.mem_finRange
      (houseOn_spec hnd (List.cons_ne_nil _ _) _).2.1,
    householderApplyLeft_spec_of_forall_mem hnd (List.nodup_finRange n) List.mem_finRange
      (houseOn_spec hnd (List.cons_ne_nil _ _) _).2.1,
    householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd' List.mem_finRange
      (houseOn_spec hnd' (List.cons_ne_nil _ _) _).2.1,
    householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hnd' List.mem_finRange
      (houseOn_spec hnd' (List.cons_ne_nil _ _) _).2.1]

/-- **Algorithm 7.7.2 on a block, exact arithmetic**: for `A` upper Hessenberg with the block
`p, …, r` decoupled (`a_{p,p-1} = 0`, `a_{r+1,r} = 0`) and `B` upper triangular, the run
`(A', B', dQ, dZ)` has `Q = householderProduct dQ` and `Z = householderProduct dZ` orthogonal and
acting on the block, `A' = Qᵀ A Z` upper Hessenberg and `B' = Qᵀ B Z` upper triangular; if the
block has at least three indices, the first reflector maps the shift vector `(x, y, z)` (at
`p, p+1, p+2`) to a multiple of `e_p` and the others fix `e_p`. -/
theorem algorithm_7_7_2_block {p r : ℕ} (hpr : p < r) (hr : r < n)
    {A B A' B' : Matrix (Fin n) (Fin n) ℝ} {dQ dZ : List ((Fin n → ℝ) × ℝ)}
    (hA : A.IsUpperHessenberg) (hB : B.IsUpperTriangular)
    (hp : 0 < p → qzEntry A p (p - 1) = 0) (hr₁ : qzEntry A (r + 1) r = 0)
    (h : Id.run (algorithm_7_7_2 pure p r A B) = (A', B', dQ, dZ)) :
    householderProduct dQ ∈ orthogonalGroup (Fin n) ℝ ∧
      householderProduct dZ ∈ orthogonalGroup (Fin n) ℝ ∧
      A' = (householderProduct dQ)ᵀ * A * householderProduct dZ ∧
      B' = (householderProduct dQ)ᵀ * B * householderProduct dZ ∧
      A'.IsUpperHessenberg ∧ B'.IsUpperTriangular ∧
      (∀ d ∈ dQ, ∀ l : Fin n, ((l : ℕ) < p ∨ r < l) → d.1 l = 0) ∧
      (∀ d ∈ dZ, ∀ l : Fin n, ((l : ℕ) < p ∨ r < l) → d.1 l = 0) ∧
      (p + 2 ≤ r → ∃ d₀ rest, dQ = d₀ :: rest ∧ (d₀.2 = 0 ∨ d₀.2 * (d₀.1 ⬝ᵥ d₀.1) = 2) ∧
        (∀ l : Fin n, (l : ℕ) ≠ p → ((1 - d₀.2 • vecMulVec d₀.1 d₀.1) *ᵥ fun i : Fin n =>
          if (i : ℕ) = p then (Id.run (qzShiftVector pure p r A B)).1
          else if (i : ℕ) = p + 1 then (Id.run (qzShiftVector pure p r A B)).2.1
          else if (i : ℕ) = p + 2 then (Id.run (qzShiftVector pure p r A B)).2.2 else 0) l = 0) ∧
        ∀ d ∈ rest, ∀ l : Fin n, (l : ℕ) = p → d.1 l = 0) := by
  have hinv : QZStepInv A B p r (r - 1) (Id.run (qzShiftVector pure p r A B)).1
      (Id.run (qzShiftVector pure p r A B)).2.1 (Id.run (qzShiftVector pure p r A B)).2.2
      (qzLoopState p hr A B) :=
    qzLoop_inv hpr hr (qzStepInv_init hr hA hB hp hr₁ _ _ _)
  rw [algorithm_7_7_2_pure hpr hr] at h
  dsimp only at h
  generalize qzLoopState p hr A B = st at hinv h
  set r₁ : Fin n := ⟨r - 1, by omega⟩ with hr₁def
  set r' : Fin n := ⟨r, hr⟩ with hr'def
  have hr₁v : (r₁ : ℕ) = r - 1 := rfl
  have hr'v : (r' : ℕ) = r := rfl
  have hmem : ∀ i : Fin n, i ∈ [r₁, r'] ↔ ((i : ℕ) = r - 1 ∨ (i : ℕ) = r) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hr₁v, hr'v]
  have hmem' : ∀ i : Fin n, i ∈ [r', r₁] ↔ ((i : ℕ) = r - 1 ∨ (i : ℕ) = r) := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hr₁v, hr'v]
    omega
  have hnd : [r₁, r'].Nodup := nodup_two (by omega)
  have hnd' : [r', r₁].Nodup := nodup_two (by omega)
  obtain ⟨hq0, hqβ, hqz⟩ := houseOn_exact hnd (List.cons_ne_nil _ _) (fun i =>
    if i = r₁ then st.x else if i = r' then st.y else 0)
  set q := Id.run (houseOn pure [r₁, r'] (fun i =>
    if i = r₁ then st.x else if i = r' then st.y else 0)) with hq
  set P₁ : Matrix (Fin n) (Fin n) ℝ := 1 - q.2 • vecMulVec q.1 q.1 with hP₁
  set A₁ := P₁ * st.A with hA₁
  set B₁ := P₁ * st.B with hB₁
  obtain ⟨hz0, hzβ, hzz⟩ := houseOn_exact hnd' (List.cons_ne_nil _ _) (B₁ r')
  set z := Id.run (houseOn pure [r', r₁] (B₁ r')) with hz
  set P₂ : Matrix (Fin n) (Fin n) ℝ := 1 - z.2 • vecMulVec z.1 z.1 with hP₂
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  have hq0' : ∀ l : Fin n, ¬ ((l : ℕ) = r - 1 ∨ (l : ℕ) = r) → q.1 l = 0 :=
    fun l hl => hq0 l ((hmem l).not.2 hl)
  have hz0' : ∀ l : Fin n, ¬ ((l : ℕ) = r - 1 ∨ (l : ℕ) = r) → z.1 l = 0 :=
    fun l hl => hz0 l ((hmem' l).not.2 hl)
  -- `A₁` is upper Hessenberg: the reflector clears the last bulge entry `(r, r - 2)`
  have hA₁z : ∀ i c : Fin n, (c : ℕ) + 1 < i → A₁ i c = 0 := by
    intro i c hic
    by_cases hio : (i : ℕ) = r - 1 ∨ (i : ℕ) = r
    · by_cases hcj : (c : ℕ) + 1 = r - 1
      · by_cases hpj : p < r - 1
        · have hcol : ∀ l ∈ [r₁, r'], st.A l c = (fun i =>
              if i = r₁ then st.x else if i = r' then st.y else 0) l := by
            intro l hl
            obtain ⟨hx, hy, -⟩ := hinv.xyz l c hpj hcj
            rw [hmem] at hl
            rcases hl with hl | hl
            · have : l = r₁ := Fin.ext hl
              subst this
              simp [hx rfl]
            · have : l = r' := Fin.ext hl
              subst this
              have hne : r' ≠ r₁ := fun e => by rw [e] at hr'v; omega
              simp [hne, hy (by omega)]
          rw [hA₁, refl_mul_apply_eq hq0 _ _ _ hcol ((hmem i).2 hio)]
          exact hqz i ((hmem i).2 hio) (fun e => by rw [e, List.head_cons] at hic; omega)
        · have hp0 : 0 < p := by omega
          have hcol : ∀ l ∈ [r₁, r'], st.A l c = 0 := fun l hl => by
            rw [hmem] at hl
            exact hinv.col l c hp0 (by omega) (by omega)
          rw [hA₁, refl_mul_apply_of_col hq0 _ _ hcol]
          exact hinv.col i c hp0 (by omega) (by omega)
      · have hcol : ∀ l ∈ [r₁, r'], st.A l c = 0 := fun l hl => by
          rw [hmem] at hl
          exact hinv.bulge l c (by omega) (by omega)
        rw [hA₁, refl_mul_apply_of_col hq0 _ _ hcol]
        exact hinv.bulge i c hic (by omega)
    · rw [hA₁, refl_mul_apply_of_not_mem hq0 _ _ ((hmem i).not.2 hio)]
      by_cases hir : (i : ℕ) = r + 1
      · exact hinv.row i c hir (by omega)
      · exact hinv.bulge i c hic (by omega)
  -- `B₁`: upper triangular except at `(r, r - 1)`
  have hB₁z : ∀ i c : Fin n, (c : ℕ) < i → ¬ ((i : ℕ) = r ∧ (c : ℕ) = r - 1) → B₁ i c = 0 := by
    intro i c hic hne
    by_cases hio : (i : ℕ) = r - 1 ∨ (i : ℕ) = r
    · have hcol : ∀ l ∈ [r₁, r'], st.B l c = 0 := fun l hl => by
        rw [hmem] at hl
        exact hinv.tri l c (by omega)
      rw [hB₁, refl_mul_apply_of_col hq0 _ _ hcol]
      exact hinv.tri i c hic
    · rw [hB₁, refl_mul_apply_of_not_mem hq0 _ _ ((hmem i).not.2 hio)]
      exact hinv.tri i c hic
  have hsym : ∀ d : (Fin n → ℝ) × ℝ,
      (1 - d.2 • vecMulVec d.1 d.1)ᵀ = 1 - d.2 • vecMulVec d.1 d.1 :=
    fun d => transpose_one_sub_smul_vecMulVec _ _
  have hβQ : ∀ d ∈ st.dQ ++ [q], d.2 = 0 ∨ d.2 * (d.1 ⬝ᵥ d.1) = 2 := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hinv.betaQ d hd
    · rw [List.mem_singleton.1 hd]; exact hqβ
  have hβZ : ∀ d ∈ st.dZ ++ [z], d.2 = 0 ∨ d.2 * (d.1 ⬝ᵥ d.1) = 2 := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hinv.betaZ d hd
    · rw [List.mem_singleton.1 hd]; exact hzβ
  refine ⟨householderProduct_mem_orthogonalGroup hβQ, householderProduct_mem_orthogonalGroup hβZ,
    ?_, ?_, ?_, ?_, ?_, ?_, fun hpr2 => ?_⟩
  · rw [householderProduct_concat, householderProduct_concat, transpose_mul, hsym, hA₁,
      hinv.eqA]
    simp only [hP₁, hP₂, Matrix.mul_assoc]
  · rw [householderProduct_concat, householderProduct_concat, transpose_mul, hsym, hB₁,
      hinv.eqB]
    simp only [hP₁, hP₂, Matrix.mul_assoc]
  · -- `A₁ P₂` is upper Hessenberg
    rw [isUpperHessenberg_iff_fin]
    intro i c hic
    by_cases hco : (c : ℕ) = r - 1 ∨ (c : ℕ) = r
    · have hrow : ∀ l ∈ [r', r₁], A₁ i l = 0 := fun l hl => by
        rw [hmem'] at hl
        by_cases hi : (i : ℕ) = r + 1 ∧ (l : ℕ) = r
        · rw [hA₁, refl_mul_apply_of_not_mem hq0 _ _ ((hmem i).not.2 (by omega))]
          exact hinv.row i l hi.1 (by omega)
        · exact hA₁z i l (by omega)
      rw [mul_refl_apply_of_row hz0 _ _ hrow]
      exact hA₁z i c hic
    · rw [mul_refl_apply_of_not_mem hz0 _ _ _ ((hmem' c).not.2 hco)]
      exact hA₁z i c hic
  · -- `B₁ P₂` is upper triangular
    rw [isUpperTriangular_iff_fin]
    intro i c hic
    by_cases hco : (c : ℕ) = r - 1 ∨ (c : ℕ) = r
    · by_cases hi : (i : ℕ) = r
      · have hi' : i = r' := Fin.ext hi
        subst hi'
        rw [mul_refl_apply_eq]
        exact hzz c ((hmem' c).2 hco) (fun e => by rw [e, List.head_cons] at hic; omega)
      · have hrow : ∀ l ∈ [r', r₁], B₁ i l = 0 := fun l hl => by
          rw [hmem'] at hl
          exact hB₁z i l (by omega) (by omega)
        rw [mul_refl_apply_of_row hz0 _ _ hrow]
        exact hB₁z i c hic (by omega)
    · rw [mul_refl_apply_of_not_mem hz0 _ _ _ ((hmem' c).not.2 hco)]
      exact hB₁z i c hic (by omega)
  · intro d hd l hl
    rcases List.mem_append.1 hd with hd | hd
    · exact hinv.suppQ d hd l hl
    · rw [List.mem_singleton.1 hd]; exact hq0' l (by omega)
  · intro d hd l hl
    rcases List.mem_append.1 hd with hd | hd
    · exact hinv.suppZ d hd l hl
    · rw [List.mem_singleton.1 hd]; exact hz0' l (by omega)
  · obtain ⟨d₀, rest, hdQ, hd₀, hrest⟩ := hinv.first (by omega)
    refine ⟨d₀, rest ++ [q], by rw [hdQ]; rfl, hinv.betaQ d₀ (by rw [hdQ]; exact
      List.mem_cons_self), hd₀, fun d hd l hl => ?_⟩
    rcases List.mem_append.1 hd with hd | hd
    · exact hrest d hd l hl
    · rw [List.mem_singleton.1 hd]; exact hq0' l (by omega)

end QZStepSpec

/-! ### Algorithm 7.7.2 performs a Francis step on `A B⁻¹` -/

section QZFrancis

open GolubVanLoan.Chapter05

/-- The entries of a product of an upper Hessenberg and an upper triangular matrix. -/
private theorem hess_mul_tri_apply {M B : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsUpperHessenberg)
    (hB : B.IsUpperTriangular) (i c : Fin n) :
    (M * B) i c =
      ∑ k : Fin n, if (i : ℕ) ≤ (k : ℕ) + 1 ∧ (k : ℕ) ≤ c then M i k * B k c else 0 := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rfl
  · rcases not_and_or.1 h with h | h
    · rw [isUpperHessenberg_iff_fin.1 hM i k (by omega), zero_mul]
    · rw [isUpperTriangular_iff_fin.1 hB k c (by omega), mul_zero]

/-- A sum with one term. -/
private theorem sum_ite_one {f : Fin n → ℝ} {P : Fin n → Prop} [DecidablePred P] (a : Fin n)
    (hP : ∀ k, P k ↔ k = a) : (∑ k, if P k then f k else 0) = f a := by
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [ite_eq_right ((hP b).not.2 hb)])
    (fun h => absurd (Finset.mem_univ a) h), ite_eq_left ((hP a).2 rfl)]

/-- A sum with two terms. -/
private theorem sum_ite_two {f : Fin n → ℝ} {P : Fin n → Prop} [DecidablePred P] {a b : Fin n}
    (hab : a ≠ b) (hP : ∀ k, P k ↔ k = a ∨ k = b) :
    (∑ k, if P k then f k else 0) = f a + f b := by
  rw [Fintype.sum_eq_add a b hab (fun x hx => ite_eq_right ((hP x).not.2 (by tauto))),
    ite_eq_left ((hP a).2 (Or.inl rfl)), ite_eq_left ((hP b).2 (Or.inr rfl))]

/-- A sum with three terms. -/
private theorem sum_ite_three {f : Fin n → ℝ} {P : Fin n → Prop} [DecidablePred P]
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : ∀ k, P k ↔ k = a ∨ k = b ∨ k = c) :
    (∑ k, if P k then f k else 0) = f a + f b + f c := by
  rw [← Finset.sum_subset (Finset.subset_univ {a, b, c}) (fun x _ hx => by
      rw [ite_eq_right ((hP x).not.2 (by simpa using hx))]),
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ite_eq_left ((hP a).2 (by simp)),
    ite_eq_left ((hP b).2 (by simp)), ite_eq_left ((hP c).2 (by simp)), add_assoc]

variable {N : ℕ}

/-- **The shift vector of the QZ step is the first column of `(M - aI)(M - bI)`** for
`M = A B⁻¹` (upper Hessenberg), `a + b`, `ab` the trace and determinant of `M`'s trailing `2 × 2`
block: the forward substitutions of `qzShiftVector` compute the entries of `M` it needs. -/
private theorem qzShiftVector_full {A B M : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    (hA : A.IsUpperHessenberg) (hB : B.IsUpperTriangular) (hBd : ∀ i, B i i ≠ 0)
    (hMdef : M = A * B⁻¹) :
    Id.run (qzShiftVector pure 0 (N + 2) A B) =
      (M ⟨0, by omega⟩ ⟨0, by omega⟩ * M ⟨0, by omega⟩ ⟨0, by omega⟩ +
          M ⟨0, by omega⟩ ⟨1, by omega⟩ * M ⟨1, by omega⟩ ⟨0, by omega⟩ -
          (M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ + M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩) *
            M ⟨0, by omega⟩ ⟨0, by omega⟩ +
          (M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ * M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩ -
            M ⟨N + 1, by omega⟩ ⟨N + 2, by omega⟩ * M ⟨N + 2, by omega⟩ ⟨N + 1, by omega⟩),
        M ⟨1, by omega⟩ ⟨0, by omega⟩ * (M ⟨0, by omega⟩ ⟨0, by omega⟩ +
          M ⟨1, by omega⟩ ⟨1, by omega⟩ -
          (M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ + M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩)),
        M ⟨1, by omega⟩ ⟨0, by omega⟩ * M ⟨2, by omega⟩ ⟨1, by omega⟩) := by
  have hdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => hBd i
  have hM : M.IsUpperHessenberg := hMdef ▸ hA.mul_isUpperTriangular hB.inv
  have hMB : M * B = A := by
    rw [hMdef, Matrix.mul_assoc, nonsing_inv_mul B hdet, Matrix.mul_one]
  have hent : ∀ i c : Fin (N + 3),
      A i c = ∑ k : Fin (N + 3),
        if (i : ℕ) ≤ (k : ℕ) + 1 ∧ (k : ℕ) ≤ c then M i k * B k c else 0 := fun i c => by
    rw [← hess_mul_tri_apply hM hB, hMB]
  -- the index names
  set i0 : Fin (N + 3) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (N + 3) := ⟨1, by omega⟩ with hi1
  set i2 : Fin (N + 3) := ⟨2, by omega⟩ with hi2
  set ia : Fin (N + 3) := ⟨N, by omega⟩ with hia
  set ib : Fin (N + 3) := ⟨N + 1, by omega⟩ with hib
  set ic : Fin (N + 3) := ⟨N + 2, by omega⟩ with hic
  have v0 : (i0 : ℕ) = 0 := rfl
  have v1 : (i1 : ℕ) = 1 := rfl
  have v2 : (i2 : ℕ) = 2 := rfl
  have va : (ia : ℕ) = N := rfl
  have vb : (ib : ℕ) = N + 1 := rfl
  have vc : (ic : ℕ) = N + 2 := rfl
  have n01 : i0 ≠ i1 := fun e => by have := congrArg Fin.val e; omega
  have nab : ia ≠ ib := fun e => by have := congrArg Fin.val e; omega
  have nac : ia ≠ ic := fun e => by have := congrArg Fin.val e; omega
  have nbc : ib ≠ ic := fun e => by have := congrArg Fin.val e; omega
  -- `a = m b` entry by entry
  have e00 : A i0 i0 = M i0 i0 * B i0 i0 := by
    rw [hent, sum_ite_one i0 fun k => by simp only [Fin.ext_iff, v0]; omega]
  have e10 : A i1 i0 = M i1 i0 * B i0 i0 := by
    rw [hent, sum_ite_one i0 fun k => by simp only [Fin.ext_iff, v0, v1]; omega]
  have e01 : A i0 i1 = M i0 i0 * B i0 i1 + M i0 i1 * B i1 i1 := by
    rw [hent, sum_ite_two n01 fun k => by simp only [Fin.ext_iff, v0, v1]; omega]
  have e11 : A i1 i1 = M i1 i0 * B i0 i1 + M i1 i1 * B i1 i1 := by
    rw [hent, sum_ite_two n01 fun k => by simp only [Fin.ext_iff, v0, v1]; omega]
  have e21 : A i2 i1 = M i2 i1 * B i1 i1 := by
    rw [hent, sum_ite_one i1 fun k => by simp only [Fin.ext_iff, v1, v2]; omega]
  have eba : A ib ia = M ib ia * B ia ia := by
    rw [hent, sum_ite_one ia fun k => by simp only [Fin.ext_iff, va, vb]; omega]
  have ebb : A ib ib = M ib ia * B ia ib + M ib ib * B ib ib := by
    rw [hent, sum_ite_two nab fun k => by simp only [Fin.ext_iff, va, vb]; omega]
  have ebc : A ib ic = M ib ia * B ia ic + M ib ib * B ib ic + M ib ic * B ic ic := by
    rw [hent, sum_ite_three nab nac nbc fun k => by simp only [Fin.ext_iff, va, vb, vc]; omega]
  have ecb : A ic ib = M ic ib * B ib ib := by
    rw [hent, sum_ite_one ib fun k => by simp only [Fin.ext_iff, vb, vc]; omega]
  have ecc : A ic ic = M ic ib * B ib ic + M ic ic * B ic ic := by
    rw [hent, sum_ite_two nbc fun k => by simp only [Fin.ext_iff, vb, vc]; omega]
  have hd : ∀ {a b c : ℝ}, b ≠ 0 → a = c * b → a / b = c := fun hb h => by
    rw [h, mul_div_cancel_right₀ _ hb]
  have m00 : A i0 i0 / B i0 i0 = M i0 i0 := hd (hBd _) e00
  have m10 : A i1 i0 / B i0 i0 = M i1 i0 := hd (hBd _) e10
  have m01 : (A i0 i1 - M i0 i0 * B i0 i1) / B i1 i1 = M i0 i1 := hd (hBd _) (by rw [e01]; ring)
  have m11 : (A i1 i1 - M i1 i0 * B i0 i1) / B i1 i1 = M i1 i1 := hd (hBd _) (by rw [e11]; ring)
  have m21 : A i2 i1 / B i1 i1 = M i2 i1 := hd (hBd _) e21
  have mba : A ib ia / B ia ia = M ib ia := hd (hBd _) eba
  have mbb : (A ib ib - M ib ia * B ia ib) / B ib ib = M ib ib := hd (hBd _) (by rw [ebb]; ring)
  have mbc : (A ib ic - M ib ia * B ia ic - M ib ib * B ib ic) / B ic ic = M ib ic :=
    hd (hBd _) (by rw [ebc]; ring)
  have mcb : A ic ib / B ib ib = M ic ib := hd (hBd _) ecb
  have mcc : (A ic ic - M ic ib * B ib ic) / B ic ic = M ic ic := hd (hBd _) (by rw [ecc]; ring)
  have hrun : Id.run (qzShiftVector pure 0 (N + 2) A B) =
      (let m₁₁ := A i0 i0 / B i0 i0
       let m₂₁ := A i1 i0 / B i0 i0
       let m₁₂ := (A i0 i1 - m₁₁ * B i0 i1) / B i1 i1
       let m₂₂ := (A i1 i1 - m₂₁ * B i0 i1) / B i1 i1
       let μ := A ib ia / B ia ia
       let e := (A ib ib - μ * B ia ib) / B ib ib
       let f := (A ib ic - μ * B ia ic - e * B ib ic) / B ic ic
       let g := A ic ib / B ib ib
       let h := (A ic ic - g * B ib ic) / B ic ic
       (m₁₁ * m₁₁ + m₁₂ * m₂₁ - (e + h) * m₁₁ + (e * h - f * g),
         m₂₁ * (m₁₁ + m₂₂ - (e + h)), m₂₁ * (A i2 i1 / B i1 i1))) := by
    simp only [qzShiftVector, Id.run_bind, Id.run_pure, show 0 + 2 ≤ N + 2 by omega,
      ↓reduceIte]
    simp (disch := omega) only [qzEntry_of_lt]
    rfl
  rw [hrun]
  dsimp only
  rw [m00, m10, m01, m11, m21, mba, mbb, mbc, mcb, mcc]

/-- **Algorithm 7.7.2 (the QZ step), exact semantics.** For `A` unreduced upper Hessenberg and
`B` nonsingular upper triangular (`n ≥ 3`), the exact run `(A', B', dQ, dZ)` on the whole pencil
has `Q = householderProduct dQ` and `Z = householderProduct dZ` orthogonal, `A' = Qᵀ A Z` upper
Hessenberg and `B' = Qᵀ B Z` upper triangular, `A' B'⁻¹ = Qᵀ (A B⁻¹) Q`, and this is a Francis
step on `M = A B⁻¹` with `s`, `t` the trace and determinant of `M`'s trailing `2 × 2` block — "`Q`
has the same first column as the orthogonal similarity transformation in Algorithm 7.5.1 when it
is applied to `A B⁻¹`", and "`Ā B̄⁻¹` is essentially the same matrix that would result if a
Francis QR step were explicitly applied to `A B⁻¹`": `Q e₁ ∥ (M - aI)(M - bI) e₁`, so
`Qᵀ (M - aI)(M - bI)` is upper triangular by the implicit Q theorem
(`Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval`). -/
theorem algorithm_7_7_2_spec {N : ℕ} {A B A' B' : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    {dQ dZ : List ((Fin (N + 3) → ℝ) × ℝ)} (hA : IsUnreduced A) (hB : B.IsUpperTriangular)
    (hBd : ∀ i, B i i ≠ 0) (h : Id.run (algorithm_7_7_2 pure 0 (N + 2) A B) = (A', B', dQ, dZ)) :
    let M := A * B⁻¹
    let s := M (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc +
      M (Fin.last (N + 2)) (Fin.last (N + 2))
    let t := M (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc *
        M (Fin.last (N + 2)) (Fin.last (N + 2)) -
      M (Fin.last (N + 1)).castSucc (Fin.last (N + 2)) *
        M (Fin.last (N + 2)) (Fin.last (N + 1)).castSucc
    householderProduct dQ ∈ orthogonalGroup (Fin (N + 3)) ℝ ∧
      householderProduct dZ ∈ orthogonalGroup (Fin (N + 3)) ℝ ∧
      A' = (householderProduct dQ)ᵀ * A * householderProduct dZ ∧
      B' = (householderProduct dQ)ᵀ * B * householderProduct dZ ∧
      A'.IsUpperHessenberg ∧ B'.IsUpperTriangular ∧
      A' * B'⁻¹ = (householderProduct dQ)ᵀ * M * householderProduct dQ ∧
      IsFrancisStep s t M (A' * B'⁻¹) := by
  intro M s t
  have hAH : A.IsUpperHessenberg := hA.1
  obtain ⟨hQo, hZo, hA', hB', hA'H, hB'T, -, -, hfirst⟩ := algorithm_7_7_2_block (by omega)
    (by omega) hAH hB (fun h => absurd h (lt_irrefl 0)) (qzEntry_of_not_lt A (by omega)) h
  obtain ⟨d₀, rest, hdQ, hβ₀, hPu₀, hrest⟩ := hfirst (by omega)
  set Q := householderProduct dQ with hQ
  set Z := householderProduct dZ with hZ
  have hdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => hBd i
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff (Fin (N + 3)) ℝ).1 hZo
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff (Fin (N + 3)) ℝ).1 hQo
  have hB'inv : B'⁻¹ = Zᵀ * B⁻¹ * Q := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hB', show Zᵀ * B⁻¹ * Q * (Qᵀ * B * Z) = Zᵀ * (B⁻¹ * ((Q * Qᵀ) * B)) * Z by
      simp only [Matrix.mul_assoc], hQQ, Matrix.one_mul, nonsing_inv_mul B hdet, Matrix.mul_one,
      (mem_orthogonalGroup_iff' (Fin (N + 3)) ℝ).1 hZo]
  have hMQ : A' * B'⁻¹ = Qᵀ * M * Q := by
    rw [hA', hB'inv, show Qᵀ * A * Z * (Zᵀ * B⁻¹ * Q) = Qᵀ * A * (Z * Zᵀ) * B⁻¹ * Q by
      simp only [Matrix.mul_assoc], hZZ, Matrix.mul_one]
    simp only [M, Matrix.mul_assoc]
  have hMH : M.IsUpperHessenberg := hAH.mul_isUpperTriangular hB.inv
  have hGH : (A' * B'⁻¹).IsUpperHessenberg := hA'H.mul_isUpperTriangular hB'T.inv
  have hMB : M * B = A := by
    simp only [M]
    rw [Matrix.mul_assoc, nonsing_inv_mul B hdet, Matrix.mul_one]
  -- `M` is unreduced
  have hsub : ∀ (k : ℕ) (hk : k + 1 < N + 3),
      A ⟨k + 1, hk⟩ ⟨k, by omega⟩ = M ⟨k + 1, hk⟩ ⟨k, by omega⟩ * B ⟨k, by omega⟩ ⟨k, by omega⟩ :=
    fun k hk => by
      rw [← hMB, hess_mul_tri_apply hMH hB,
        sum_ite_one ⟨k, by omega⟩ fun j => by simp [Fin.ext_iff]; omega]
  have hMU : M.IsUnreducedUpperHessenberg := by
    refine isUnreducedUpperHessenberg_iff_fin.2 ⟨hMH, fun k hk hM0 => ?_⟩
    exact (isUnreduced_iff.1 hA).2 k hk (by rw [hsub k hk, hM0, zero_mul])
  -- the shift vector is the first column of `(M - aI)(M - bI)`
  set i0 : Fin (N + 3) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (N + 3) := ⟨1, by omega⟩ with hi1
  set i2 : Fin (N + 3) := ⟨2, by omega⟩ with hi2
  have hs : s = M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ + M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩ :=
    rfl
  have ht : t = M ⟨N + 1, by omega⟩ ⟨N + 1, by omega⟩ * M ⟨N + 2, by omega⟩ ⟨N + 2, by omega⟩ -
      M ⟨N + 1, by omega⟩ ⟨N + 2, by omega⟩ * M ⟨N + 2, by omega⟩ ⟨N + 1, by omega⟩ := rfl
  have hsv := qzShiftVector_full hAH hB hBd (M := M) rfl
  rw [← hs, ← ht] at hsv
  rw [← hi0, ← hi1, ← hi2] at hsv
  have v0 : (i0 : ℕ) = 0 := rfl
  have v1 : (i1 : ℕ) = 1 := rfl
  have v2 : (i2 : ℕ) = 2 := rfl
  set P := M * M - s • M + t • 1 with hP
  have hMM : ∀ i, (M * M) i i0 = M i i0 * M i0 i0 + M i i1 * M i1 i0 := fun i => by
    rw [mul_apply, Fintype.sum_eq_add i0 i1
      (fun e => by have := congrArg Fin.val e; rw [v0, v1] at this; omega) fun k hk => by
        have a : (k : ℕ) ≠ 0 := fun e => hk.1 (Fin.ext e)
        have b : (k : ℕ) ≠ 1 := fun e => hk.2 (Fin.ext e)
        rw [isUpperHessenberg_iff_fin.1 hMH k i0 (by rw [v0]; omega), mul_zero]]
  have hPcol : ∀ i, P i i0 = M i i0 * M i0 i0 + M i i1 * M i1 i0 - s * M i i0 +
      t * (1 : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ) i i0 := fun i => by
    rw [hP, Matrix.add_apply, Matrix.sub_apply, hMM, Matrix.smul_apply, Matrix.smul_apply,
      smul_eq_mul, smul_eq_mul]
  set u₀ : Fin (N + 3) → ℝ := fun i => if (i : ℕ) = 0 then
      (Id.run (qzShiftVector pure 0 (N + 2) A B)).1
    else if (i : ℕ) = 0 + 1 then (Id.run (qzShiftVector pure 0 (N + 2) A B)).2.1
    else if (i : ℕ) = 0 + 2 then (Id.run (qzShiftVector pure 0 (N + 2) A B)).2.2 else 0 with hu₀
  have hPu : P *ᵥ Pi.single i0 1 = u₀ := by
    funext i
    rw [mulVec_single_one, col_apply, hPcol, hu₀, hsv]
    dsimp only
    by_cases h0 : (i : ℕ) = 0
    · have : i = i0 := Fin.ext h0
      subst this
      rw [ite_eq_left v0, one_apply_eq]
      ring
    have hne0 : i ≠ i0 := fun e => h0 (by rw [e])
    rw [ite_eq_right h0, one_apply_ne hne0, mul_zero, add_zero]
    by_cases h1 : (i : ℕ) = 1
    · have : i = i1 := Fin.ext h1
      subst this
      rw [ite_eq_left (show (i1 : ℕ) = 0 + 1 by rw [v1])]
      ring
    rw [ite_eq_right (show ¬ (i : ℕ) = 0 + 1 by omega)]
    have hi0' : M i i0 = 0 := isUpperHessenberg_iff_fin.1 hMH i i0 (by rw [v0]; omega)
    by_cases h2 : (i : ℕ) = 2
    · have : i = i2 := Fin.ext h2
      subst this
      rw [ite_eq_left (show (i2 : ℕ) = 0 + 2 by rw [v2]), hi0']
      ring
    · have hi1' : M i i1 = 0 := isUpperHessenberg_iff_fin.1 hMH i i1 (by rw [v1]; omega)
      rw [ite_eq_right (show ¬ (i : ℕ) = 0 + 2 by omega), hi0', hi1']
      ring
  -- the first column of `Q`
  set P₀ := 1 - d₀.2 • vecMulVec d₀.1 d₀.1 with hP₀
  have hQcol : Q *ᵥ Pi.single i0 1 = P₀ *ᵥ Pi.single i0 1 := by
    rw [hQ, hdQ, householderProduct_cons, ← mulVec_mulVec,
      householderProduct_mulVec_single fun q hq => hrest q hq i0 rfl]
  have hPP : P₀ * P₀ = 1 := by
    refine one_sub_smul_vecMulVec_mul_self_of_mem
      (one_sub_smul_vecMulVec_mem_orthogonalGroup ?_)
    rcases hβ₀ with hb | hb
    · rw [hb, zero_mul]
    · rw [hb, sub_self, mul_zero]
  have hP₀u : P₀ *ᵥ u₀ = (P₀ *ᵥ u₀) i0 • Pi.single i0 1 := by
    funext i
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hi : i = i0
    · rw [hi, ite_eq_left rfl, mul_one]
    · rw [ite_eq_right hi, mul_zero]
      exact hPu₀ i fun e => hi (Fin.ext e)
  have hu0 : u₀ ≠ 0 := by
    intro hu
    have hz := congrFun hu i2
    simp only [hu₀, hi2, show ¬ (2 = 0) by omega, show ¬ (2 = 0 + 1) by omega, ↓reduceIte,
      Pi.zero_apply, hsv] at hz
    have e10 : M i1 i0 ≠ 0 := by
      have := (isUnreducedUpperHessenberg_iff_fin.1 hMU).2 0 (by omega)
      convert this using 2
    have e21 : M i2 i1 ≠ 0 := by
      have := (isUnreducedUpperHessenberg_iff_fin.1 hMU).2 1 (by omega)
      convert this using 2
    exact mul_ne_zero e10 e21 hz
  set cn := (P₀ *ᵥ u₀) i0 with hcn
  have hcn0 : cn ≠ 0 := by
    intro hc
    refine hu0 ?_
    rw [← one_mulVec u₀, ← hPP, ← mulVec_mulVec, hP₀u, hc, zero_smul, mulVec_zero]
  have hPe : P₀ *ᵥ Pi.single i0 1 = cn⁻¹ • u₀ := by
    have h' : u₀ = cn • (P₀ *ᵥ Pi.single i0 1) := by
      rw [← mulVec_smul, ← hP₀u, mulVec_mulVec, hPP, one_mulVec]
    rw [h', smul_smul, inv_mul_cancel₀ hcn0, one_smul]
  have hi00 : (0 : Fin (N + 3)) = i0 := Fin.ext rfl
  have hstarQ : star Q = Qᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have htri : (Qᵀ * P).IsUpperTriangular := by
    have := IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval hMU
      (X ^ 2 - C s * X + C t) hQo (by rw [hstarQ, ← hMQ]; exact hGH)
      (by
        rw [aeval_francisPoly, ← mulVec_single_one Q 0, hi00, hQcol, hPe, ← hP, hPu]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    rwa [aeval_francisPoly, hstarQ] at this
  exact ⟨hQo, hZo, hA', hB', hA'H, hB'T, hMQ, Q, hQo, hMQ, hGH, htri⟩

end QZFrancis

/-! ### Algorithm 7.7.3: the specification -/

section QZAlgorithmSpec

open GolubVanLoan.Chapter05

open scoped Matrix.Norms.Frobenius

/-- The deflation sweep of Algorithm 7.7.3 is the one of Algorithm 7.5.2 (exact arithmetic). -/
theorem qzDeflate_pure_eq (ε : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (qzDeflate pure ε A) = Id.run (qrDeflate pure ε A) := by
  unfold qzDeflate qrDeflate
  rw [List.idRun_foldlM, List.idRun_foldlM]
  congr 1
  funext H i
  rw [qrDeflateStep_pure]
  by_cases hi : 0 < (i : ℕ)
  · simp only [hi, ↓reduceDIte, ↓reduceIte, Id.run_bind, Id.run_pure]
    rw [add_comm |H _ _|]
    split_ifs
    · ext a b
      by_cases ha : a = i
      · subst ha
        by_cases hb : b = ⟨(a : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩
        · simp [hb]
        · simp [hb]
      · simp [ha, updateRow_apply]
    · rfl
  · simp only [hi, ↓reduceDIte, ↓reduceIte, Id.run_pure]

/-- `qzEntry` of the subdiagonal and `SubdiagZero`. -/
theorem subdiagZero_iff_qzEntry {A : Matrix (Fin n) (Fin n) ℝ} {i : ℕ} :
    SubdiagZero A i ↔ (i < n → 0 < i → qzEntry A i (i - 1) = 0) :=
  ⟨fun h hi hpos => by rw [qzEntry_of_lt A hi (by omega)]; exact h hi hpos,
    fun h hi hpos => by have := h hi hpos; rwa [qzEntry_of_lt A hi (by omega)] at this⟩

/-- **The invariant of the passes of Algorithm 7.7.3**: `(A, B) = (Qᵀ (A₀ + E) Z, Qᵀ B₀ Z)` with
`Q`, `Z` orthogonal, `A` upper Hessenberg and `B` upper triangular, `‖E‖_F ≤ (c - 1) ‖A₀‖_F`
(`E = 0` when `ε = 0`), and no two consecutive subdiagonal entries of `A` nonzero once `done`. -/
private def QZPassInv (ε : ℝ) (A₀ B₀ : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (st : QZArrays n × Bool) : Prop :=
  st.1.Q ∈ orthogonalGroup (Fin n) ℝ ∧ st.1.Z ∈ orthogonalGroup (Fin n) ℝ ∧
    st.1.B = st.1.Qᵀ * B₀ * st.1.Z ∧ st.1.A.IsUpperHessenberg ∧ st.1.B.IsUpperTriangular ∧
    (st.2 = true → NoTwoSubdiag st.1.A) ∧
    ∃ E, st.1.A = st.1.Qᵀ * (A₀ + E) * st.1.Z ∧ ‖E‖ ≤ (c - 1) * ‖A₀‖ ∧ (ε = 0 → E = 0)

open Classical in
/-- The unfolded exact run of an unfinished pass of Algorithm 7.7.3. -/
private theorem qzPass_false_pure (ε : ℝ) (st : QZArrays n) :
    Id.run (qzPass pure ε (st, false)) =
      let A := Id.run (qzDeflate pure ε st.A)
      if Nat.findGreatest (fun q => qzTrailingQuasi A (n - q)) n = n then
        (⟨A, st.B, st.Q, st.Z⟩, true)
      else
        let r := n - Nat.findGreatest (fun q => qzTrailingQuasi A (n - q)) n - 1
        let p := r - Nat.findGreatest (fun d => qzUnreducedTail A r d) r
        let blk := (List.finRange n).filter fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r
        match (blk.filter fun i => st.B i i = 0).getLast? with
        | some k => (Id.run (qzZeroChase pure p k r ⟨A, st.B, st.Q, st.Z⟩), false)
        | none =>
          let out := Id.run (algorithm_7_7_2 pure p r A st.B)
          (⟨out.1, out.2.1,
            Id.run (out.2.2.1.foldlM (fun Q d =>
              householderApplyRight pure d.1 d.2 (List.finRange n) blk Q) st.Q),
            Id.run (out.2.2.2.foldlM (fun Z d =>
              householderApplyRight pure d.1 d.2 (List.finRange n) blk Z) st.Z)⟩, false) := by
  simp only [qzPass, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Accumulating reflector data supported on the block into `Q` (`householderApplyRight` on the
block's columns) multiplies `Q` by their product. -/
private theorem foldlM_householderApplyRight {blk : List (Fin n)} (hblk : blk.Nodup)
    {data : List ((Fin n → ℝ) × ℝ)} (hdata : ∀ d ∈ data, ∀ l, l ∉ blk → d.1 l = 0)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (data.foldlM (fun Q d => householderApplyRight pure d.1 d.2 (List.finRange n) blk Q)
      Q) = Q * householderProduct data := by
  rw [List.idRun_foldlM]
  induction data generalizing Q with
  | nil => simp [householderProduct_nil]
  | cons d data ih =>
    rw [List.foldl_cons, householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) hblk
      List.mem_finRange (hdata d List.mem_cons_self),
      ih (fun d' hd' => hdata d' (List.mem_cons_of_mem _ hd')), householderProduct_cons,
      Matrix.mul_assoc]

/-- **One pass of Algorithm 7.7.3 keeps the invariant**, with the perturbation factor multiplied
by `(1 + 2 ε)^n` (the deflation, `qrDeflate_spec`); the zero chase (`qzZeroChase_spec`) and the QZ
step on the block (`algorithm_7_7_2_block`, its reflector data accumulated into `Q`, `Z`) are
exact equivalences, and `q = n` means no two consecutive subdiagonal entries are nonzero. -/
private theorem qzPass_inv {ε : ℝ} (hε : 0 ≤ ε) {A₀ B₀ : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : 1 ≤ c) {st : QZArrays n × Bool} (hst : QZPassInv ε A₀ B₀ c st) :
    QZPassInv ε A₀ B₀ ((1 + 2 * ε) ^ n * c) (Id.run (qzPass pure ε st)) := by
  classical
  obtain ⟨st, d⟩ := st
  obtain ⟨hQ, hZ, hBE, hAH, hBT, hdone, E, hAE, hE, hE0⟩ := hst
  have hA0 : 0 ≤ ‖A₀‖ := norm_nonneg _
  have hpow : 1 ≤ (1 + 2 * ε) ^ n := one_le_pow₀ (by linarith)
  cases d with
  | true =>
    refine ⟨hQ, hZ, hBE, hAH, hBT, hdone, E, hAE, hE.trans ?_, hE0⟩
    have : c ≤ (1 + 2 * ε) ^ n * c := le_mul_of_one_le_left (by linarith) hpow
    nlinarith
  | false =>
    rw [qzPass_false_pure]
    dsimp only
    rw [qzDeflate_pure_eq]
    obtain ⟨E₁, hA₁E, hE₁, hE₁0, hA₁H⟩ := qrDeflate_spec hε hQ hZ A₀ hAE hE hE0 hAH
    generalize Id.run (qrDeflate pure ε st.A) = A₁ at hA₁E hA₁H ⊢
    have hq : qzTrailingQuasi A₁ (n - Nat.findGreatest (fun q => qzTrailingQuasi A₁ (n - q)) n) :=
      Nat.findGreatest_spec (P := fun q => qzTrailingQuasi A₁ (n - q)) (m := 0) (Nat.zero_le n)
        ⟨Or.inr (qzEntry_of_not_lt A₁ (by omega)),
        fun i hi hni _ => absurd hni (by omega)⟩
    have hqn := Nat.findGreatest_le (P := fun q => qzTrailingQuasi A₁ (n - q)) n
    generalize Nat.findGreatest (fun q => qzTrailingQuasi A₁ (n - q)) n = q at hq hqn ⊢
    split_ifs with hqe
    · -- `q = n`: done
      rw [hqe, Nat.sub_self] at hq
      refine ⟨hQ, hZ, hBE, hA₁H, hBT, fun _ i hi => ?_, E₁, hA₁E, hE₁, hE₁0⟩
      rw [subdiagZero_iff_qzEntry, subdiagZero_iff_qzEntry]
      by_cases hin : i + 1 < n
      · rcases hq.2 i (by omega) (by omega) hin with h | h
        · exact Or.inl fun _ _ => h
        · exact Or.inr fun _ _ => by simpa using h
      · exact Or.inr fun h => absurd h (by omega)
    · have hqlt : q < n := lt_of_le_of_ne hqn hqe
      set r := n - q - 1 with hrdef
      have hr : r < n := by omega
      have hr₁ : qzEntry A₁ (r + 1) r = 0 := by
        rcases hq.1 with h | h
        · omega
        · rwa [show n - q = r + 1 by omega, show r + 1 - 1 = r by omega] at h
      have hd0 : qzUnreducedTail A₁ r (Nat.findGreatest (fun d => qzUnreducedTail A₁ r d) r) :=
        Nat.findGreatest_spec (P := fun d => qzUnreducedTail A₁ r d) (m := 0) (Nat.zero_le r)
          fun i _ hi => absurd hi (by omega)
      have hdle := Nat.findGreatest_le (P := fun d => qzUnreducedTail A₁ r d) r
      have hdmax : ∀ k, Nat.findGreatest (fun d => qzUnreducedTail A₁ r d) r < k → k ≤ r →
          ¬ qzUnreducedTail A₁ r k := fun k h1 h2 => Nat.findGreatest_is_greatest h1 h2
      generalize Nat.findGreatest (fun d => qzUnreducedTail A₁ r d) r = dd at hd0 hdle hdmax ⊢
      set p := r - dd with hpdef
      have hp : 0 < p → qzEntry A₁ p (p - 1) = 0 := by
        intro hp0
        have hnot := hdmax (dd + 1) (by omega) (by omega)
        simp only [qzUnreducedTail, not_forall, not_not] at hnot
        obtain ⟨i, hir, hi, hzero⟩ := hnot
        by_cases hip : r - dd < i
        · exact absurd hzero (hd0 i hir hip)
        · rwa [show i = p by omega] at hzero
      have hblk : ((List.finRange n).filter fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r).Nodup :=
        (List.nodup_finRange n).filter _
      have hmemblk : ∀ i : Fin n, i ∈ (List.finRange n).filter
          (fun (i : Fin n) => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r) ↔ (p ≤ (i : ℕ) ∧ (i : ℕ) ≤ r) := by
        intro i
        simp
      have hequiv : QZArrays.IsEquiv (A₀ + E₁) B₀ ⟨A₁, st.B, st.Q, st.Z⟩ :=
        ⟨hQ, hZ, hA₁E, hBE⟩
      split
      · -- a zero on the diagonal of `B₂₂`: the zero chase
        rename_i k hk
        have hkmem := List.mem_of_getLast? hk
        rw [List.mem_filter, hmemblk] at hkmem
        obtain ⟨⟨hpk, hkr⟩, hBk⟩ := hkmem
        have hBk' : qzEntry st.B k k = 0 := by rw [qzEntry_fin]; simpa using hBk
        obtain ⟨⟨hQ', hZ', hA'E, hB'E⟩, hA'H, hB'T, -⟩ := qzZeroChase_spec hpk hkr hr hequiv
          hA₁H hBT hBk' hp hr₁
        exact ⟨hQ', hZ', hB'E, hA'H, hB'T, fun h => by simp at h, E₁, hA'E, hE₁, hE₁0⟩
      · -- the QZ step on the block
        by_cases hpr : p < r
        · generalize hout : Id.run (algorithm_7_7_2 pure p r A₁ st.B) = out
          obtain ⟨A', B', dQ, dZ⟩ := out
          obtain ⟨hQo, hZo, hA', hB', hA'H, hB'T, hsQ, hsZ, -⟩ :=
            algorithm_7_7_2_block hpr hr hA₁H hBT hp hr₁ hout
          dsimp only
          rw [foldlM_householderApplyRight hblk (fun d hd l hl => hsQ d hd l (by
              rw [hmemblk] at hl; omega)),
            foldlM_householderApplyRight hblk (fun d hd l hl => hsZ d hd l (by
              rw [hmemblk] at hl; omega))]
          refine ⟨mul_mem hQ hQo, mul_mem hZ hZo, ?_, hA'H, hB'T, fun h => by simp at h, E₁, ?_,
            hE₁, hE₁0⟩
          · rw [hB', hBE, transpose_mul]
            simp only [Matrix.mul_assoc]
          · rw [hA', hA₁E, transpose_mul]
            simp only [Matrix.mul_assoc]
        · have hout : Id.run (algorithm_7_7_2 pure p r A₁ st.B) = (A₁, st.B, [], []) := by
            simp [algorithm_7_7_2, hpr]
          rw [hout]
          dsimp only
          simp only [List.foldlM_nil, Id.run_pure]
          exact ⟨hQ, hZ, hBE, hA₁H, hBT, fun h => by simp at h, E₁, hA₁E, hE₁, hE₁0⟩

/-- The passes of Algorithm 7.7.3 keep the invariant, the perturbation factor growing by
`(1 + 2 ε)^n` per pass. -/
private theorem qzPass_foldl {ε : ℝ} (hε : 0 ≤ ε) (A₀ B₀ : Matrix (Fin n) (Fin n) ℝ) :
    ∀ (l : List ℕ) (c : ℝ) (st : QZArrays n × Bool), 1 ≤ c → QZPassInv ε A₀ B₀ c st →
      QZPassInv ε A₀ B₀ ((1 + 2 * ε) ^ (n * l.length) * c)
        (l.foldl (fun st _ => Id.run (qzPass pure ε st)) st)
  | [], c, st, _, h => by simpa using h
  | a :: l, c, st, hc, h => by
    have hpow : 1 ≤ (1 + 2 * ε) ^ n := one_le_pow₀ (by linarith)
    have := qzPass_foldl hε A₀ B₀ l _ _ (one_le_mul_of_one_le_of_one_le hpow hc)
      (qzPass_inv hε hc h)
    rw [List.foldl_cons, show (1 + 2 * ε) ^ (n * (a :: l).length) * c =
      (1 + 2 * ε) ^ (n * l.length) * ((1 + 2 * ε) ^ n * c) by
        rw [List.length_cons, Nat.mul_succ, pow_add]; ring]
    exact this

/-- **Algorithm 7.7.3 (the QZ algorithm), exact semantics.** For `0 ≤ ε` and
`(⟨T, S, Q, Z⟩, done) = Algorithm 7.7.3 (A, B, ε)` run for at most `fuel` passes with exact
arithmetic: `Q` and `Z` are orthogonal, `S = Qᵀ B Z` is upper triangular, and `T = Qᵀ (A + E) Z` is
upper Hessenberg for a perturbation `E` with `‖E‖_F ≤ ((1 + 2ε)^(n·fuel) - 1) ‖A‖_F` (the
deflations; the zero chase and the QZ steps are exact equivalences), `E = 0` when `ε = 0`; and if
the loop ended (`q = n`, `done`), `T` is upper quasi-triangular: `(T, S)` is the generalized real
Schur form of `(A + E, B)` (Theorem 7.7.2, made constructive up to the deflation perturbation). -/
theorem algorithm_7_7_3_spec {ε : ℝ} (hε : 0 ≤ ε) (A B : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ)
    {st : QZArrays n} {done : Bool}
    (h : Id.run (algorithm_7_7_3 pure ε A B fuel) = (st, done)) :
    st.Q ∈ orthogonalGroup (Fin n) ℝ ∧ st.Z ∈ orthogonalGroup (Fin n) ℝ ∧
      st.B = st.Qᵀ * B * st.Z ∧ st.B.IsUpperTriangular ∧
      (∃ E : Matrix (Fin n) (Fin n) ℝ, st.A = st.Qᵀ * (A + E) * st.Z ∧
        ‖E‖ ≤ ((1 + 2 * ε) ^ (n * fuel) - 1) * ‖A‖ ∧ (ε = 0 → E = 0)) ∧
      st.A.IsUpperHessenberg ∧ (done = true → st.A.IsQuasiUpperTriangular) := by
  have hrun : Id.run (algorithm_7_7_3 pure ε A B fuel) =
      Id.run ((List.range fuel).foldlM (fun st _ => qzPass pure ε st)
        (Id.run (algorithm_7_7_1 pure A B), false)) := rfl
  rw [hrun, List.idRun_foldlM] at h
  obtain ⟨hQ₀, hZ₀, hA₀, hB₀, hA₀H, hB₀T⟩ := algorithm_7_7_1_spec A B
  have hinit : QZPassInv ε A B 1 (Id.run (algorithm_7_7_1 pure A B), false) :=
    ⟨hQ₀, hZ₀, hB₀, hA₀H, hB₀T, fun h => by simp at h, 0, by rw [add_zero]; exact hA₀, by simp,
      fun _ => rfl⟩
  have hpass := qzPass_foldl hε A B (List.range fuel) 1 _ le_rfl hinit
  rw [List.length_range, mul_one, h] at hpass
  obtain ⟨hQ, hZ, hBE, hAH, hBT, hdone, E, hAE, hE, hE0⟩ := hpass
  exact ⟨hQ, hZ, hBE, hBT, ⟨E, hAE, hE, hE0⟩, hAH, fun hd =>
    isQuasiUpperTriangular_of_noTwoSubdiag hAH (hdone hd)⟩

end QZAlgorithmSpec

end GolubVanLoan.Chapter07
