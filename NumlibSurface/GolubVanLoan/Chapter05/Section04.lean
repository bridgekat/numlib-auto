import Numlib.LinearAlgebra.Matrix.Bidiagonal
import Numlib.LinearAlgebra.Matrix.CompleteOrthogonal
import Numlib.LinearAlgebra.Matrix.RankRevealing
import NumlibSurface.GolubVanLoan.Chapter02.Section05
import NumlibSurface.GolubVanLoan.Chapter05.Section03

/-!
# Golub–Van Loan §5.4: other orthogonal factorizations

Surface file for [golub2013matrix] §5.4: numerical rank and the SVD (§5.4.1: the singular value
perturbation under (5.4.4), the `δ`-rank (5.4.5)); QR with column pivoting ((5.4.6), the norm
downdate, Algorithm 5.4.1) and the Kahan matrix (§5.4.3); Chan's Theorem 5.4.1 (§5.4.4); the
rank-revealing update of §5.4.5; the complete orthogonal decomposition ((5.4.12), §5.4.7);
bidiagonalization ((5.4.13), Algorithm 5.4.2) and `R`-bidiagonalization (§5.4.9).

## Conventions

The book's sorted `σ_k` (1-based) is `A.sortedSingularValues (k - 1)` (Mathlib's
`LinearMap.singularValues` of `toEuclideanLin A`, antitone, 0-based). Programs follow the
conventions of `NumlibSurface/GolubVanLoan`; a Householder step on a block is `houseOn` and
`householderApplyLeft`/`Right` over index lists (`indexFrom`). Indices are 0-based. A pivoted
factorization `A Π = QR` with `R = [R₁₁ R₁₂; 0 0]`, `R₁₁` nonsingular, is the backbone's
`Matrix.IsPivotedQR.IsRankRevealing A Q R π r` (`A Π = A.submatrix id π`); a complete orthogonal
decomposition is `Matrix.IsCompleteOrthogonal A U V r` (over `ℝ`, `Uᴴ = Uᵀ`).

## Book slips carried

§5.4.1 cites "Corollary 2.4.6" for `σ_k = min_{rank B = k-1} ‖A - B‖₂` (it is Theorem 2.4.8, and
the minimum is over `rank B ≤ k - 1`); Algorithm 5.4.1 prints `A(:r:m, r:n)`.

## Not formalized

(5.4.2)–(5.4.3) (approximations `≈`), the backward stability (5.4.4) of the Golub–Kahan–Reinsch SVD
(a Chapter 8 algorithm, used only as a hypothesis), the numerical claim `σ₃₀₀(Kah₃₀₀(.99)) =
O(10⁻¹⁹)`, "in practice small trailing submatrices almost always emerge" (empirical), flop counts,
and the pivot rule (5.4.8) as a separate statement (it is the choice of `k` in
`algorithm_5_4_1`).
-/

open FloatingPoint Matrix WithLp

namespace GolubVanLoan.Chapter05

variable {m n : ℕ}

/-! ### §5.4.1 Numerical rank and the SVD -/

section NumericalRank

open scoped Matrix.Norms.L2Operator

/-- **§5.4.1, the computed singular values are accurate in absolute terms**: if
`Σ̂ = Wᵀ (A + ΔA) Z` with `W`, `Z` orthogonal and `Σ̂` "diagonal" with sorted nonnegative entries
`σ̂₁ ≥ σ̂₂ ≥ ⋯ ≥ 0` (the conclusion (5.4.4) of a backward-stable SVD algorithm), and
`‖ΔA‖₂ ≤ ε ‖A‖₂`, then `|σ_k - σ̂_k| ≤ ε σ₁` for `k = 1:n` (with `σ₁ = ‖A‖₂`). The book's argument
by Eckart–Young is Weyl's inequality for singular values. -/
theorem singularValues_perturbation {A ΔA : Matrix (Fin m) (Fin n) ℝ}
    {W : Matrix (Fin m) (Fin m) ℝ} {Z : Matrix (Fin n) (Fin n) ℝ} {σhat : ℕ → ℝ}
    (hW : W ∈ orthogonalGroup (Fin m) ℝ) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (hσ : Antitone σhat) (hσ0 : ∀ i, 0 ≤ σhat i)
    (hsig : Wᵀ * (A + ΔA) * Z = rectDiagonal fun i => σhat i) {ε : ℝ}
    (hε : ‖ΔA‖ ≤ ε * ‖A‖) {k : ℕ} (hkm : k < m) (hkn : k < n) :
    |A.sortedSingularValues k - σhat k| ≤ ε * A.sortedSingularValues 0 := by
  have hsvd : IsSVD (A + ΔA) W σhat Z :=
    ⟨hW, hZ, hσ, hσ0, by
      rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]⟩
  rw [hsvd.singularValues_eq hkm hkn, sortedSingularValues_zero_eq_l2_opNorm]
  refine le_trans ?_ hε
  have hweyl := LinearMap.abs_singularValues_sub_le (S := toEuclideanLin A)
    (T := toEuclideanLin (A + ΔA)) (norm_nonneg ΔA) (fun x => by
      rw [← map_sub, add_sub_cancel_left]
      exact norm_toEuclideanLin_apply_le ΔA x) k
  rw [abs_sub_comm]
  exact hweyl

/-- **(5.4.5), the `δ`-rank** of a nonincreasing sequence `σ̂₁ ≥ ⋯ ≥ σ̂_n` of computed singular
values: the number `r̂` of them exceeding the tolerance `δ`, so that
`σ̂₁ ≥ ⋯ ≥ σ̂_r̂ > δ ≥ σ̂_{r̂+1} ≥ ⋯ ≥ σ̂_n` (`deltaRank_spec`). -/
noncomputable def deltaRank (n : ℕ) (δ : ℝ) (σhat : ℕ → ℝ) : ℕ :=
  ((Finset.range n).filter fun i => δ < σhat i).card

/-- **(5.4.5)**: for antitone `σ̂`, the `δ`-rank `r̂` is characterized by `σ̂_i > δ` for `i < r̂`
and `σ̂_i ≤ δ` for `r̂ ≤ i < n` (0-based). For the exact singular values of `A` and `δ = 0` it is
the rank. -/
theorem deltaRank_spec {δ : ℝ} {σhat : ℕ → ℝ} (hσ : Antitone σhat) :
    deltaRank n δ σhat ≤ n ∧ (∀ i, i < deltaRank n δ σhat → δ < σhat i) ∧
      ∀ i, deltaRank n δ σhat ≤ i → i < n → σhat i ≤ δ := by
  -- the set `{i < n | δ < σ̂ i}` is an initial segment
  set r := Nat.find (⟨n, fun h => lt_irrefl n h.1⟩ : ∃ r, ¬ (r < n ∧ δ < σhat r)) with hr
  have hseg : (Finset.range n).filter (fun i => δ < σhat i) = Finset.range r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hin, hi⟩
      by_contra hri
      have hri := not_lt.1 hri
      have := Nat.find_spec (⟨n, fun h => lt_irrefl n h.1⟩ : ∃ r, ¬ (r < n ∧ δ < σhat r))
      rw [← hr] at this
      exact this ⟨by omega, lt_of_lt_of_le hi (hσ hri)⟩
    · intro hir
      have := Nat.find_min (⟨n, fun h => lt_irrefl n h.1⟩ : ∃ r, ¬ (r < n ∧ δ < σhat r))
        (show i < Nat.find _ from hr ▸ hir)
      exact not_not.1 this
  have hrn : r ≤ n := Nat.find_min' _ fun h => lt_irrefl n h.1
  have hdr : deltaRank n δ σhat = r := by rw [deltaRank, hseg, Finset.card_range]
  rw [hdr]
  refine ⟨hrn, fun i hi => ?_, fun i hri hin => ?_⟩
  · have : i ∈ (Finset.range n).filter (fun i => δ < σhat i) := by
      rw [hseg]; exact Finset.mem_range.2 hi
    exact (Finset.mem_filter.1 this).2
  · by_contra h
    have h := lt_of_not_ge h
    have : i ∈ (Finset.range n).filter (fun i => δ < σhat i) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 hin, h⟩
    rw [hseg, Finset.mem_range] at this
    omega

/-- **(5.4.1)**: if `rank A = r` and `Uᵀ A V = Σ` is an SVD, then `σ_{r+1} = ⋯ = σ_n = 0` and
`A = ∑_{k=1}^{r} σ_k u_k v_kᵀ` (Corollaries 2.4.6–2.4.7). -/
theorem equation_5_4_1 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) :
    (∀ i, A.rank ≤ i → i < m → i < n → σ i = 0) ∧
      A = ∑ k : Fin A.rank, σ k • vecMulVec (U.col (Fin.castLE (rank_le_height A) k))
        (V.col (Fin.castLE (rank_le_width A) k)) := by
  have hz : ∀ i, A.rank ≤ i → i < m → i < n → σ i = 0 := fun i hi him hin => by
    rw [h.singularValues_eq him hin]
    exact (sortedSingularValues_eq_zero_iff_rank_le (A := A) i).2 hi
  refine ⟨hz, ?_⟩
  have hA := h.eq_mul_mul_star
  simp only [RCLike.ofReal_real_eq_id, id] at hA
  ext p q
  have hUD : ∀ b : Fin n, (U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ)) p b =
      if hb : (b : ℕ) < m then U p ⟨b, hb⟩ * σ b else 0 := by
    intro b
    simp only [mul_apply, rectDiagonal_apply, mul_ite, mul_zero]
    split_ifs with hb
    · rw [Finset.sum_eq_single ⟨b, hb⟩ (fun a _ ha => by
        rw [ite_eq_right (fun e => (ha (Fin.ext e)).elim)]) (by simp)]
      simp
    · exact Finset.sum_eq_zero fun a _ => by
        rw [ite_eq_right (fun e => (hb (by have := a.isLt; omega)).elim)]
  have hlhs : A p q =
      ∑ b : Fin n, (if hb : (b : ℕ) < m then U p ⟨b, hb⟩ * σ b else 0) * V q b := by
    conv_lhs => rw [hA]
    rw [mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hUD b, star_apply, star_trivial]
  rw [hlhs, Matrix.sum_apply]
  simp only [Matrix.smul_apply, vecMulVec_apply, col_apply, smul_eq_mul]
  set g : Fin n → ℝ := fun b =>
    (if hb : (b : ℕ) < m then U p ⟨b, hb⟩ * σ b else 0) * V q b with hg
  have h1 : ∀ k : Fin A.rank, σ k * (U p (Fin.castLE (rank_le_height A) k) *
      V q (Fin.castLE (rank_le_width A) k)) = g (Fin.castLE (rank_le_width A) k) := by
    intro k
    have hk : ((Fin.castLE (rank_le_width A) k : Fin n) : ℕ) < m :=
      lt_of_lt_of_le k.isLt (rank_le_height A)
    simp only [hg, hk, ↓reduceDIte]
    change _ = U p (Fin.castLE (rank_le_height A) k) * σ k * _
    ring
  rw [Finset.sum_congr rfl fun k _ => h1 k, Fin.sum_castLE_eq_sum_ite]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hbr
  · rfl
  · simp only [hg]
    split_ifs with hbm
    · rw [hz b (not_lt.1 hbr) hbm b.isLt, mul_zero, zero_mul]
    · rw [zero_mul]

end NumericalRank

/-! ### §5.4.2 QR with column pivoting -/

section ColumnPivoting

/-- **(5.4.6)**: every `A ∈ ℝ^{m×n}` has a QR factorization with column pivoting
`Qᵀ A Π = [R₁₁ R₁₂; 0 0]` with `r = rank A`, `Q` orthogonal, `R₁₁` (`r × r`) upper triangular and
nonsingular and `Π` a permutation (`A Π = A.submatrix id σ`; the bundle
`Matrix.IsPivotedQR.IsRankRevealing`); and for any such factorization
`ran(A) = span{q₁, …, q_r}`. -/
theorem equation_5_4_6 (A : Matrix (Fin m) (Fin n) ℝ) :
    (∃ σ Q R, IsPivotedQR.IsRankRevealing A Q R σ A.rank) ∧
      ∀ {σ : Equiv.Perm (Fin n)} {Q : Matrix (Fin m) (Fin m) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
        {r : ℕ} (h : IsPivotedQR.IsRankRevealing A Q R σ r),
        LinearMap.range (toEuclideanLin A) =
          Submodule.span ℝ (Set.range fun i : Fin r =>
            (toLp 2 (Q.col (Fin.castLE h.le_rows i)) : EuclideanSpace ℝ (Fin m))) :=
  ⟨exists_isPivotedQR_rank A, fun h => h.range_eq_span⟩

/-- **§5.4.2, the column-norm update**: for `Q ∈ ℝ^{s×s}` orthogonal and `Qᵀ z = [α; w]`,
`‖w‖₂² = ‖z‖₂² - α²` — whence Algorithm 5.4.1's downdate `c(i) = c(i) - A(r, i)²` of the squared
norms of the trailing columns. -/
theorem norm_sq_tail_eq {s : ℕ} {Q : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (s + 1)) ℝ) (z : Fin (s + 1) → ℝ) :
    ∑ i : Fin s, (Qᵀ *ᵥ z) i.succ ^ 2 = ∑ i, z i ^ 2 - (Qᵀ *ᵥ z) 0 ^ 2 := by
  have := norm_sq_tail_eq_of_mem_unitaryGroup hQ z
  simpa only [Real.norm_eq_abs, sq_abs, conjTranspose_eq_transpose_of_trivial] using this


variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The largest of the listed entries of `c`, and `0` if none (the book's
`τ = max{c(r+1), …, c(n)}`; the loop test `τ > 0` is unchanged by the default `0`). -/
noncomputable def listMax (c : Fin n → ℝ) (l : List (Fin n)) : ℝ :=
  (l.map c).foldl max 0

/-- The state of Algorithm 5.4.1: the array, the `β_j`, the pivots `piv`, the column norms
`c`, the rank counter `r` and the current maximum `τ`. -/
structure PivotedQRState (m n : ℕ) where
  /-- The overwritten array. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- The `β_j` returned by `house`. -/
  β : Fin n → ℝ
  /-- The pivot of step `j` (`Π_j` swaps `j` and `piv j`). -/
  piv : Fin n → Fin n
  /-- The (downdated) squared column norms. -/
  c : Fin n → ℝ
  /-- The number of steps taken, the computed rank. -/
  r : ℕ
  /-- The current maximum of the trailing column norms. -/
  τ : ℝ

/-- One step `r` of Algorithm 5.4.1, performed while `τ > 0`:
```
r = r + 1
find the smallest k with r ≤ k ≤ n so c(k) = τ;  piv(r) = k
A(1:m, r) ↔ A(1:m, k);  c(r) ↔ c(k)
[v, β] = house(A(r:m, r))
A(r:m, r:n) = (I - β v vᵀ) A(r:m, r:n)
A(r+1:m, r) = v(2:m-r+1)
for i = r+1:n:  c(i) = c(i) - A(r, i)²
τ = max{c(r+1), …, c(n)}
```
Comparisons act on computed values; the downdates are rounded. -/
noncomputable def pivotedQRStep (hnm : n ≤ m) (st : PivotedQRState m n) (j : Fin n) :
    M (PivotedQRState m n) :=
  if 0 < st.τ then do
    let k := (((List.finRange n).filter fun k => j ≤ k ∧ st.c k = st.τ).head?).getD j
    let A := st.A.submatrix id (Equiv.swap j k)
    let c := st.c ∘ Equiv.swap j k
    let vβ ← houseOn rnd (indexFrom m j) (fun i => A i j)
    let A ← householderApplyLeft rnd vβ.1 vβ.2 (indexFrom m j) (indexFrom n j) A
    let A := A.updateCol j (fun i => if (j : ℕ) < i then vβ.1 i else A i j)
    let c ← ((List.finRange n).filter fun i => j < i).foldlM (fun (c : Fin n → ℝ) i => do
      let d ← rnd (c i - (← rnd (A (Fin.castLE hnm j) i * A (Fin.castLE hnm j) i)))
      pure (Function.update c i d)) c
    pure ⟨A, Function.update st.β j vβ.2, Function.update st.piv j k, c, st.r + 1,
      listMax c ((List.finRange n).filter fun i => j < i)⟩
  else pure st

/-- **Algorithm 5.4.1 (Householder QR With Column Pivoting)**: "Given `A ∈ ℝ^{m×n}` with `m ≥ n`,
the following algorithm computes `r = rank(A)` and the factorization (5.4.6) with
`Q = H₁ ⋯ H_r` and `Π = Π₁ ⋯ Π_r`. The upper triangular part of `A` is overwritten by the upper
triangular part of `R` and components `j+1:m` of the `j`th Householder vector are stored in
`A(j+1:m, j)`. The permutation `Π` is encoded in an integer vector `piv`":
```
for j = 1:n:  c(j) = A(1:m, j)ᵀ A(1:m, j)
r = 0;  τ = max{c(1), …, c(n)}
while τ > 0 and r < n:  (the body `pivotedQRStep`)
```
The `while` loop is a fold over the `n` possible steps in which a step with `τ ≤ 0` is the
identity (convention 3); `c(j)` is Algorithm 1.1.1. -/
noncomputable def algorithm_5_4_1 (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (PivotedQRState m n) := do
  let c ← (List.finRange n).foldlM (fun (c : Fin n → ℝ) (j : Fin n) => do
    let d ← Chapter01.algorithm_1_1_1 rnd (fun i => A i j) (fun i => A i j)
    pure (Function.update c j d)) 0
  (List.finRange n).foldlM (pivotedQRStep rnd hnm) ⟨A, 0, id, c, 0, listMax c (List.finRange n)⟩

end ColumnPivoting

/-! ### §5.4.3 The termination criterion -/

section Termination

open scoped Matrix.Norms.L2Operator

/-- A block upper triangular `R = [R₁₁ R₁₂; 0 R₂₂]` whose leading block row has `k` rows has
`σ_{k+1}(R) ≤ ‖R₂₂‖₂` (`Matrix.sortedSingularValues_le_l2_opNorm_trailing`, reindexed). -/
private theorem sortedSingularValues_le_trailing {R : Matrix (Fin m) (Fin n) ℝ} {k : ℕ}
    (hkm : k ≤ m) (hkn : k ≤ n)
    (hR : ∀ (i : Fin m) (j : Fin n), (j : ℕ) < k → k ≤ (i : ℕ) → R i j = 0) :
    R.sortedSingularValues k ≤ ‖R.submatrix (tailIdx hkm) (tailIdx hkn)‖ := by
  have hblk : R.submatrix (blockEquiv hkm) (blockEquiv hkn) =
      fromBlocks (R.submatrix (Fin.castLE hkm) (Fin.castLE hkn))
        (R.submatrix (Fin.castLE hkm) (tailIdx hkn)) 0
        (R.submatrix (tailIdx hkm) (tailIdx hkn)) := by
    ext (i | i) (j | j)
    · rfl
    · rfl
    · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
      exact hR (tailIdx hkm i) (Fin.castLE hkn j) j.isLt (Nat.le_add_right k i)
    · rfl
  have := sortedSingularValues_le_l2_opNorm_trailing (R.submatrix (Fin.castLE hkm) (Fin.castLE hkn))
    (R.submatrix (Fin.castLE hkm) (tailIdx hkn)) (R.submatrix (tailIdx hkm) (tailIdx hkn))
  rwa [← hblk, sortedSingularValues_submatrix_equiv, Fintype.card_fin] at this

/-- **§5.4.3, the termination criterion of QR with column pivoting**: "`R̂^{(k)}` is the exact
R-factor of a matrix `A + E_k`" — `Q R̂^{(k)} = (A + E_k) Π` with `Q` orthogonal and
`R̂^{(k)} = [R̂₁₁ R̂₁₂; 0 R̂₂₂]` (leading block `k × k`) — "where `‖E_k‖₂ ≤ ε₂ ‖A‖₂`"; if the
reduction is terminated with `‖R̂₂₂^{(k)}‖₂ ≤ ε₁ ‖A‖₂`, then `σ_{k+1}(A) ≤ (ε₁ + ε₂) ‖A‖₂`.
The two steps: `σ_{k+1}(A + E_k) = σ_{k+1}(R̂^{(k)}) ≤ ‖R̂₂₂^{(k)}‖₂`
(`Matrix.sortedSingularValues_le_l2_opNorm_trailing`) and
`σ_{k+1}(A) ≤ σ_{k+1}(A + E_k) + ‖E_k‖₂`. The book cites Corollary 2.4.4, which
(`Chapter02.corollary_2_4_4`) covers only `σ_max` and `σ_min`; at the index `k + 1` it is the
Weyl inequality `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)` behind it (`Matrix.sortedSingularValues_add_le`,
§8.6). -/
theorem sigma_succ_le_of_colPivot {A E R : Matrix (Fin m) (Fin n) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {π : Equiv.Perm (Fin n)} (hQ : Q ∈ orthogonalGroup (Fin m) ℝ)
    (hQR : Q * R = (A + E).submatrix id π) {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hR : ∀ (i : Fin m) (j : Fin n), (j : ℕ) < k → k ≤ (i : ℕ) → R i j = 0) {ε₁ ε₂ : ℝ}
    (hE : ‖E‖ ≤ ε₂ * ‖A‖) (hR₂₂ : ‖R.submatrix (tailIdx hkm) (tailIdx hkn)‖ ≤ ε₁ * ‖A‖) :
    A.sortedSingularValues k ≤ (ε₁ + ε₂) * ‖A‖ := by
  have h1 : (A + E).sortedSingularValues k ≤ ε₁ * ‖A‖ := by
    rw [← sortedSingularValues_submatrix_equiv (A + E) (Equiv.refl _) π, Equiv.coe_refl, ← hQR,
      sortedSingularValues_unitary_mul _ hQ]
    exact (sortedSingularValues_le_trailing hkm hkn hR).trans hR₂₂
  have h2 := sortedSingularValues_add_le (A + E) (-E) k 0
  rw [add_zero, add_neg_cancel_right, sortedSingularValues_zero_eq_l2_opNorm, norm_neg] at h2
  linarith

end Termination

/-! ### §5.4.3 The Kahan matrix -/

/-- **§5.4.3, the Kahan matrix** `Kah_n(s) = diag(1, s, …, s^{n-1}) T`, `T` unit upper triangular
with `-c` above the diagonal (`c² + s² = 1`, `c, s > 0`). -/
def kahanMatrix (n : ℕ) (c s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => s ^ (i : ℕ) * (if i = j then 1 else if i < j then -c else 0)

section Kahan

variable {c s : ℝ}

/-- The Kahan matrix vanishes below the diagonal. -/
private theorem kahan_below {n : ℕ} {i j : Fin n} (h : j < i) : kahanMatrix n c s i j = 0 := by
  simp [kahanMatrix, h.ne', not_lt.2 h.le]

/-- The entries of the Kahan matrix above the diagonal. -/
private theorem kahan_above {n : ℕ} {i j : Fin n} (h : i < j) :
    kahanMatrix n c s i j = -(c * s ^ (i : ℕ)) := by
  simp only [kahanMatrix, of_apply, h.ne, h, ↓reduceIte]
  ring

/-- The diagonal of the Kahan matrix. -/
private theorem kahan_diag {n : ℕ} (j : Fin n) : kahanMatrix n c s j j = s ^ (j : ℕ) := by
  simp [kahanMatrix]

/-- `c² (1 + s² + ⋯ + s^{2(k-1)}) = 1 - s^{2k}` for `c² + s² = 1`. -/
private theorem kahan_geom (hcs : c ^ 2 + s ^ 2 = 1) (k : ℕ) :
    c ^ 2 * ∑ l ∈ Finset.range k, (s ^ 2) ^ l = 1 - (s ^ 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    have : c ^ 2 = 1 - s ^ 2 := by linarith
    rw [this]
    ring

/-- Every column of the Kahan matrix has unit 2-norm. -/
private theorem kahan_col_norm (hcs : c ^ 2 + s ^ 2 = 1) {n : ℕ} (j : Fin n) :
    (fun i => kahanMatrix n c s i j) ⬝ᵥ (fun i => kahanMatrix n c s i j) = 1 := by
  set f : ℕ → ℝ := fun l => if l < (j : ℕ) then c ^ 2 * (s ^ 2) ^ l else
    if l = (j : ℕ) then (s ^ 2) ^ (j : ℕ) else 0 with hf
  have hterm : ∀ l : Fin n, kahanMatrix n c s l j * kahanMatrix n c s l j = f l := by
    intro l
    rcases lt_trichotomy l j with h | h | h
    · rw [kahan_above h, hf]
      simp only [show (l : ℕ) < j from h, ↓reduceIte]
      ring
    · subst h
      rw [kahan_diag, hf]
      simp only [lt_irrefl, ↓reduceIte]
      ring
    · rw [kahan_below h, hf]
      simp only [show ¬ (l : ℕ) < j from not_lt.2 h.le,
        show (l : ℕ) ≠ j from Fin.val_ne_of_ne h.ne', ↓reduceIte, mul_zero]
  simp only [dotProduct, hterm]
  rw [Fin.sum_univ_eq_sum_range f n]
  have key : ∀ d, ∑ l ∈ Finset.range ((j : ℕ) + 1 + d), f l = 1 := by
    intro d
    induction d with
    | zero =>
      rw [add_zero, Finset.sum_range_succ]
      have h1 : ∑ l ∈ Finset.range (j : ℕ), f l =
          c ^ 2 * ∑ l ∈ Finset.range (j : ℕ), (s ^ 2) ^ l := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l hl => ?_
        simp only [hf, Finset.mem_range.1 hl, ↓reduceIte]
      rw [h1, kahan_geom hcs, hf]
      simp only [lt_irrefl, ↓reduceIte]
      ring
    | succ d ih =>
      rw [← add_assoc, Finset.sum_range_succ, ih, hf]
      simp only [show ¬ ((j : ℕ) + 1 + d) < j by omega, show (j : ℕ) + 1 + d ≠ j by omega,
        ↓reduceIte, add_zero]
  have := key (n - ((j : ℕ) + 1))
  rwa [show (j : ℕ) + 1 + (n - ((j : ℕ) + 1)) = n by omega] at this

/-- `listMax` of a list on which the values are all `a ≥ 0`. -/
private theorem listMax_const {n : ℕ} (c' : Fin n → ℝ) (l : List (Fin n)) {a : ℝ} (ha : 0 ≤ a)
    (hc : ∀ i ∈ l, c' i = a) : listMax c' l = if l = [] then 0 else a := by
  unfold listMax
  suffices h : ∀ x, (x = 0 ∨ x = a) → (l.map c').foldl max x = if l = [] then x else a from
    h 0 (Or.inl rfl)
  induction l with
  | nil => intro x _; simp
  | cons b l ih =>
    intro x hx
    rw [List.map_cons, List.foldl_cons, hc b List.mem_cons_self,
      ih (fun i hi => hc i (List.mem_cons_of_mem b hi)) (max x a)
        (Or.inr (by rcases hx with rfl | rfl <;> simp [ha]))]
    simp only [reduceCtorEq, ↓reduceIte]
    split_ifs
    · rcases hx with rfl | rfl <;> simp [ha]
    · rfl

/-- The pivot search of Algorithm 5.4.1 returns `j` when the searched predicate is `j ≤ k`. -/
private theorem head?_getD_filter_eq {n : ℕ} (j : Fin n) (p : Fin n → Bool)
    (hp : ∀ k, p k = decide (j ≤ k)) : (((List.finRange n).filter p).head?).getD j = j := by
  have h1 : (List.finRange n).filter p = indexFrom n j := by
    unfold indexFrom
    exact List.filter_congr (fun k _ => by rw [hp, decide_eq_decide]; exact Iff.rfl)
  rw [h1, List.head?_eq_some_head (indexFrom_ne_nil j.isLt), head_indexFrom j.isLt]
  rfl

/-- The state of Algorithm 5.4.1 on `Kah_n(s)` after `k` steps. -/
private noncomputable def kahanState (n : ℕ) (c s : ℝ) (k : ℕ) : PivotedQRState n n :=
  ⟨kahanMatrix n c s, 0, id, fun i => (s ^ 2) ^ min (i : ℕ) k, k,
    if k < n then (s ^ 2) ^ k else 0⟩

/-- One step of Algorithm 5.4.1 on `Kah_n(s)`: nothing is swapped, `house` returns `β = 0`, the
array is unaltered and the downdated norms of the trailing columns are all `s^{2(k+1)}`. -/
private theorem kahan_step (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) {n k : ℕ} (hk : k < n) :
    Id.run (pivotedQRStep (M := Id) pure le_rfl (kahanState n c s k) ⟨k, hk⟩) =
      kahanState n c s (k + 1) := by
  have hτ : 0 < (s ^ 2) ^ k := by positivity
  set K := kahanMatrix n c s with hKdef
  -- the pivot search returns `k`: every trailing column has the same norm `s^{2k}`
  have hpiv : (((List.finRange n).filter fun k' : Fin n =>
      decide ((⟨k, hk⟩ : Fin n) ≤ k' ∧ (s ^ 2) ^ min (k' : ℕ) k = (s ^ 2) ^ k)).head?).getD
        (⟨k, hk⟩ : Fin n) = ⟨k, hk⟩ := by
    refine head?_getD_filter_eq _ _ fun k' => ?_
    rw [decide_eq_decide]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rw [Nat.min_eq_right (show k ≤ (k' : ℕ) from h)]
  -- `house` on the column `[s^k; 0]` returns `β = 0`
  have hhouse : ∃ v : Fin n → ℝ,
      Id.run (houseOn pure (indexFrom n k) fun i => K i ⟨k, hk⟩) = (v, 0) ∧
        (∀ i, i ∉ indexFrom n k → v i = 0) ∧ ∀ i : Fin n, k < (i : ℕ) → v i = 0 := by
    obtain ⟨p, t, hpt⟩ := List.exists_cons_of_ne_nil (indexFrom_ne_nil (m := n) hk)
    have hp : p = ⟨k, hk⟩ := by
      have := congrArg List.head? hpt
      rw [List.head?_eq_some_head (indexFrom_ne_nil hk), head_indexFrom hk, List.head?_cons]
        at this
      exact (Option.some.inj this).symm
    have hnd := nodup_indexFrom n k
    rw [hpt] at hnd
    have htail : ∀ i ∈ t, k < (i : ℕ) := by
      intro i hi
      have h1 : i ∈ indexFrom n k := by rw [hpt]; exact List.mem_cons_of_mem p hi
      rw [mem_indexFrom] at h1
      have h2 : i ≠ p := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hi)
      rw [hp] at h2
      exact lt_of_le_of_ne h1 (fun e => h2 (Fin.ext e.symm))
    rw [hpt]
    subst hp
    have hσ : (t.map fun i => K i ⟨k, hk⟩ * K i ⟨k, hk⟩).sum = 0 := by
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
      rw [hKdef, kahan_below (htail i hi : (⟨k, hk⟩ : Fin n) < i), mul_zero]
    have hx : 0 ≤ K ⟨k, hk⟩ ⟨k, hk⟩ := by rw [hKdef, kahan_diag]; positivity
    refine ⟨fun i => if i = ⟨k, hk⟩ then 1 else if i ∈ t then K i ⟨k, hk⟩ else 0, ?_, ?_, ?_⟩
    · simp only [houseOn, dotAccum_pure, pure_bind, hσ, add_zero, hx, and_true, ↓reduceIte]
      rfl
    · intro i hi
      rw [List.mem_cons, not_or] at hi
      simp only [hi.1, hi.2, ↓reduceIte]
    · intro i hi
      have hne : i ≠ ⟨k, hk⟩ := fun e => by rw [e] at hi; exact lt_irrefl _ hi
      simp only [hne, ↓reduceIte]
      split_ifs
      · rw [hKdef, kahan_below (hi : (⟨k, hk⟩ : Fin n) < i)]
      · rfl
  obtain ⟨v, hv1, hv2, hv3⟩ := hhouse
  have hApply : Id.run (householderApplyLeft pure v 0 (indexFrom n k) (indexFrom n k) K) = K := by
    rw [householderApplyLeft_spec (nodup_indexFrom n k) (nodup_indexFrom n k) hv2 0 K]
    ext i q
    simp only [zero_smul, sub_zero, Matrix.one_mul, of_apply, ite_self]
  have hupd : K.updateCol ⟨k, hk⟩ (fun i => if k < (i : ℕ) then v i else K i ⟨k, hk⟩) = K := by
    ext i q
    by_cases hq : q = ⟨k, hk⟩
    · subst hq
      rw [updateCol_self]
      split_ifs with hi
      · rw [hv3 i hi, hKdef, kahan_below (hi : (⟨k, hk⟩ : Fin n) < i)]
      · rfl
    · rw [updateCol_ne hq]
  have hcast : ∀ h : n ≤ n, Fin.castLE h ⟨k, hk⟩ = ⟨k, hk⟩ := fun _ => Fin.ext rfl
  simp only [pivotedQRStep, kahanState, hk, ↓reduceIte, hτ]
  rw [hpiv]
  simp only [Equiv.swap_self, Equiv.coe_refl, submatrix_id_id, Function.comp_id, ← hKdef]
  simp only [Id.run_bind, hv1, hApply, hupd, hcast, pure_bind, List.foldlM_pure, Id.run_pure]
  rw [show Function.update (0 : Fin n → ℝ) ⟨k, hk⟩ 0 = 0 by simp,
    show Function.update (id : Fin n → Fin n) ⟨k, hk⟩ ⟨k, hk⟩ = id by simp]
  set l := (List.finRange n).filter fun i => decide ((⟨k, hk⟩ : Fin n) < i) with hl
  have hlnd : l.Nodup := (List.nodup_finRange n).filter _
  have hmem : ∀ i, i ∈ l ↔ k < (i : ℕ) := by
    intro i
    rw [hl, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_finRange i, h⟩⟩
  have hc2 : c ^ 2 = 1 - s ^ 2 := by linarith
  have hval : ∀ i : Fin n, k < (i : ℕ) →
      (s ^ 2) ^ min (i : ℕ) k - K ⟨k, hk⟩ i * K ⟨k, hk⟩ i = (s ^ 2) ^ (k + 1) := by
    intro i hi
    rw [Nat.min_eq_right hi.le, hKdef, kahan_above (hi : (⟨k, hk⟩ : Fin n) < i)]
    linear_combination (-(s ^ 2) ^ k) * hc2
  congr 1
  · refine (List.foldl_update_of_nodup hlnd (fun i y => y i - K ⟨k, hk⟩ i * K ⟨k, hk⟩ i)
      (fun _ _ _ _ _ e => by rw [e]) _).trans ?_
    funext i
    by_cases hi : k < (i : ℕ)
    · simp only [(hmem i).2 hi, ↓reduceIte]
      rw [hval i hi, Nat.min_eq_right (show k + 1 ≤ (i : ℕ) by omega)]
    · simp only [show i ∉ l from fun h => hi ((hmem i).1 h), ↓reduceIte]
      rw [Nat.min_eq_left (not_lt.1 hi), Nat.min_eq_left (by omega)]
  · rw [listMax_const _ l (a := (s ^ 2) ^ (k + 1)) (by positivity) fun i hi => ?_]
    · by_cases hkn : k + 1 < n
      · have hne : l ≠ [] := List.ne_nil_of_mem ((hmem ⟨k + 1, hkn⟩).2 (Nat.lt_succ_self k))
        simp only [hne, hkn, ↓reduceIte]
      · have hnil : l = [] := List.eq_nil_iff_forall_not_mem.2 fun i hi => by
          have := (hmem i).1 hi
          omega
        simp only [hnil, hkn, ↓reduceIte]
    · refine (congrFun (List.foldl_update_of_nodup hlnd
        (fun i y => y i - K ⟨k, hk⟩ i * K ⟨k, hk⟩ i) (fun _ _ _ _ _ e => by rw [e]) _) i).trans ?_
      simp only [hi, ↓reduceIte]
      exact hval i ((hmem i).1 hi)

/-- After `k` steps of Algorithm 5.4.1 on `Kah_n(s)` the state is `kahanState n c s k`. -/
private theorem kahan_steps (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) {n : ℕ} :
    ∀ k ≤ n, ((List.finRange n).take k).foldl
      (fun st j => Id.run (pivotedQRStep (M := Id) pure le_rfl st j)) (kahanState n c s 0) =
        kahanState n c s k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    rw [List.take_succ_eq_append_getElem (by simpa using hkn), List.foldl_append, ih hkn.le,
      List.foldl_cons, List.foldl_nil]
    have : (List.finRange n)[k]'(by simpa using hkn) = ⟨k, hkn⟩ := by simp
    rw [this]
    exact kahan_step hs hcs hkn

open scoped Matrix.Norms.L2Operator in
/-- **§5.4.3, the Kahan matrices are unaltered by Algorithm 5.4.1**: for `s > 0`, `c² + s² = 1`,
the exact run of QR with column pivoting on `Kah_n(s)` performs `r = n` steps, swaps nothing
(`piv = id`), returns `β = 0` at every step (each subcolumn is `[x₁; 0]` with `x₁ = s^k > 0`)
and leaves the array unaltered; "and thus `‖R₂₂^{(k)}‖₂ ≥ s^{n-1}`" for every trailing block
`R(k:n, k:n)`, `k < n` (its last diagonal entry is `s^{n-1}`). -/
theorem kahanMatrix_unaltered (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) {n : ℕ} :
    (Id.run (algorithm_5_4_1 pure le_rfl (kahanMatrix n c s))).A = kahanMatrix n c s ∧
      (Id.run (algorithm_5_4_1 pure le_rfl (kahanMatrix n c s))).piv = id ∧
      (Id.run (algorithm_5_4_1 pure le_rfl (kahanMatrix n c s))).β = 0 ∧
      (Id.run (algorithm_5_4_1 pure le_rfl (kahanMatrix n c s))).r = n ∧
      ∀ k < n, s ^ (n - 1) ≤
        ‖(kahanMatrix n c s).submatrix (Subtype.val : {i : Fin n // k ≤ (i : ℕ)} → Fin n)
          (Subtype.val : {i : Fin n // k ≤ (i : ℕ)} → Fin n)‖ := by
  have hrun : Id.run (algorithm_5_4_1 pure le_rfl (kahanMatrix n c s)) = kahanState n c s n := by
    have hc0 : Id.run ((List.finRange n).foldlM (fun (c' : Fin n → ℝ) (j : Fin n) => do
        let d ← Chapter01.algorithm_1_1_1 pure (fun i => kahanMatrix n c s i j)
          (fun i => kahanMatrix n c s i j)
        pure (Function.update c' j d)) 0) = fun _ => 1 := by
      rw [List.idRun_foldlM]
      simp only [Id.run_bind, Chapter01.algorithm_1_1_1_spec, Id.run_pure]
      refine (List.foldl_update_eq_ite (fun j => (fun i => kahanMatrix n c s i j) ⬝ᵥ
        (fun i => kahanMatrix n c s i j)) _ _).trans ?_
      funext j
      simp only [List.mem_finRange, ↓reduceIte, kahan_col_norm hcs]
    have h0 : (⟨kahanMatrix n c s, 0, id, fun _ => 1, 0,
        listMax (fun _ => (1 : ℝ)) (List.finRange n)⟩ : PivotedQRState n n) =
          kahanState n c s 0 := by
      rw [listMax_const _ _ zero_le_one fun _ _ => rfl]
      simp only [kahanState, Nat.min_zero, pow_zero, List.finRange_eq_nil_iff]
      congr 1
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn, Nat.pos_of_ne_zero hn]
    unfold algorithm_5_4_1
    rw [Id.run_bind, hc0, h0, List.idRun_foldlM]
    have := kahan_steps hs hcs n le_rfl
    rwa [List.take_of_length_le (by simp)] at this
  rw [hrun]
  refine ⟨rfl, rfl, rfl, rfl, fun k hk => ?_⟩
  have hlast : k ≤ ((⟨n - 1, by omega⟩ : Fin n) : ℕ) := by simp only; omega
  set e : {i : Fin n // k ≤ (i : ℕ)} := ⟨⟨n - 1, by omega⟩, hlast⟩ with he
  have := norm_entry_le_l2_opNorm ((kahanMatrix n c s).submatrix
    (Subtype.val : {i : Fin n // k ≤ (i : ℕ)} → Fin n)
    (Subtype.val : {i : Fin n // k ≤ (i : ℕ)} → Fin n)) e e
  rwa [submatrix_apply, kahan_diag, Real.norm_eq_abs, abs_of_pos (by positivity)] at this

end Kahan

/-! ### §5.4.4 Other rank-revealing ideas: Chan's theorem -/

section Chan

/-- **Theorem 5.4.1** (Chan): "if `A ∈ ℝ^{m×n}` and `v ∈ ℝⁿ` is a unit 2-norm vector, then there
exists a permutation `Π` so that the QR factorization `A Π = QR` satisfies `|r_nn| ≤ √n σ` where
`σ = ‖Av‖₂`" (`m ≥ n = k + 1`; every QR factorization of `A Π` does). -/
theorem theorem_5_4_1 {k : ℕ} (A : Matrix (Fin m) (Fin (k + 1)) ℝ) (hkm : k + 1 ≤ m)
    (v : EuclideanSpace ℝ (Fin (k + 1))) (hv : ‖v‖ = 1) :
    ∃ π : Equiv.Perm (Fin (k + 1)), ∀ Q R, IsQR (A.submatrix id π) Q R →
      |R ⟨k, by omega⟩ (Fin.last k)| ≤ √(k + 1 : ℝ) * ‖toEuclideanLin A v‖ := by
  simpa only [Real.norm_eq_abs] using exists_perm_isQR_abs_le A hkm v hv

/-- The columns of an SVD's right factor are stretched by the singular values:
`‖v_j‖₂ = 1` and `‖A v_j‖₂ = σ_j` for `j < m`. -/
private theorem norm_mulVec_col_of_isSVD {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    (j : Fin n) (hj : (j : ℕ) < m) :
    ‖(toLp 2 (V.col j) : EuclideanSpace ℝ (Fin n))‖ = 1 ∧
      ‖toEuclideanLin A (toLp 2 (V.col j))‖ = σ j := by
  have hVc : V.col j = V *ᵥ Pi.single j 1 := by
    funext i
    simp [mulVec, dotProduct, Pi.single_apply]
  have hAV : A * V = U * (rectDiagonal fun i => σ i : Matrix (Fin m) (Fin n) ℝ) := by
    have hA := h.eq_mul_mul_star
    simp only [RCLike.ofReal_real_eq_id, id] at hA
    rw [hA, Matrix.mul_assoc, Unitary.star_mul_self_of_mem h.mem_unitaryGroup_right,
      Matrix.mul_one]
  have hS : (rectDiagonal fun i => σ i : Matrix (Fin m) (Fin n) ℝ) *ᵥ
      Pi.single j 1 = Pi.single ⟨j, hj⟩ (σ j) := by
    funext i
    rw [mulVec, dotProduct, Finset.sum_eq_single j (fun k _ hk => by
      rw [Pi.single_eq_of_ne hk, mul_zero]) (by simp), Pi.single_eq_same, mul_one,
      rectDiagonal_apply]
    by_cases hi : i = ⟨j, hj⟩
    · subst hi
      simp
    · have : (i : ℕ) ≠ j := fun e => hi (Fin.ext e)
      simp [this, hi]
  refine ⟨?_, ?_⟩
  · rw [hVc, ← toEuclideanLin_toLp,
      norm_toEuclideanLin_apply_of_mem_unitaryGroup h.mem_unitaryGroup_right,
      PiLp.toLp_single, PiLp.norm_single, norm_one]
  · rw [hVc, toEuclideanLin_toLp, mulVec_mulVec, hAV, ← mulVec_mulVec, hS,
      ← toEuclideanLin_toLp, norm_toEuclideanLin_apply_of_mem_unitaryGroup h.mem_unitaryGroup_left,
      PiLp.toLp_single, PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (h.nonneg _)]

/-- **Theorem 5.4.1, the closing remark**: "if `v = v_n` is the right singular vector
corresponding to `σ_min(A)`, then `|r_nn| ≤ √n σ_n`" (`σ_n = σ (n - 1)`, 0-based). -/
theorem theorem_5_4_1_svd {k : ℕ} {A : Matrix (Fin m) (Fin (k + 1)) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (h : IsSVD A U σ V) (hkm : k + 1 ≤ m) :
    ∃ π : Equiv.Perm (Fin (k + 1)), ∀ Q R, IsQR (A.submatrix id π) Q R →
      |R ⟨k, by omega⟩ (Fin.last k)| ≤ √(k + 1 : ℝ) * σ k := by
  obtain ⟨h1, h2⟩ := norm_mulVec_col_of_isSVD h (Fin.last k) (by simp; omega)
  have := theorem_5_4_1 A hkm _ h1
  rwa [h2, Fin.val_last] at this

end Chan

/-! ### §5.4.5 Updating a rank-revealing factorization -/

section RevealUpdate

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step `j` of `givensRevealUpdate` (the plane `(j, j + 1)`) as a named function: the
flipped rotation zeroing `v_j`, applied to `v`, to the rows `≤ j + 1` of `R` and to `Z_G`, then
the conventional rotation zeroing the new `r_{j+1,j}`, applied to `R` and `Q_G`. -/
noncomputable def givensRevealStep {k : ℕ}
    (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin (k + 1) → ℝ) ×
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (j : Fin k) :
    M (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin (k + 1) → ℝ) ×
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := do
  let i := j.castSucc
  let i' := j.succ
  let cs ← algorithm_5_1_3 rnd (st.2.1 i') (st.2.1 i)
  let v ← givensRotateVec rnd i i' cs.1 (-cs.2) st.2.1
  let R ← givensApplyRight rnd i i' cs.1 (-cs.2)
    ((List.finRange (k + 1)).filter fun r => (r : ℕ) ≤ i') st.1
  let Z ← givensApplyRight rnd i i' cs.1 (-cs.2) (List.finRange (k + 1)) st.2.2.1
  let cs₂ ← algorithm_5_1_3 rnd (R i i) (R i' i)
  let R ← givensApplyLeft rnd i i' cs₂.1 cs₂.2 (indexFrom (k + 1) i) R
  let Q ← givensApplyRight rnd i i' cs₂.1 cs₂.2 (List.finRange (k + 1)) st.2.2.2
  pure (R, v, Z, Q)

/-- **§5.4.5, the zero-chasing update** (displayed for `n = 4`, "the pattern is clear"): given
`A Z = Q R` with `R` upper triangular and a unit vector `v`, for `i = 1:n-1`:
* a "flipped" rotation `G_{i,i+1}` zeroing `v_i` against `v_{i+1}` — Algorithm 5.1.3 with the roles
  of the entries exchanged (`givens(v_{i+1}, v_i)` and `s ↦ -s`), "a slight modification";
* `v ← G_{i,i+1}ᵀ v`, `R ← R G_{i,i+1}` (rows `1:i+1`, where `R` can be nonzero), `Z_G ← Z_G G`;
* a conventional `H_{i,i+1}` zeroing the new `r_{i+1,i}`: `R ← H_{i,i+1}ᵀ R` (columns `i:n`),
  `Q_G ← Q_G H`.

Returns `(R_new, v_new, Z_G, Q_G)`; `n = k + 1` and the step `i` pairs `i` with `i + 1`. -/
noncomputable def givensRevealUpdate {k : ℕ} (R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (v : Fin (k + 1) → ℝ) :
    M (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin (k + 1) → ℝ) ×
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :=
  (List.finRange k).foldlM (givensRevealStep rnd) (R, v, 1, 1)

end RevealUpdate

/-! ### §5.4.7 The complete orthogonal decomposition -/

section CompleteOrthogonal

/-- **(5.4.12), the complete orthogonal decomposition**: every `A ∈ ℝ^{m×n}` has orthogonal `U`,
`V` with `Uᵀ A V = [T₁₁ 0; 0 0]`, `T₁₁` nonsingular of order `r = rank A`
(`Matrix.IsCompleteOrthogonal`); "the SVD is obviously an example"; and for any such
decomposition, `r = rank A`, `ran(A) = span{u₁, …, u_r}` and `null(A) = span{v_{r+1}, …, v_n}`. -/
theorem equation_5_4_12 (A : Matrix (Fin m) (Fin n) ℝ) :
    (∃ U V, IsCompleteOrthogonal A U V A.rank) ∧
      (∀ {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ},
        IsSVD A U σ V → IsCompleteOrthogonal A U V A.rank) ∧
      ∀ {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
        (h : IsCompleteOrthogonal A U V r), A.rank = r ∧
        LinearMap.range (toEuclideanLin A) = Submodule.span ℝ (Set.range fun i : Fin r =>
          (toLp 2 (U.col (Fin.castLE h.le_rows i)) : EuclideanSpace ℝ (Fin m))) ∧
        LinearMap.ker (toEuclideanLin A) = Submodule.span ℝ (Set.range fun j : Fin (n - r) =>
          (toLp 2 (V.col (tailIdx h.le_cols j)) : EuclideanSpace ℝ (Fin n))) :=
  ⟨exists_isCompleteOrthogonal A, isCompleteOrthogonal_of_svd,
    fun h => ⟨h.rank_eq, h.range_eq_span, h.ker_eq_span⟩⟩


/-- The column permutation `Π = Π₁ ⋯ Π_n` encoded by Algorithm 5.4.1's `piv` (step `j` swaps
columns `j` and `piv j`; an untaken step has `piv j = j`): `A Π` is
`A.submatrix id (pivotPerm piv)`. -/
def pivotPerm (piv : Fin n → Fin n) : Equiv.Perm (Fin n) :=
  (List.finRange n).foldl (fun p j => p * Equiv.swap j (piv j)) 1

/-- The permutation matrix `Π` of `pivotPerm piv`, so that
`A * pivotMatrix piv = A.submatrix id (pivotPerm piv)` (`Matrix.mul_toPEquiv_toMatrix`). -/
def pivotMatrix (piv : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (pivotPerm piv).symm.toPEquiv.toMatrix

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **§5.4.7, the two-step construction of a complete orthogonal decomposition**: Algorithm 5.4.1
gives `Uᵀ A Π = [R₁₁ R₁₂; 0 0]` with `r` steps; Algorithm 5.2.1 on the `n × r` matrix
`[R₁₁ R₁₂]ᵀ` gives `Qᵀ [R₁₁ R₁₂]ᵀ = [S₁; 0]`; then `V = Π Q` and `T₁₁ = S₁ᵀ`. Returns `(U, V, r)`,
`U` and `Q` accumulated from the two programs' stored reflectors with the returned `β`
(`backwardAccumulation`, convention 13); `Π` is exact (a permutation). -/
noncomputable def completeOrthogonalDecomposition (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin n) (Fin n) ℝ × ℕ) := do
  let st ← algorithm_5_4_1 rnd hnm A
  let T : Matrix (Fin n) (Fin st.r) ℝ := fun i k =>
    if hk : (k : ℕ) < m then upperPart st.A ⟨k, hk⟩ i else 0
  let QR ← algorithm_5_2_1 rnd T
  let U ← backwardAccumulation rnd (storedReflectors st.A st.β)
  let Q ← backwardAccumulation rnd (storedReflectors QR.1 QR.2)
  pure (U, pivotMatrix st.piv * Q, st.r)

end CompleteOrthogonal

/-! ### §5.4.2 Algorithm 5.4.1 in exact arithmetic -/

section PivotedQRSpec

/-- The running maximum from `x₀` dominates `x₀` and every listed value, and is `x₀` or one of
them. -/
private theorem foldl_max_spec (c : Fin n → ℝ) (l : List (Fin n)) (x₀ : ℝ) :
    x₀ ≤ (l.map c).foldl max x₀ ∧ (∀ q ∈ l, c q ≤ (l.map c).foldl max x₀) ∧
      ((l.map c).foldl max x₀ = x₀ ∨ ∃ q ∈ l, c q = (l.map c).foldl max x₀) := by
  induction l generalizing x₀ with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (max x₀ (c a))
    simp only [List.map_cons, List.foldl_cons, List.mem_cons, forall_eq_or_imp,
      exists_eq_or_imp]
    refine ⟨(le_max_left _ _).trans h1, ⟨(le_max_right _ _).trans h1, h2⟩, ?_⟩
    rcases h3 with h3 | h3
    · rcases le_total x₀ (c a) with h | h
      · rw [max_eq_right h] at h3 ⊢
        exact Or.inr (Or.inl h3.symm)
      · rw [max_eq_left h] at h3 ⊢
        exact Or.inl h3
    · exact Or.inr (Or.inr h3)

/-- `listMax` is nonnegative and dominates the listed values. -/
private theorem le_listMax (c : Fin n → ℝ) (l : List (Fin n)) :
    0 ≤ listMax c l ∧ ∀ q ∈ l, c q ≤ listMax c l :=
  ⟨(foldl_max_spec c l 0).1, (foldl_max_spec c l 0).2.1⟩

/-- A positive `listMax` is attained on the list. -/
private theorem exists_eq_listMax {c : Fin n → ℝ} {l : List (Fin n)} (h : 0 < listMax c l) :
    ∃ q ∈ l, c q = listMax c l := by
  rcases (foldl_max_spec c l 0).2.2 with h0 | h0
  · exact absurd h0 (ne_of_gt h)
  · exact h0

/-- The pivot of Algorithm 5.4.1: when `τ = max_{q ≥ j} c(q) > 0`, the first `k ≥ j` with
`c(k) = τ` exists; the search returns it. -/
private theorem pivot_spec {c : Fin n → ℝ} {τ : ℝ} (j : Fin n)
    (hτ : τ = listMax c ((List.finRange n).filter fun i => (j : ℕ) ≤ i)) (hpos : 0 < τ) :
    j ≤ (((List.finRange n).filter fun k => j ≤ k ∧ c k = τ).head?).getD j ∧
      c ((((List.finRange n).filter fun k => j ≤ k ∧ c k = τ).head?).getD j) = τ := by
  obtain ⟨q, hq, hcq⟩ := exists_eq_listMax (hτ ▸ hpos)
  rw [← hτ] at hcq
  have hne : ((List.finRange n).filter fun k => j ≤ k ∧ c k = τ) ≠ [] := by
    refine List.ne_nil_of_mem (a := q) ?_
    rw [List.mem_filter] at hq ⊢
    simp only [decide_eq_true_eq] at hq ⊢
    exact ⟨hq.1, Fin.le_def.2 hq.2, hcq⟩
  rw [List.head?_eq_some_head hne, Option.getD_some]
  have := List.head_mem hne
  rw [List.mem_filter] at this
  simpa using this.2

/-- The product of the reflectors of the first `k` steps of Algorithm 5.4.1, read from the
state (the stored vectors and the recorded `β`). -/
private noncomputable def pcQ (k : ℕ) (st : PivotedQRState m n) : Matrix (Fin m) (Fin m) ℝ :=
  householderProduct (((List.finRange n).take k).map fun q => (storedHouseholderVec st.A q, st.β q))

/-- The column permutation of the first `k` steps of Algorithm 5.4.1. -/
private def pcP (k : ℕ) (st : PivotedQRState m n) : Equiv.Perm (Fin n) :=
  (((List.finRange n).take k).map fun q => Equiv.swap q (st.piv q)).prod

/-- `C = Q_kᵀ A Π_k`, the matrix the first `k` steps of Algorithm 5.4.1 have produced. -/
private noncomputable def pcC (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) (st : PivotedQRState m n) :
    Matrix (Fin m) (Fin n) ℝ :=
  (pcQ k st)ᵀ * A.submatrix id (pcP k st)

/-- The invariant of Algorithm 5.4.1 after `k` steps: the array holds `C = Q_kᵀ A Π_k` on its
upper part and its unprocessed columns; the processed columns of `C` vanish below a nonzero
diagonal; the recorded `β` are `0` or `2/vᵀv` (and `0`, with `piv` the identity, on the steps not
taken); `c` holds the squared norms of the trailing parts of the unprocessed columns and `τ`
their maximum. -/
private def pcInv (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) (st : PivotedQRState m n) : Prop :=
  st.r = k ∧
    (∀ (i : Fin m) (q : Fin n), ((i : ℕ) ≤ q ∨ k ≤ (q : ℕ)) → st.A i q = pcC A k st i q) ∧
    (∀ (i : Fin m) (q : Fin n), (q : ℕ) < k → (q : ℕ) < i → pcC A k st i q = 0) ∧
    (∀ (i : Fin m) (q : Fin n), (q : ℕ) < k → (i : ℕ) = q → pcC A k st i q ≠ 0) ∧
    (∀ q : Fin n, (q : ℕ) < k → st.β q = 0 ∨
      st.β q * (storedHouseholderVec st.A q ⬝ᵥ storedHouseholderVec st.A q) = 2) ∧
    (∀ q : Fin n, k ≤ (q : ℕ) → st.β q = 0 ∧ st.piv q = q) ∧
    (∀ q : Fin n, k ≤ (q : ℕ) →
      st.c q = ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ (i : ℕ)), pcC A k st i q ^ 2) ∧
    st.τ = listMax st.c ((List.finRange n).filter fun i => k ≤ (i : ℕ))

/-- An orthogonal matrix fixing the coordinates below `j` preserves the squared norm of the
coordinates from `j` on. -/
private theorem sum_sq_mulVec_filter {j : ℕ} {P : Matrix (Fin m) (Fin m) ℝ}
    (hP : P ∈ orthogonalGroup (Fin m) ℝ) (y : Fin m → ℝ)
    (hfix : ∀ l : Fin m, (l : ℕ) < j → (P *ᵥ y) l = y l) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin m => j ≤ (l : ℕ)), (P *ᵥ y) l ^ 2 =
      ∑ l ∈ Finset.univ.filter (fun l : Fin m => j ≤ (l : ℕ)), y l ^ 2 := by
  have h := congrArg (· ^ 2) (norm_toLp_mulVec_of_mem_orthogonalGroup hP y)
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] at h
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin m => j ≤ (l : ℕ)),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin m => j ≤ (l : ℕ))
      (fun l => y l ^ 2)]
    at h
  have hlow : ∑ l ∈ Finset.univ.filter (fun l : Fin m => ¬ j ≤ (l : ℕ)), (P *ᵥ y) l ^ 2 =
      ∑ l ∈ Finset.univ.filter (fun l : Fin m => ¬ j ≤ (l : ℕ)), y l ^ 2 :=
    Finset.sum_congr rfl fun l hl => by
      rw [hfix l (by simpa using (Finset.mem_filter.1 hl).2)]
  linarith

/-- The first `j + 1` indices are the first `j` and then `j`. -/
private theorem take_succ_finRange (j : Fin n) :
    (List.finRange n).take ((j : ℕ) + 1) = (List.finRange n).take j ++ [j] := by
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp

/-- The reflectors of one more step. -/
private theorem pcQ_succ (st st' : PivotedQRState m n) (j : Fin n)
    (hA : ∀ q : Fin n, (q : ℕ) < j → storedHouseholderVec st'.A q = storedHouseholderVec st.A q)
    (hβ : ∀ q : Fin n, (q : ℕ) < j → st'.β q = st.β q) :
    pcQ ((j : ℕ) + 1) st' = pcQ j st * (1 - st'.β j • vecMulVec (storedHouseholderVec st'.A j)
      (storedHouseholderVec st'.A j)) := by
  rw [pcQ, pcQ, take_succ_finRange, List.map_append, List.map_cons, List.map_nil,
    householderProduct_concat]
  congr 2
  refine List.map_congr_left fun q hq => ?_
  have := lt_of_mem_take_finRange hq
  rw [hA q this, hβ q this]

/-- The column permutation of one more step. -/
private theorem pcP_succ (st st' : PivotedQRState m n) (j : Fin n)
    (hpiv : ∀ q : Fin n, (q : ℕ) < j → st'.piv q = st.piv q) :
    pcP ((j : ℕ) + 1) st' = pcP j st * Equiv.swap j (st'.piv j) := by
  rw [pcP, pcP, take_succ_finRange, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  congr 2
  exact List.map_congr_left fun q hq => by rw [hpiv q (lt_of_mem_take_finRange hq)]

/-- `C` of one more step is the new reflector applied to the column-swapped `C`. -/
private theorem pcC_succ (A : Matrix (Fin m) (Fin n) ℝ) (st st' : PivotedQRState m n)
    (j : Fin n) {P : Matrix (Fin m) (Fin m) ℝ} {s : Equiv.Perm (Fin n)}
    (hQ : pcQ ((j : ℕ) + 1) st' = pcQ j st * P) (hPs : Pᵀ = P)
    (hPi : pcP ((j : ℕ) + 1) st' = pcP j st * s) :
    pcC A ((j : ℕ) + 1) st' = P * (pcC A j st).submatrix id s := by
  rw [pcC, pcC, hQ, hPi, transpose_mul, hPs, Matrix.mul_assoc]
  congr 1

/-- Splitting off the first index of a tail sum. -/
private theorem sum_filter_le_succ {j : ℕ} (hj : j < m) (f : Fin m → ℝ) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin m => j ≤ (l : ℕ)), f l =
      f ⟨j, hj⟩ + ∑ l ∈ Finset.univ.filter (fun l : Fin m => j + 1 ≤ (l : ℕ)), f l := by
  have : Finset.univ.filter (fun l : Fin m => j ≤ (l : ℕ)) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun l : Fin m => j + 1 ≤ (l : ℕ))) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp)]

/-- One step of Algorithm 5.4.1 taken (`τ > 0`) preserves the invariant. -/
private theorem pcInv_step (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (st : PivotedQRState m n) (j : Fin n) (hI : pcInv A j st) (hτ : 0 < st.τ) :
    pcInv A ((j : ℕ) + 1) (Id.run (pivotedQRStep pure hnm st j)) := by
  obtain ⟨hr, ha, hb, hdiag, hβd, hβp, hc, hτeq⟩ := hI
  have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
  have hne := indexFrom_ne_nil hjm
  obtain ⟨hkj, hck⟩ := pivot_spec j hτeq hτ
  set k := (((List.finRange n).filter fun k => j ≤ k ∧ st.c k = st.τ).head?).getD j with hk
  set s := Equiv.swap j k with hs
  have hs_lt : ∀ q : Fin n, (q : ℕ) < j → s q = q := fun q hq =>
    Equiv.swap_apply_of_ne_of_ne (fun e => by rw [e] at hq; omega)
      (fun e => by rw [e] at hq; exact absurd (Fin.le_def.1 hkj) (by omega))
  have hs_ge : ∀ q : Fin n, (j : ℕ) ≤ q → (j : ℕ) ≤ s q := by
    intro q hq
    rw [hs, Equiv.swap_apply_def]
    split_ifs
    · exact Fin.le_def.1 hkj
    · exact le_rfl
    · exact hq
  set C := pcC A j st with hC
  set C' : Matrix (Fin m) (Fin n) ℝ := C.submatrix id s with hC'
  have hA₁ : ∀ (i : Fin m) (q : Fin n), ((i : ℕ) ≤ q ∨ (j : ℕ) ≤ q) →
      st.A.submatrix id s i q = C' i q := by
    intro i q h
    simp only [submatrix_apply, id, hC']
    rcases h with h | h
    · by_cases hq : (q : ℕ) < j
      · rw [hs_lt q hq]
        exact ha i q (Or.inl h)
      · exact ha i (s q) (Or.inr (hs_ge q (not_lt.1 hq)))
    · exact ha i (s q) (Or.inr (hs_ge q h))
  set x : Fin m → ℝ := fun i => st.A.submatrix id s i j with hx
  have hxC : ∀ i, x i = C' i j := fun i => hA₁ i j (Or.inr le_rfl)
  obtain ⟨hv1, hvout, hdich, hPO, hmul⟩ := houseOn_spec (nodup_indexFrom m j) hne x
  rw [head_indexFrom hjm hne] at hv1 hmul
  simp only [pivotedQRStep, hτ, ↓reduceIte, Id.run_bind, Id.run_pure, List.idRun_foldlM]
  rw [← hk, ← hs]
  rw [hx] at hv1 hvout hdich hPO hmul
  generalize Id.run (houseOn pure (indexFrom m ↑j) fun i => st.A.submatrix id s i j) = vβ
    at hv1 hvout hdich hPO hmul ⊢
  obtain ⟨v, b⟩ := vβ
  dsimp only at hv1 hvout hdich hPO hmul ⊢
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom n j) hvout b]
  set P : Matrix (Fin m) (Fin m) ℝ := 1 - b • vecMulVec v v with hP
  set A₁ := st.A.submatrix id s with hA₁def
  set A₂ : Matrix (Fin m) (Fin n) ℝ :=
    of fun i q => if q ∈ indexFrom n j then (P * A₁) i q else A₁ i q with hA₂
  set A₃ := A₂.updateCol j (fun i => if (j : ℕ) < i then v i else A₂ i j) with hA₃
  set jr : Fin m := Fin.castLE hnm j with hjr
  have hjr' : jr = ⟨j, hjm⟩ := Fin.ext rfl
  set l := (List.finRange n).filter fun i => j < i with hl
  rw [List.foldl_update_of_nodup (l := l) ((List.nodup_finRange n).filter _)
    (fun i y => y i - A₃ jr i * A₃ jr i) fun _ _ _ _ _ e => by rw [e]]
  -- facts about the reflector
  have hvlt : ∀ r : Fin m, (r : ℕ) < j → v r = 0 := fun r hr' =>
    hvout r (by rw [mem_indexFrom]; omega)
  have hPsymm : Pᵀ = P := transpose_one_sub_smul_vecMulVec b v
  have hPfix : ∀ (y : Fin m → ℝ) (r : Fin m), (r : ℕ) < j → (P *ᵥ y) r = y r := fun y r hr' => by
    rw [hP, one_sub_smul_vecMulVec_mulVec_apply, hvlt r hr', mul_zero, zero_mul, sub_zero]
  have hPM : ∀ (M : Matrix (Fin m) (Fin n) ℝ) i q, (P * M) i q = (P *ᵥ fun r => M r q) i :=
    fun _ _ _ => rfl
  -- the columns of the new array
  have hcol_lt : ∀ q : Fin n, (q : ℕ) < j → ∀ i, A₃ i q = st.A i q := fun q hq i => by
    have hqj : q ≠ j := fun e => by rw [e] at hq; omega
    rw [hA₃, updateCol_ne hqj, hA₂, of_apply, ite_eq_right_iff.2 (fun h => absurd
      (mem_indexFrom.1 h) (by omega)), hA₁def, submatrix_apply, id, hs_lt q hq]
  have hsvj : storedHouseholderVec A₃ j = v := funext fun i => by
    simp only [storedHouseholderVec]
    by_cases hij : (i : ℕ) < j
    · rw [ite_eq_left_iff.2 (fun h => absurd hij h), hvlt i hij]
    · rw [ite_eq_right_iff.2 (fun h => absurd h hij)]
      by_cases hij' : (i : ℕ) = j
      · rw [ite_eq_left_iff.2 (fun h => absurd hij' h)]
        have : i = ⟨j, hjm⟩ := Fin.ext hij'
        rw [this, hv1]
      · rw [ite_eq_right_iff.2 (fun h => absurd h hij'), hA₃, updateCol_self,
          ite_eq_left_iff.2 (fun h => absurd (by omega) h)]
  -- the reflector on the columns of `C'`
  have hPcol : ∀ q : Fin n, (q : ℕ) < j → ∀ i, (P * C') i q = C' i q := fun q hq i => by
    have hdot : (v ⬝ᵥ fun r => C' r q) = 0 := Finset.sum_eq_zero fun r _ => by
      change v r * C' r q = 0
      by_cases hr' : (r : ℕ) < j
      · rw [hvlt r hr', zero_mul]
      · rw [hC', submatrix_apply, id, hs_lt q hq, hb r q hq (by omega), mul_zero]
    rw [hPM, hP, one_sub_smul_vecMulVec_mulVec_apply, hdot, mul_zero, sub_zero]
  have hPA : ∀ (q : Fin n), (j : ℕ) ≤ q → ∀ i, (P * A₁) i q = (P * C') i q := fun q hq i => by
    rw [hPM, hPM]
    congr 2
    funext r
    exact hA₁ r q (Or.inr hq)
  have hA₃C : ∀ (i : Fin m) (q : Fin n), ((i : ℕ) ≤ q ∨ (j : ℕ) + 1 ≤ q) →
      A₃ i q = (P * C') i q := by
    intro i q h
    rcases lt_trichotomy (q : ℕ) j with hq | hq | hq
    · have hiq : (i : ℕ) ≤ q := h.resolve_right (by omega)
      rw [hcol_lt q hq, ha i q (Or.inl hiq), hPcol q hq, hC', submatrix_apply, id, hs_lt q hq]
    · have hq' : q = j := Fin.ext hq
      subst hq'
      have hiq : ¬ (q : ℕ) < i := by omega
      rw [hA₃, updateCol_self, ite_eq_right_iff.2 (fun h => absurd h hiq), hA₂, of_apply,
        ite_eq_left_iff.2 (fun h => absurd (mem_indexFrom.2 le_rfl) h), hPA q le_rfl]
    · have hqj : q ≠ j := fun e => by rw [e] at hq; omega
      rw [hA₃, updateCol_ne hqj, hA₂, of_apply,
        ite_eq_left_iff.2 (fun h => absurd (mem_indexFrom.2 (by omega)) h), hPA q (by omega)]
  have hPx : ∀ i, (P * C') i j = (P *ᵥ fun r => A₁ r j) i := fun i => by
    rw [hPM]
    congr 2
    funext r
    exact (hA₁ r j (Or.inr le_rfl)).symm
  have hne_j : ∀ q : Fin n, (q : ℕ) < j → q ≠ j := fun q hq e => by rw [e] at hq; omega
  have key : ∀ st' : PivotedQRState m n, st'.A = A₃ → st'.β = Function.update st.β j b →
      st'.piv = Function.update st.piv j k → st'.r = st.r + 1 →
      (∀ q : Fin n, (j : ℕ) + 1 ≤ q → st'.c q = st.c (s q) - A₃ jr q * A₃ jr q) →
      st'.τ = listMax st'.c l → pcInv A ((j : ℕ) + 1) st' := by
    intro st' hA' hβ' hpiv' hr' hc' hτ'
    have hsv : ∀ q : Fin n, (q : ℕ) < j →
        storedHouseholderVec st'.A q = storedHouseholderVec st.A q := fun q hq => by
      rw [hA']
      exact funext fun i => by simp only [storedHouseholderVec, hcol_lt q hq]
    have hQ' := pcQ_succ st st' j hsv (fun q hq => by rw [hβ', Function.update_of_ne (hne_j q hq)])
    rw [hA', hsvj, hβ', Function.update_self] at hQ'
    have hPi' := pcP_succ st st' j (fun q hq => by rw [hpiv', Function.update_of_ne (hne_j q hq)])
    rw [hpiv', Function.update_self] at hPi'
    have hC'' : pcC A ((j : ℕ) + 1) st' = P * C' := pcC_succ A st st' j hQ' hPsymm hPi'
    refine ⟨by rw [hr', hr], fun i q h => ?_, fun i q hq hqi => ?_, fun i q hq hiq => ?_,
      fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, ?_⟩
    · rw [hA', hC'']
      exact hA₃C i q h
    · rw [hC'']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · rw [hPcol q hq, hC', submatrix_apply, id, hs_lt q hq]
        exact hb i q hq hqi
      · have hq' : q = j := Fin.ext hq
        subst hq'
        rw [hPx, hmul]
        have hi1 : i ≠ ⟨q, hjm⟩ := fun e => by rw [e] at hqi; exact lt_irrefl _ hqi
        have hi2 : i ∈ indexFrom m q := by rw [mem_indexFrom]; omega
        simp [hi1, hi2]
    · rw [hC'']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · rw [hPcol q hq, hC', submatrix_apply, id, hs_lt q hq]
        exact hdiag i q hq hiq
      · have hq' : q = j := Fin.ext hq
        subst hq'
        have hi : i = ⟨q, hjm⟩ := Fin.ext hiq
        rw [hPx, hmul]
        simp only [hi, ↓reduceIte, Ne, norm_eq_zero]
        intro h0
        -- the pivot column has a nonzero trailing part
        have hpos : 0 < st.c k := hck ▸ hτ
        rw [hc k hkj] at hpos
        obtain ⟨r, hr, hr0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
        have hrq : r ∈ indexFrom m q := mem_indexFrom.2 (Finset.mem_filter.1 hr).2
        have := congrArg (fun w : EuclideanSpace ℝ {i // i ∈ indexFrom m q} => w ⟨r, hrq⟩) h0
        simp only [PiLp.zero_apply] at this
        apply hr0
        rw [hA₁ r q (Or.inr le_rfl), hC', submatrix_apply, id, hs, Equiv.swap_apply_left] at this
        rw [this]
        ring
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · rw [hβ', Function.update_of_ne (hne_j q hq), hsv q hq]
        exact hβd q hq
      · have hq' : q = j := Fin.ext hq
        subst hq'
        rw [hβ', Function.update_self, hA', hsvj]
        exact hdich
    · have hqj : q ≠ j := fun e => by rw [e] at hq; omega
      rw [hβ', hpiv', Function.update_of_ne hqj, Function.update_of_ne hqj]
      exact hβp q (by omega)
    · rw [hc' q hq, hC'']
      have hjq : (j : ℕ) ≤ s q := hs_ge q (by omega)
      rw [hc (s q) hjq]
      have hcolq : ∀ r, C r (s q) = C' r q := fun r => rfl
      simp only [hcolq]
      have hsum := sum_sq_mulVec_filter hPO (fun r => C' r q) (hPfix _)
      simp only [← hPM] at hsum
      rw [← hsum, sum_filter_le_succ hjm, hA₃C jr q (Or.inl (by simp [hjr]; omega)), hjr']
      ring
    · rw [hτ']
      congr 1
  refine key _ rfl rfl rfl rfl (fun q hq => ?_) rfl
  have hql : q ∈ l := by
    rw [hl, List.mem_filter]
    simp only [List.mem_finRange, true_and, decide_eq_true_eq, Fin.lt_def]
    omega
  simp only [hql, ↓reduceIte, Function.comp_apply]

/-- A step not taken (`τ ≤ 0`) leaves the state unchanged. -/
private theorem pivotedQRStep_of_not_pos (hnm : n ≤ m) (st : PivotedQRState m n) (j : Fin n)
    (h : ¬ 0 < st.τ) : Id.run (pivotedQRStep pure hnm st j) = st := by
  simp only [pivotedQRStep, h, ↓reduceIte, Id.run_pure]

/-- The initial state of Algorithm 5.4.1: `c(j)` the squared column norms, `τ` their maximum. -/
private noncomputable def pcInit (A : Matrix (Fin m) (Fin n) ℝ) : PivotedQRState m n :=
  ⟨A, 0, id, fun q => (fun i => A i q) ⬝ᵥ (fun i => A i q), 0,
    listMax (fun q => (fun i => A i q) ⬝ᵥ (fun i => A i q)) (List.finRange n)⟩

/-- The invariant holds initially. -/
private theorem pcInv_init (A : Matrix (Fin m) (Fin n) ℝ) : pcInv A 0 (pcInit A) := by
  have hC : pcC A 0 (pcInit A) = A := by
    simp [pcC, pcQ, pcP]
  refine ⟨rfl, fun i q _ => by rw [hC]; rfl, fun i q hq => absurd hq (Nat.not_lt_zero _),
    fun i q hq => absurd hq (Nat.not_lt_zero _), fun q hq => absurd hq (Nat.not_lt_zero _),
    fun q _ => ⟨rfl, rfl⟩, fun q _ => ?_, ?_⟩
  · rw [hC, Finset.filter_true_of_mem (fun i _ => Nat.zero_le _)]
    simp [pcInit, dotProduct, sq]
  · simp only [pcInit, Nat.zero_le, decide_true, List.filter_true]

/-- The run of Algorithm 5.4.1 at `Id` is the fold of its steps from `pcInit A`. -/
private theorem algorithm_5_4_1_run (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_5_4_1 pure hnm A) =
      (List.finRange n).foldl (fun st q => Id.run (pivotedQRStep pure hnm st q)) (pcInit A) := by
  have hc0 : Id.run ((List.finRange n).foldlM (fun (c : Fin n → ℝ) (j : Fin n) => do
      let d ← Chapter01.algorithm_1_1_1 pure (fun i => A i j) (fun i => A i j)
      pure (Function.update c j d)) 0) = fun q => (fun i => A i q) ⬝ᵥ (fun i => A i q) := by
    rw [List.idRun_foldlM]
    simp only [Id.run_bind, Chapter01.algorithm_1_1_1_spec, Id.run_pure]
    refine (List.foldl_update_eq_ite (fun j => (fun i => A i j) ⬝ᵥ (fun i => A i j)) _ _).trans ?_
    funext q
    simp only [List.mem_finRange, ↓reduceIte]
  unfold algorithm_5_4_1
  rw [Id.run_bind, hc0, List.idRun_foldlM]
  rfl

/-- The invariant along the fold: after the first `j` indices, `k ≤ j` steps have been taken,
and if fewer than `j`, the loop has stopped (`τ ≤ 0`). -/
private theorem pcInv_fold (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∀ j ≤ n, ∃ k ≤ j, pcInv A k (((List.finRange n).take j).foldl
        (fun st q => Id.run (pivotedQRStep pure hnm st q)) (pcInit A)) ∧
      (k < j → (((List.finRange n).take j).foldl
        (fun st q => Id.run (pivotedQRStep pure hnm st q)) (pcInit A)).τ ≤ 0) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨0, le_rfl, pcInv_init A, fun h => absurd h (lt_irrefl _)⟩
  | succ j ih =>
    intro hj
    obtain ⟨k, hkj, hI, hstop⟩ := ih (by omega)
    have ht := take_succ_finRange (n := n) ⟨j, by omega⟩
    simp only at ht
    rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set st := ((List.finRange n).take j).foldl
      (fun st q => Id.run (pivotedQRStep pure hnm st q)) (pcInit A)
    by_cases hτ : 0 < st.τ
    · have hk : k = j := by
        by_contra hne
        exact absurd (hstop (by omega)) (not_le.2 hτ)
      subst hk
      exact ⟨k + 1, le_rfl, pcInv_step hnm A st ⟨k, by omega⟩ hI hτ,
        fun h => absurd h (lt_irrefl _)⟩
    · rw [pivotedQRStep_of_not_pos hnm st _ hτ]
      exact ⟨k, by omega, hI, fun _ => not_lt.1 hτ⟩

/-- The members of `(List.finRange n).drop r` are the indices from `r` on. -/
private theorem le_of_mem_drop_finRange {r : ℕ} {q : Fin n}
    (hq : q ∈ (List.finRange n).drop r) : r ≤ (q : ℕ) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  rw [List.getElem_drop, List.getElem_finRange]
  change r ≤ r + i
  omega

/-- A right fold of products from `p₀` is `p₀` times the product. -/
private theorem foldl_mul_eq_mul_prod {α : Type*} [Monoid α] {ι : Type*} (g : ι → α)
    (l : List ι) (p₀ : α) : l.foldl (fun p q => p * g q) p₀ = p₀ * (l.map g).prod := by
  induction l generalizing p₀ with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- **Algorithm 5.4.1 computes the factorization (5.4.6)** (exact arithmetic, `m ≥ n`): with
`(A', β, piv, r)` the output, `Q = H₁ ⋯ H_n` the factored form of the stored vectors and the
returned `β` (the steps not taken have `β_j = 0`, `H_j = I`), `Π` the product of the
transpositions `(j, piv j)` and `R` the upper triangle of `A'`, `A Π = QR` is a rank-revealing
QR factorization: the rows of `R` from the `r`-th on vanish and `R₁₁` is nonsingular; hence
`r = rank A`. Every `β_j` is `0` or `2/v⁽ʲ⁾ᵀv⁽ʲ⁾`. The invariant (5.4.7): after `k` steps the array
holds `R⁽ᵏ⁾ = H_k ⋯ H₁ A Π₁ ⋯ Π_k` with `R₁₁⁽ᵏ⁾` upper triangular and nonsingular, and `c(j)`
the squared norms of the columns of `R₂₂⁽ᵏ⁾` (`norm_sq_tail_eq`); the loop stops exactly when
`R₂₂⁽ᵏ⁾ = 0`. -/
theorem algorithm_5_4_1_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsPivotedQR.IsRankRevealing A
        (factoredQ (Id.run (algorithm_5_4_1 pure hnm A)).β (Id.run (algorithm_5_4_1 pure hnm A)).A)
        (upperPart (Id.run (algorithm_5_4_1 pure hnm A)).A)
        (pivotPerm (Id.run (algorithm_5_4_1 pure hnm A)).piv)
        (Id.run (algorithm_5_4_1 pure hnm A)).r ∧
      (Id.run (algorithm_5_4_1 pure hnm A)).r = A.rank ∧
      ∀ q, (Id.run (algorithm_5_4_1 pure hnm A)).β q = 0 ∨
        (Id.run (algorithm_5_4_1 pure hnm A)).β q *
          (storedHouseholderVec (Id.run (algorithm_5_4_1 pure hnm A)).A q ⬝ᵥ
            storedHouseholderVec (Id.run (algorithm_5_4_1 pure hnm A)).A q) = 2 := by
  obtain ⟨r, hrn, hI, hstop⟩ := pcInv_fold hnm A n le_rfl
  rw [List.take_of_length_le (by simp), ← algorithm_5_4_1_run] at hI hstop
  generalize Id.run (algorithm_5_4_1 pure hnm A) = out at hI hstop ⊢
  obtain ⟨hr, ha, hb, hdiag, hβd, hβp, hc, hτ⟩ := hI
  subst hr
  set C := pcC A out.r out with hC
  -- the trailing block vanishes
  have htrail : ∀ (i : Fin m) (q : Fin n), out.r ≤ (i : ℕ) → out.r ≤ (q : ℕ) → C i q = 0 := by
    intro i q hi hq
    have hτ0 := hstop (lt_of_le_of_lt hq q.isLt)
    have hcq : out.c q ≤ 0 := ((le_listMax out.c _).2 q (by
      rw [List.mem_filter]
      simpa using hq)).trans (hτ ▸ hτ0)
    rw [hc q hq] at hcq
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg (C l q))).1
      (le_antisymm hcq (Finset.sum_nonneg fun l _ => sq_nonneg _)) i (by simpa using hi)
    exact pow_eq_zero_iff two_ne_zero |>.1 h0
  have hdichAll : ∀ q, out.β q = 0 ∨
      out.β q * (storedHouseholderVec out.A q ⬝ᵥ storedHouseholderVec out.A q) = 2 := fun q => by
    by_cases hq : (q : ℕ) < out.r
    · exact hβd q hq
    · exact Or.inl (hβp q (not_lt.1 hq)).1
  -- the reflectors and the permutation of the steps taken are those of the whole run
  have hQ : pcQ out.r out = factoredQ out.β out.A := by
    have e : pcQ out.r out = (((List.finRange n).take out.r).map fun q =>
        1 - out.β q • vecMulVec (storedHouseholderVec out.A q)
          (storedHouseholderVec out.A q)).prod := by
      simp only [pcQ, householderProduct, List.map_map]
      rfl
    have hdrop : (((List.finRange n).drop out.r).map fun q =>
        1 - out.β q • vecMulVec (storedHouseholderVec out.A q)
          (storedHouseholderVec out.A q)).prod = 1 := by
      refine List.prod_eq_one fun M hM => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
      simp [(hβp q (le_of_mem_drop_finRange hq)).1]
    rw [e, factoredQ_eq_prod]
    conv_rhs => rw [← List.take_append_drop out.r (List.finRange n), List.map_append,
      List.prod_append]
    rw [hdrop, mul_one]
  have hP : pcP out.r out = pivotPerm out.piv := by
    have hdrop : (((List.finRange n).drop out.r).map fun q =>
        Equiv.swap q (out.piv q)).prod = 1 := by
      refine List.prod_eq_one fun M hM => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
      rw [(hβp q (le_of_mem_drop_finRange hq)).2, Equiv.swap_self, ← Equiv.Perm.one_def]
    rw [pcP, pivotPerm, foldl_mul_eq_mul_prod, one_mul]
    conv_rhs => rw [← List.take_append_drop out.r (List.finRange n), List.map_append,
      List.prod_append]
    rw [hdrop, mul_one]
  have hR : upperPart out.A = C := by
    ext i q
    simp only [upperPart, of_apply]
    split_ifs with h
    · exact ha i q (Or.inl h)
    · by_cases hq : (q : ℕ) < out.r
      · exact (hb i q hq (by omega)).symm
      · exact (htrail i q (by omega) (by omega)).symm
  have hO : factoredQ out.β out.A ∈ orthogonalGroup (Fin m) ℝ := by
    refine householderProduct_mem_orthogonalGroup fun p hp => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
    exact hdichAll k
  have hup : ∀ (i : Fin m) (q : Fin n), (q : ℕ) < i → upperPart out.A i q = 0 :=
    fun i q hqi => by
      simp only [upperPart, of_apply]
      rw [ite_eq_right_iff]
      intro h
      omega
  have hRR : IsPivotedQR.IsRankRevealing A (factoredQ out.β out.A) (upperPart out.A)
      (pivotPerm out.piv) out.r := by
    refine ⟨⟨⟨hO, hup, ?_⟩⟩, hrn.trans hnm, hrn, fun i q hi => ?_, ?_⟩
    · rw [hR, hC, pcC, hQ, hP, mul_transpose_mul_of_mem_orthogonalGroup hO]
    · simp only [upperPart, of_apply]
      split_ifs with h
      · rw [ha i q (Or.inl h)]
        exact htrail i q hi (by omega)
      · rfl
    · have hup' : ((upperPart out.A).submatrix (Fin.castLE (hrn.trans hnm))
          (Fin.castLE hrn)).IsUpperTriangular := fun i q hqi =>
        hup (Fin.castLE _ i) (Fin.castLE _ q) hqi
      refine (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hup').2 fun i => ?_
      rw [submatrix_apply, hR]
      exact hdiag _ _ (by simp) (by simp)
  exact ⟨hRR, hRR.rank_eq.symm, hdichAll⟩

end PivotedQRSpec

/-! ### §5.4.7 The complete orthogonal decomposition in exact arithmetic -/

section CompleteOrthogonalSpec

/-- `A Π = A.submatrix id (pivotPerm piv)` for the permutation matrix `Π = pivotMatrix piv`. -/
theorem mul_pivotMatrix {p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (piv : Fin n → Fin n) :
    A * pivotMatrix piv = A.submatrix id (pivotPerm piv) := by
  rw [pivotMatrix, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]

/-- The permutation matrix `Π` of Algorithm 5.4.1 is orthogonal. -/
theorem pivotMatrix_mem_orthogonalGroup (piv : Fin n → Fin n) :
    pivotMatrix piv ∈ orthogonalGroup (Fin n) ℝ := by
  have h : pivotMatrix piv = (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (pivotPerm piv) := by
    rw [pivotMatrix, ← Matrix.one_mul (Equiv.toPEquiv _).toMatrix, PEquiv.mul_toMatrix_toPEquiv,
      Equiv.symm_symm]
  rw [h]
  exact one_submatrix_mem_unitaryGroup (𝕜 := ℝ) (pivotPerm piv)

/-- **§5.4.7, the two-step complete orthogonal decomposition is one** (exact arithmetic): the
output `(U, V, r)` satisfies `Uᵀ A V = [T₁₁ 0; 0 0]` with `U`, `V` orthogonal and `T₁₁`
nonsingular of order `r = rank A` (`Matrix.IsCompleteOrthogonal`). From `algorithm_5_4_1_spec`
(`Uᵀ A Π = [R₁₁ R₁₂; 0 0]`), `algorithm_5_2_1_spec` on `[R₁₁ R₁₂]ᵀ = Q [S₁; 0]` (full column rank
since `R₁₁` is nonsingular, so `S₁` is nonsingular) and backward accumulation
(`backwardAccumulation_spec`): `Uᵀ A (Π Q) = [S₁ᵀ 0; 0 0]`. -/
theorem completeOrthogonalDecomposition_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsCompleteOrthogonal A (Id.run (completeOrthogonalDecomposition pure hnm A)).1
        (Id.run (completeOrthogonalDecomposition pure hnm A)).2.1
        (Id.run (completeOrthogonalDecomposition pure hnm A)).2.2 ∧
      (Id.run (completeOrthogonalDecomposition pure hnm A)).2.2 = A.rank := by
  obtain ⟨h1, hrank, -⟩ := algorithm_5_4_1_spec hnm A
  unfold completeOrthogonalDecomposition
  simp only [Id.run_bind, Id.run_pure, backwardAccumulation_spec]
  generalize Id.run (algorithm_5_4_1 pure hnm A) = out at h1 hrank ⊢
  set T : Matrix (Fin n) (Fin out.r) ℝ := fun i k =>
    if hk : (k : ℕ) < m then upperPart out.A ⟨k, hk⟩ i else 0 with hT
  have hrn : out.r ≤ n := h1.le_cols
  obtain ⟨h2, -⟩ := algorithm_5_2_1_spec hrn T
  generalize Id.run (algorithm_5_2_1 pure T) = QR at h2 ⊢
  change IsCompleteOrthogonal A (factoredQ out.β out.A)
    (pivotMatrix out.piv * factoredQ QR.2 QR.1) out.r ∧ out.r = A.rank
  set Q₁ := factoredQ out.β out.A with hQ₁
  set Q₂ := factoredQ QR.2 QR.1 with hQ₂
  set R := upperPart out.A with hR
  set S := upperPart QR.1 with hS
  have hQ₁O : Q₁ ∈ orthogonalGroup (Fin m) ℝ := h1.isQR.mem_unitaryGroup
  have hQ₂O : Q₂ ∈ orthogonalGroup (Fin n) ℝ := h2.mem_unitaryGroup
  -- `Q₁ᵀ A Π = R` and `Q₂ᵀ T = S`
  have hRA : Q₁ᵀ * A.submatrix id (pivotPerm out.piv) = R := by
    rw [← h1.isQR.mul_eq, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hQ₁O,
      Matrix.one_mul]
  have hST : Q₂ᵀ * T = S := by
    rw [← h2.mul_eq, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hQ₂O, Matrix.one_mul]
  have hTR : ∀ i (k : Fin out.r), T i k = R (Fin.castLE h1.le_rows k) i := fun i k => by
    simp only [hT]
    split_ifs with hk
    · rfl
    · exact absurd (lt_of_lt_of_le k.isLt h1.le_rows) hk
  -- the entries of `Q₁ᵀ A V`
  have hentry : ∀ (i : Fin m) (j : Fin n), (Q₁ᵀ * A * (pivotMatrix out.piv * Q₂)) i j =
      if hi : (i : ℕ) < out.r then S j ⟨i, hi⟩ else 0 := by
    intro i j
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Q₁ᵀ, mul_pivotMatrix, hRA]
    split_ifs with hi
    · rw [← hST, mul_apply, mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [transpose_apply, hTR, mul_comm]
      rfl
    · rw [mul_apply]
      exact Finset.sum_eq_zero fun l _ => by rw [h1.apply_eq_zero i l (by omega), zero_mul]
  -- `T` has independent columns
  have hTli : LinearIndependent ℝ Tᵀ := by
    refine mulVec_injective_iff.1 fun g g' hgg => ?_
    have hB := h1.isUnit_block
    rw [← sub_eq_zero]
    have hd : T *ᵥ (g - g') = 0 := by rw [mulVec_sub, hgg, sub_self]
    have hB' : (R.submatrix (Fin.castLE h1.le_rows) (Fin.castLE h1.le_cols))ᵀ *ᵥ (g - g') = 0 := by
      funext i
      have := congrFun hd (Fin.castLE hrn i)
      simp only [mulVec, dotProduct, Pi.zero_apply] at this ⊢
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [transpose_apply, submatrix_apply, hTR]
    have hBt : IsUnit (R.submatrix (Fin.castLE h1.le_rows) (Fin.castLE h1.le_cols))ᵀ :=
      (isUnit_transpose _).2 hB
    exact (mulVec_injective_iff_isUnit.2 hBt) (by rw [hB', mulVec_zero])
  have hS1 := h2.isUnit_firstRows_of_linearIndependent hrn hTli
  refine ⟨⟨by simpa using hQ₁O, mul_mem (pivotMatrix_mem_orthogonalGroup out.piv) hQ₂O,
    h1.le_rows, hrn, fun i j hij => ?_, ?_⟩, hrank⟩
  · rw [conjTranspose_eq_transpose_of_trivial, hentry]
    split_ifs with hi
    · exact h2.apply_eq_zero j ⟨i, hi⟩ (by simp only; omega)
    · rfl
  · rw [conjTranspose_eq_transpose_of_trivial]
    have e : (Q₁ᵀ * A * (pivotMatrix out.piv * Q₂)).submatrix (Fin.castLE h1.le_rows)
        (Fin.castLE hrn) = (firstRows S hrn)ᵀ := by
      ext i j
      rw [submatrix_apply, hentry]
      split_ifs with hi
      · rfl
      · exact absurd (by simp) hi
    rw [e]
    exact (isUnit_transpose _).2 hS1

end CompleteOrthogonalSpec

/-! ### §5.4.8 Bidiagonalization -/

section Bidiagonalization

/-- **(5.4.13)**: for `A ∈ ℝ^{m×n}` there are orthogonal `U_B ∈ ℝ^{m×m}`, `V_B ∈ ℝ^{n×n}` with
`U_Bᵀ A V_B` upper bidiagonal (`d_i` on the diagonal, `f_i` above it, zero elsewhere). -/
theorem equation_5_4_13 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin m) ℝ, ∃ V ∈ orthogonalGroup (Fin n) ℝ,
      ∀ (i : Fin m) (j : Fin n), (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → (Uᵀ * A * V) i j = 0 := by
  obtain ⟨U, V, B, h⟩ := exists_isBidiagonalization A
  refine ⟨U, h.left_mem_unitaryGroup, V, h.right_mem_unitaryGroup, fun i j h1 h2 => ?_⟩
  have := h.conj_eq
  rw [conjTranspose_eq_transpose_of_trivial] at this
  rw [this]
  exact h.isUpperBidiagonalRect i j h1 h2

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step `j` of Algorithm 5.4.2: a left Householder step on column `j` (rows `j:m`, columns
`j:n`, the vector stored below the diagonal) and, while `j ≤ n - 2` (1-based), a right Householder
step on row `j` (columns `j+1:n`, rows `j:m`, the vector stored in `A(j, j+2:n)`). The row
`A(j, j+1:n)` is the function `A j` on the column list (no transpose copy, convention 10). -/
noncomputable def bidiagonalizationStep (hnm : n ≤ m)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ)) := do
  let uβ ← houseOn rnd (indexFrom m j) (fun i => st.1 i j)
  let A ← householderApplyLeft rnd uβ.1 uβ.2 (indexFrom m j) (indexFrom n j) st.1
  let A := A.updateCol j (fun i => if (j : ℕ) < i then uβ.1 i else A i j)
  if (j : ℕ) + 3 ≤ n then do
    let jr : Fin m := Fin.castLE hnm j
    let wγ ← houseOn rnd (indexFrom n (j + 1)) (A jr)
    let A ← householderApplyRight rnd wγ.1 wγ.2 (indexFrom m j) (indexFrom n (j + 1)) A
    let A := A.updateRow jr (fun q => if (j : ℕ) + 1 < q then wγ.1 q else A jr q)
    pure (A, Function.update st.2.1 j uβ.2, Function.update st.2.2 j wγ.2)
  else pure (A, Function.update st.2.1 j uβ.2, st.2.2)

/-- **Algorithm 5.4.2 (Householder Bidiagonalization)**: "Given `A ∈ ℝ^{m×n}` with `m ≥ n`, the
following algorithm overwrites `A` with `U_Bᵀ A V_B = B` where `B` is upper bidiagonal and
`U_B = U₁ ⋯ U_n` and `V_B = V₁ ⋯ V_{n-2}`. The essential part of `U_j`'s Householder vector is
stored in `A(j+1:m, j)` and the essential part of `V_j`'s Householder vector is stored in
`A(j, j+2:n)`":
```
for j = 1:n
    [v, β] = house(A(j:m, j))
    A(j:m, j:n) = (I - β v vᵀ) A(j:m, j:n)
    A(j+1:m, j) = v(2:m-j+1)
    if j ≤ n - 2
        [v, β] = house(A(j, j+1:n)ᵀ)
        A(j:m, j+1:n) = A(j:m, j+1:n) (I - β v vᵀ)
        A(j, j+2:n) = v(2:n-j)ᵀ
    end
end
```
(the second call is printed "ho se"). The program returns the array and both lists of `β`. -/
noncomputable def algorithm_5_4_2 (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ)) :=
  (List.finRange n).foldlM (bidiagonalizationStep rnd hnm) (A, 0, 0)

end Bidiagonalization

/-! ### §5.4.8 Algorithm 5.4.2 in exact arithmetic -/

section BidiagonalizationSpec

/-- **The Householder vector of the right reflector `V_k`** read from row `k` of an array
overwritten by Algorithm 5.4.2: zeros in positions `≤ k`, `1` at `k + 1`, and the essential part
`A(k, k+2:n)` stored there. -/
def storedRowVec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) (k : Fin n) : Fin n → ℝ :=
  fun q => if (q : ℕ) < k + 1 then 0 else if (q : ℕ) = k + 1 then 1 else A (Fin.castLE hnm k) q

/-- **The factored form `V_B = V₁ ⋯ V_n`** of Algorithm 5.4.2's right reflectors: the vectors
stored in the rows of the array and the returned `γ` (a step without a right reflector records
`γ_k = 0`, an identity factor). -/
noncomputable def bidiagRightQ (hnm : n ≤ m) (γ : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  householderProduct (List.ofFn fun k => (storedRowVec hnm A k, γ k))

/-- **The bidiagonal part** of an array: its diagonal `d_i` and superdiagonal `f_i`, zero
elsewhere (the book's `B`, read off the overwritten `A`). -/
def bidiagonalPart (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i q => if (q : ℕ) = i ∨ (q : ℕ) = i + 1 then A i q else 0

/-- Two dot products with `v` agree when the second factors agree wherever `v` is nonzero. -/
private theorem dotProduct_congr_of_ne_zero {ι : Type*} [Fintype ι] {v f g : ι → ℝ}
    (h : ∀ r, v r ≠ 0 → f r = g r) : v ⬝ᵥ f = v ⬝ᵥ g := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : v r = 0
  · rw [hr, zero_mul, zero_mul]
  · rw [h r hr]

/-- An element of the first `j` entries of `List.finRange n` is below `j`. -/
private theorem bidiag_lt_of_mem_take {j : ℕ} {k : Fin n}
    (hk : k ∈ (List.finRange n).take j) : (k : ℕ) < j := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  simp only [List.length_take, List.length_finRange] at hi
  rw [List.getElem_take, List.getElem_finRange]
  change i < j
  omega

/-- The product of the left reflectors of the first `j` steps of Algorithm 5.4.2, read from the
state. -/
private noncomputable def bidiagLeftPrefix (j : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ)) : Matrix (Fin m) (Fin m) ℝ :=
  householderProduct
    (((List.finRange n).take j).map fun k => (storedHouseholderVec st.1 k, st.2.1 k))

/-- The product of the right reflectors of the first `j` steps of Algorithm 5.4.2, read from the
state. -/
private noncomputable def bidiagRightPrefix (hnm : n ≤ m) (j : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  householderProduct
    (((List.finRange n).take j).map fun k => (storedRowVec hnm st.1 k, st.2.2 k))

/-- The invariant of Algorithm 5.4.2 after `j` steps, with `C = U_jᵀ A V_j` for the products of
the reflectors so far: outside the stored vectors the array holds `C`; the processed columns of
`C` vanish below the diagonal and its processed rows beyond the superdiagonal; the recorded `β`,
`γ` are `0` or `2/vᵀv`, and the `γ` of the steps to come are `0`. -/
private def bidiagInvariant (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ)) : Prop :=
  (∀ (i : Fin m) (q : Fin n), ¬ ((q : ℕ) < j ∧ (q : ℕ) < i) → ¬ ((i : ℕ) < j ∧ (i : ℕ) + 1 < q) →
      st.1 i q = ((bidiagLeftPrefix j st)ᵀ * A * bidiagRightPrefix hnm j st) i q) ∧
    (∀ (i : Fin m) (q : Fin n), (q : ℕ) < j → (q : ℕ) < i →
      ((bidiagLeftPrefix j st)ᵀ * A * bidiagRightPrefix hnm j st) i q = 0) ∧
    (∀ (i : Fin m) (q : Fin n), (i : ℕ) < j → (i : ℕ) + 1 < q →
      ((bidiagLeftPrefix j st)ᵀ * A * bidiagRightPrefix hnm j st) i q = 0) ∧
    (∀ k : Fin n, (k : ℕ) < j → st.2.1 k = 0 ∨
      st.2.1 k * (storedHouseholderVec st.1 k ⬝ᵥ storedHouseholderVec st.1 k) = 2) ∧
    (∀ k : Fin n, (k : ℕ) < j → st.2.2 k = 0 ∨
      st.2.2 k * (storedRowVec hnm st.1 k ⬝ᵥ storedRowVec hnm st.1 k) = 2) ∧
    ∀ k : Fin n, j ≤ (k : ℕ) → st.2.2 k = 0

/-- The core of one step of Algorithm 5.4.2: given the data of the left reflector `(v, b)`, the
array `A1` after the left update, the data of the right reflector `(w, g)` (`g = 0` when there is
none) and the array `B3` after the right update, the invariant advances. -/
private theorem bidiagInvariant_step_core (hnm : n ≤ m) (A B : Matrix (Fin m) (Fin n) ℝ)
    (β γ : Fin n → ℝ) (j : Fin n) (hI : bidiagInvariant hnm A j (B, β, γ))
    (v : Fin m → ℝ) (b : ℝ) (hvout : ∀ i : Fin m, (i : ℕ) < j → v i = 0)
    (hv1 : ∀ i : Fin m, (i : ℕ) = j → v i = 1) (hdich : b = 0 ∨ b * (v ⬝ᵥ v) = 2)
    (hmul : ∀ i : Fin m, (j : ℕ) < i → ((1 - b • vecMulVec v v) *ᵥ fun r => B r j) i = 0)
    (A1 : Matrix (Fin m) (Fin n) ℝ)
    (hA1 : ∀ (i : Fin m) (q : Fin n), A1 i q = if q = j ∧ (j : ℕ) < i then v i else
      if (j : ℕ) ≤ q then ((1 - b • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * B) i q
      else B i q)
    (w : Fin n → ℝ) (g : ℝ) (B3 : Matrix (Fin m) (Fin n) ℝ)
    (hwout : ∀ q : Fin n, (q : ℕ) < j + 1 → w q = 0)
    (hg : g = 0 ∨ g * (storedRowVec hnm B3 j ⬝ᵥ storedRowVec hnm B3 j) = 2)
    (hW : g • vecMulVec (storedRowVec hnm B3 j) (storedRowVec hnm B3 j) = g • vecMulVec w w)
    (hred : ∀ q : Fin n, (j : ℕ) + 1 < q →
      A1 (Fin.castLE hnm j) q - g * (A1 (Fin.castLE hnm j) ⬝ᵥ w) * w q = 0)
    (hB3 : ∀ (i : Fin m) (q : Fin n), ¬ ((i : ℕ) = j ∧ (j : ℕ) + 1 < q) →
      B3 i q = if (j : ℕ) ≤ i then A1 i q - g * (A1 i ⬝ᵥ w) * w q else A1 i q) :
    bidiagInvariant hnm A ((j : ℕ) + 1) (B3, Function.update β j b, Function.update γ j g) := by
  obtain ⟨ha, hb, hc, hdβ, hdγ, hγ0⟩ := hI
  obtain ⟨C, hC⟩ : ∃ C,
      C = (bidiagLeftPrefix j (B, β, γ))ᵀ * A * bidiagRightPrefix hnm j (B, β, γ) :=
    ⟨_, rfl⟩
  have ha' : ∀ (i : Fin m) (q : Fin n), ¬ ((q : ℕ) < j ∧ (q : ℕ) < i) →
      ¬ ((i : ℕ) < j ∧ (i : ℕ) + 1 < q) → B i q = C i q := fun i q h1 h2 => by
    rw [hC]; exact ha i q h1 h2
  have hb' : ∀ (i : Fin m) (q : Fin n), (q : ℕ) < j → (q : ℕ) < i → C i q = 0 :=
    fun i q h1 h2 => by rw [hC]; exact hb i q h1 h2
  have hc' : ∀ (i : Fin m) (q : Fin n), (i : ℕ) < j → (i : ℕ) + 1 < q → C i q = 0 :=
    fun i q h1 h2 => by rw [hC]; exact hc i q h1 h2
  obtain ⟨D, hDdef⟩ : ∃ D, D = (1 - b • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * C := ⟨_, rfl⟩
  have hD : ∀ (i : Fin m) (q : Fin n), D i q = C i q - b * v i * (v ⬝ᵥ fun r => C r q) :=
      fun i q => by
    rw [hDdef, one_sub_smul_vecMulVec_mul_apply]
  -- the left update
  have hvdot : ∀ q : Fin n, (j : ℕ) ≤ q →
      (v ⬝ᵥ fun r => B r q) = v ⬝ᵥ fun r => C r q := fun q hq =>
    dotProduct_congr_of_ne_zero fun r hr => by
      have hr' : ¬ (r : ℕ) < j := fun h => hr (hvout r h)
      exact ha' r q (fun h => absurd h.1 (by omega)) (fun h => hr' h.1)
  have hA1lt : ∀ (i : Fin m) (q : Fin n), (i : ℕ) < j → A1 i q = B i q := fun i q hi => by
    rw [hA1 i q, ite_eq_right (show ¬ (q = j ∧ (j : ℕ) < i) from fun h => absurd h.2 (by omega))]
    split_ifs
    · rw [one_sub_smul_vecMulVec_mul_apply, hvout i hi]; ring
    · rfl
  have hA1col : ∀ (i : Fin m) (q : Fin n), (q : ℕ) < j → A1 i q = B i q := fun i q hq => by
    rw [hA1 i q, ite_eq_right (show ¬ (q = j ∧ (j : ℕ) < i) from fun h => by
      have := congrArg Fin.val h.1; omega), ite_eq_right (show ¬ ((j : ℕ) ≤ q) by omega)]
  have hDrow : ∀ (i : Fin m) (q : Fin n), (i : ℕ) < j → D i q = C i q := fun i q hi => by
    rw [hD, hvout i hi]; ring
  have hDcol : ∀ (i : Fin m) (q : Fin n), (q : ℕ) < j → D i q = C i q := fun i q hq => by
    have h0 : (v ⬝ᵥ fun r => C r q) = 0 := Finset.sum_eq_zero fun r _ => by
      change v r * C r q = 0
      by_cases hr : (r : ℕ) < j
      · rw [hvout r hr, zero_mul]
      · rw [hb' r q hq (by omega), mul_zero]
    rw [hD, h0]; ring
  have hPB : ∀ (i : Fin m) (q : Fin n), (j : ℕ) ≤ i → (j : ℕ) ≤ q →
      ((1 - b • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * B) i q = D i q := fun i q hi hq => by
    rw [one_sub_smul_vecMulVec_mul_apply, hD, ha' i q (fun h => absurd h.1 (by omega))
      (fun h => absurd h.1 (by omega)), hvdot q hq]
  have hA1a : ∀ (i : Fin m) (q : Fin n), (j : ℕ) ≤ i → (j : ℕ) < q → A1 i q = D i q :=
      fun i q hi hq => by
    rw [hA1 i q, ite_eq_right (show ¬ (q = j ∧ (j : ℕ) < i) from fun h => by
      have := congrArg Fin.val h.1; omega), ite_eq_left (show (j : ℕ) ≤ q by omega)]
    exact hPB i q hi hq.le
  have hA1b : ∀ i : Fin m, (i : ℕ) = j → A1 i j = D i j := fun i hi => by
    rw [hA1 i j, ite_eq_right (show ¬ (j = j ∧ (j : ℕ) < i) from fun h => absurd h.2 (by omega)),
      ite_eq_left (show (j : ℕ) ≤ j from le_rfl)]
    exact hPB i j hi.ge le_rfl
  have hA1dot : ∀ i : Fin m, (j : ℕ) ≤ i → A1 i ⬝ᵥ w = D i ⬝ᵥ w := fun i hi => by
    rw [dotProduct_comm, dotProduct_comm (D i)]
    exact dotProduct_congr_of_ne_zero fun q hq =>
      hA1a i q hi (by by_contra h; exact hq (hwout q (by omega)))
  have hDj : ∀ i : Fin m, (j : ℕ) < i → D i j = 0 := fun i hi => by
    have h1 := hmul i hi
    rw [one_sub_smul_vecMulVec_mulVec_apply] at h1
    rw [hD, ← ha' i j (fun h => absurd h.1 (lt_irrefl _)) (fun h => absurd h.1 (by omega)),
      ← hvdot j le_rfl]
    exact h1
  -- the new array
  have hB3col : ∀ (i : Fin m) (k : Fin n), (k : ℕ) ≤ j → B3 i k = A1 i k := fun i k hk => by
    rw [hB3 i k (fun h => absurd h.2 (by omega)), hwout k (by omega), mul_zero, sub_zero, ite_self]
  have hB3row : ∀ (i : Fin m) (q : Fin n), (i : ℕ) < j → B3 i q = B i q := fun i q hi => by
    rw [hB3 i q (fun h => absurd h.1 (by omega)), ite_eq_right (show ¬ ((j : ℕ) ≤ i) by omega),
      hA1lt i q hi]
  have hsvk : ∀ k : Fin n, (k : ℕ) < j → storedHouseholderVec B3 k = storedHouseholderVec B k :=
    fun k hk => funext fun i => by
      simp only [storedHouseholderVec, hB3col i k hk.le, hA1col i k hk]
  have hsvj : storedHouseholderVec B3 j = v := funext fun i => by
    simp only [storedHouseholderVec]
    by_cases hij : (i : ℕ) < j
    · rw [ite_eq_left hij, hvout i hij]
    · rw [ite_eq_right hij]
      by_cases hij' : (i : ℕ) = j
      · rw [ite_eq_left hij', hv1 i hij']
      · rw [ite_eq_right hij', hB3col i j le_rfl, hA1 i j,
          ite_eq_left (show j = j ∧ (j : ℕ) < i from ⟨rfl, by omega⟩)]
  have hsrk : ∀ k : Fin n, (k : ℕ) < j → storedRowVec hnm B3 k = storedRowVec hnm B k :=
    fun k hk => funext fun q => by
      simp only [storedRowVec, hB3row (Fin.castLE hnm k) q hk]
  -- the new products of reflectors
  have htake : (List.finRange n).take ((j : ℕ) + 1) = (List.finRange n).take j ++ [j] := by
    rw [List.take_succ_eq_append_getElem (by simp)]
    simp
  have hL3 : bidiagLeftPrefix ((j : ℕ) + 1) (B3, Function.update β j b, Function.update γ j g) =
      bidiagLeftPrefix j (B, β, γ) * (1 - b • vecMulVec v v) := by
    rw [bidiagLeftPrefix, bidiagLeftPrefix, htake, List.map_append, List.map_cons, List.map_nil,
      householderProduct_concat]
    congr 1
    · congr 1
      refine List.map_congr_left fun k hk => ?_
      have hk' := bidiag_lt_of_mem_take hk
      have hkj : k ≠ j := fun e => by rw [e] at hk'; omega
      simp only [hsvk k hk', Function.update_of_ne hkj]
    · simp only [hsvj, Function.update_self]
  have hR3 : bidiagRightPrefix hnm ((j : ℕ) + 1)
      (B3, Function.update β j b, Function.update γ j g) =
      bidiagRightPrefix hnm j (B, β, γ) * (1 - g • vecMulVec w w) := by
    rw [bidiagRightPrefix, bidiagRightPrefix, htake, List.map_append, List.map_cons, List.map_nil,
      householderProduct_concat]
    congr 1
    · congr 1
      refine List.map_congr_left fun k hk => ?_
      have hk' := bidiag_lt_of_mem_take hk
      have hkj : k ≠ j := fun e => by rw [e] at hk'; omega
      simp only [hsrk k hk', Function.update_of_ne hkj]
    · simp only [Function.update_self, hW]
  have hC3 : ∀ (i : Fin m) (q : Fin n), ((bidiagLeftPrefix ((j : ℕ) + 1)
      (B3, Function.update β j b, Function.update γ j g))ᵀ * A *
      bidiagRightPrefix hnm ((j : ℕ) + 1) (B3, Function.update β j b, Function.update γ j g)) i q =
      D i q - g * (D i ⬝ᵥ w) * w q := fun i q => by
    rw [hL3, hR3, transpose_mul, transpose_one_sub_smul_vecMulVec,
      ← mul_one_sub_smul_vecMulVec_apply, hDdef, hC]
    simp only [Matrix.mul_assoc]
  refine ⟨fun i q h1 h2 => ?_, fun i q h1 h2 => ?_, fun i q h1 h2 => ?_, fun k hk => ?_,
    fun k hk => ?_, fun k hk => ?_⟩
  · -- the array outside the stored vectors
    dsimp only
    rw [hC3, hB3 i q (fun h => h2 ⟨by omega, by omega⟩)]
    by_cases hij : (i : ℕ) < j
    · rw [ite_eq_right (show ¬ ((j : ℕ) ≤ i) by omega), hA1lt i q hij, hDrow i q hij,
        hwout q (by omega), mul_zero, sub_zero]
      exact ha' i q (fun h => h1 ⟨by omega, h.2⟩) (fun h => h2 ⟨by omega, h.2⟩)
    · rw [ite_eq_left (show (j : ℕ) ≤ i by omega), hA1dot i (by omega)]
      congr 1
      by_cases hqj : (q : ℕ) = j
      · rw [show q = j from Fin.ext hqj]
        exact hA1b i (by omega)
      · exact hA1a i q (by omega) (by omega)
  · -- the processed columns
    rw [hC3, hwout q h1, mul_zero, sub_zero]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with hqj | hqj
    · rw [hDcol i q hqj]
      exact hb' i q hqj h2
    · rw [show q = j from Fin.ext hqj]
      exact hDj i (by omega)
  · -- the processed rows
    rw [hC3]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with hij | hij
    · have hrow : D i ⬝ᵥ w = 0 := Finset.sum_eq_zero fun r _ => by
        change D i r * w r = 0
        by_cases hr : (r : ℕ) < j + 1
        · rw [hwout r hr, mul_zero]
        · rw [hDrow i r hij, hc' i r hij (by omega), zero_mul]
      rw [hrow, hDrow i q hij, hc' i q hij h2]
      ring
    · rw [← hA1dot i (by omega), ← hA1a i q (by omega) (by omega)]
      have hi : i = Fin.castLE hnm j := Fin.ext hij
      rw [hi]
      exact hred q (by omega)
  · -- the recorded `β`
    dsimp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hkj | hkj
    · have hkj' : k ≠ j := fun e => by rw [e] at hkj; omega
      rw [Function.update_of_ne hkj', hsvk k hkj]
      exact hdβ k hkj
    · rw [show k = j from Fin.ext hkj, Function.update_self, hsvj]
      exact hdich
  · -- the recorded `γ`
    dsimp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hkj | hkj
    · have hkj' : k ≠ j := fun e => by rw [e] at hkj; omega
      rw [Function.update_of_ne hkj', hsrk k hkj]
      exact hdγ k hkj
    · rw [show k = j from Fin.ext hkj, Function.update_self]
      exact hg
  · -- the `γ` still to come
    dsimp only
    have hkj' : k ≠ j := fun e => by rw [e] at hk; omega
    rw [Function.update_of_ne hkj']
    exact hγ0 k (by omega)

/-- One exact step of Algorithm 5.4.2 preserves the invariant. -/
private theorem bidiagInvariant_step (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n)
    (hI : bidiagInvariant hnm A j st) :
    bidiagInvariant hnm A ((j : ℕ) + 1) (Id.run (bidiagonalizationStep pure hnm st j)) := by
  obtain ⟨B, β, γ⟩ := st
  have hγj : γ j = 0 := hI.2.2.2.2.2 j le_rfl
  have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
  have hne := indexFrom_ne_nil hjm
  set x : Fin m → ℝ := fun i => B i j with hx
  obtain ⟨hv1, hvout, hdich, -, hmul⟩ := houseOn_spec (nodup_indexFrom m j) hne x
  rw [head_indexFrom hjm hne] at hv1 hmul
  simp only [bidiagonalizationStep, Id.run_bind]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom n j) hvout]
  generalize Id.run (houseOn pure (indexFrom m ↑j) x) = vβ at hv1 hvout hdich hmul ⊢
  obtain ⟨v, b⟩ := vβ
  dsimp only at hv1 hvout hdich hmul ⊢
  have hvout' : ∀ i : Fin m, (i : ℕ) < j → v i = 0 := fun i hi =>
    hvout i (by rw [mem_indexFrom]; omega)
  have hv1' : ∀ i : Fin m, (i : ℕ) = j → v i = 1 := fun i hi => by
    rw [show i = ⟨j, hjm⟩ from Fin.ext hi]
    exact hv1
  have hmul' : ∀ i : Fin m, (j : ℕ) < i →
      ((1 - b • vecMulVec v v) *ᵥ fun r => B r j) i = 0 := fun i hi => by
    change ((1 - b • vecMulVec v v) *ᵥ x) i = 0
    rw [hmul]
    have hi1 : i ≠ ⟨j, hjm⟩ := fun e => by
      have : (i : ℕ) = j := congrArg Fin.val e
      omega
    have hi2 : i ∈ indexFrom m j := by rw [mem_indexFrom]; omega
    simp [hi1, hi2]
  set B' : Matrix (Fin m) (Fin n) ℝ :=
    of fun i q => if q ∈ indexFrom n j then
      ((1 - b • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * B) i q else B i q with hB'
  set A1 : Matrix (Fin m) (Fin n) ℝ :=
    B'.updateCol j (fun i => if (j : ℕ) < i then v i else B' i j) with hA1def
  have hA1 : ∀ i q, A1 i q = if q = j ∧ (j : ℕ) < i then v i else
      if (j : ℕ) ≤ q then ((1 - b • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * B) i q
      else B i q := fun i q => by
    by_cases hq : q = j
    · subst hq
      by_cases hi : (q : ℕ) < i
      · simp only [hA1def, updateCol_self, hi, ↓reduceIte, and_self]
      · simp only [hA1def, updateCol_self, hi, ↓reduceIte, and_false, hB', of_apply,
          mem_indexFrom, le_refl]
    · simp only [hA1def, updateCol_ne hq, hq, false_and, ↓reduceIte, hB', of_apply,
        mem_indexFrom]
  by_cases hj3 : (j : ℕ) + 3 ≤ n
  · rw [ite_eq_left hj3]
    simp only [Id.run_bind, Id.run_pure]
    have hjn : (j : ℕ) + 1 < n := by omega
    have hne' := indexFrom_ne_nil (m := n) hjn
    obtain ⟨hw1, hwout, hgdich, -, hwmul⟩ :=
      houseOn_spec (nodup_indexFrom n ((j : ℕ) + 1)) hne' (A1 (Fin.castLE hnm j))
    rw [head_indexFrom hjn hne'] at hw1 hwmul
    rw [householderApplyRight_spec (nodup_indexFrom m j) (nodup_indexFrom n ((j : ℕ) + 1)) hwout]
    generalize Id.run (houseOn pure (indexFrom n (↑j + 1)) (A1 (Fin.castLE hnm j))) = wγ
      at hw1 hwout hgdich hwmul ⊢
    obtain ⟨w, g⟩ := wγ
    dsimp only at hw1 hwout hgdich hwmul ⊢
    have hwout' : ∀ q : Fin n, (q : ℕ) < j + 1 → w q = 0 := fun q hq =>
      hwout q (by rw [mem_indexFrom]; omega)
    set B3 : Matrix (Fin m) (Fin n) ℝ :=
      (of fun r c => if r ∈ indexFrom m j then
          (A1 * (1 - g • vecMulVec w w : Matrix (Fin n) (Fin n) ℝ)) r c
        else A1 r c).updateRow (Fin.castLE hnm j) (fun q => if (j : ℕ) + 1 < q then w q else
          (of fun r c => if r ∈ indexFrom m j then
              (A1 * (1 - g • vecMulVec w w : Matrix (Fin n) (Fin n) ℝ)) r c
            else A1 r c) (Fin.castLE hnm j) q) with hB3def
    have hsrv : storedRowVec hnm B3 j = w := funext fun q => by
      simp only [storedRowVec]
      by_cases hq : (q : ℕ) < j + 1
      · rw [ite_eq_left hq, hwout' q hq]
      · rw [ite_eq_right hq]
        by_cases hq' : (q : ℕ) = j + 1
        · rw [ite_eq_left hq', show q = ⟨(j : ℕ) + 1, hjn⟩ from Fin.ext hq', hw1]
        · rw [ite_eq_right hq', hB3def, updateRow_self, ite_eq_left (show (j : ℕ) + 1 < q by omega)]
    refine bidiagInvariant_step_core hnm A B β γ j hI v b hvout' hv1' hdich hmul' A1 hA1 w g B3
      hwout' (by rw [hsrv]; exact hgdich) (by rw [hsrv]) (fun q hq => ?_) (fun i q hiq => ?_)
    · have h1 := congrFun hwmul q
      rw [one_sub_smul_vecMulVec_mulVec_apply] at h1
      have hq1 : q ≠ ⟨(j : ℕ) + 1, hjn⟩ := fun e => by
        have : (q : ℕ) = j + 1 := congrArg Fin.val e
        omega
      have hq2 : q ∈ indexFrom n ((j : ℕ) + 1) := by rw [mem_indexFrom]; omega
      simp only [hq1, hq2, ↓reduceIte] at h1
      rw [dotProduct_comm]
      linear_combination h1
    · by_cases hi : i = Fin.castLE hnm j
      · subst hi
        have hq : ¬ ((j : ℕ) + 1 < (q : ℕ)) := fun h => hiq ⟨rfl, h⟩
        have hjj : (j : ℕ) ≤ (Fin.castLE hnm j : ℕ) := le_refl (j : ℕ)
        have hmem : Fin.castLE hnm j ∈ indexFrom m j := mem_indexFrom.2 hjj
        simp only [hB3def, updateRow_self, hq, ↓reduceIte, of_apply, hmem, hjj]
        exact mul_one_sub_smul_vecMulVec_apply g w A1 _ q
      · rw [hB3def, updateRow_ne hi, of_apply]
        by_cases hji : (j : ℕ) ≤ i
        · rw [ite_eq_left (mem_indexFrom.2 hji), ite_eq_left hji]
          exact mul_one_sub_smul_vecMulVec_apply g w A1 i q
        · rw [ite_eq_right (fun h => hji (mem_indexFrom.1 h)), ite_eq_right hji]
  · rw [ite_eq_right hj3]
    simp only [Id.run_pure]
    have hγ : γ = Function.update γ j 0 := by rw [← hγj, Function.update_eq_self]
    rw [hγ]
    refine bidiagInvariant_step_core hnm A B β γ j hI v b hvout' hv1' hdich hmul' A1 hA1 0 0 A1
      (fun _ _ => rfl) (Or.inl rfl) (by rw [zero_smul, zero_smul]) (fun q hq => ?_)
      (fun i q _ => ?_)
    · have := q.isLt
      omega
    · split_ifs <;> simp

/-- **Algorithm 5.4.2 computes a bidiagonalization** (exact arithmetic, `m ≥ n`): with
`(A', β, γ) = Id.run (algorithm_5_4_2 pure hnm A)`, the factored forms `U_B = U₁ ⋯ U_n` of the
column-stored vectors with the returned `β` and `V_B = V₁ ⋯ V_n` of the row-stored vectors with
the returned `γ` (convention 13; a step without a right reflector has `γ_j = 0`) satisfy
`U_Bᵀ A V_B = B` for the bidiagonal part `B` of `A'`, both orthogonal — "overwrites `A` with
`U_Bᵀ A V_B = B` where `B` is upper bidiagonal" — and every `β_j`, `γ_j` is `0` or `2/vᵀv`. -/
theorem algorithm_5_4_2_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsBidiagonalization A
        (factoredQ (Id.run (algorithm_5_4_2 pure hnm A)).2.1
          (Id.run (algorithm_5_4_2 pure hnm A)).1)
        (bidiagRightQ hnm (Id.run (algorithm_5_4_2 pure hnm A)).2.2
          (Id.run (algorithm_5_4_2 pure hnm A)).1)
        (bidiagonalPart (Id.run (algorithm_5_4_2 pure hnm A)).1) ∧
      (∀ j, (Id.run (algorithm_5_4_2 pure hnm A)).2.1 j = 0 ∨
        (Id.run (algorithm_5_4_2 pure hnm A)).2.1 j *
          (storedHouseholderVec (Id.run (algorithm_5_4_2 pure hnm A)).1 j ⬝ᵥ
            storedHouseholderVec (Id.run (algorithm_5_4_2 pure hnm A)).1 j) = 2) ∧
      ∀ j, (Id.run (algorithm_5_4_2 pure hnm A)).2.2 j = 0 ∨
        (Id.run (algorithm_5_4_2 pure hnm A)).2.2 j *
          (storedRowVec hnm (Id.run (algorithm_5_4_2 pure hnm A)).1 j ⬝ᵥ
            storedRowVec hnm (Id.run (algorithm_5_4_2 pure hnm A)).1 j) = 2 := by
  set f := fun st j => Id.run (bidiagonalizationStep (m := m) (n := n) pure hnm st j) with hf
  have hprog : Id.run (algorithm_5_4_2 pure hnm A) = (List.finRange n).foldl f (A, 0, 0) := by
    rw [algorithm_5_4_2, List.idRun_foldlM]
  have hall : ∀ j ≤ n, bidiagInvariant hnm A j (((List.finRange n).take j).foldl f (A, 0, 0)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i q _ _ => ?_, fun i q hq => absurd hq (Nat.not_lt_zero _),
        fun i q hi => absurd hi (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _),
        fun k hk => absurd hk (Nat.not_lt_zero _), fun k _ => rfl⟩
      simp [bidiagLeftPrefix, bidiagRightPrefix]
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h := bidiagInvariant_step hnm A _ ⟨j, by omega⟩ (ih (by omega))
      simpa [hf] using h
  have hn := hall n le_rfl
  rw [List.take_of_length_le (by simp), ← hprog] at hn
  generalize Id.run (algorithm_5_4_2 pure hnm A) = st at hn ⊢
  obtain ⟨B, β, γ⟩ := st
  obtain ⟨ha, hb, hc, hdβ, hdγ, -⟩ := hn
  have hL : bidiagLeftPrefix n (B, β, γ) = factoredQ β B := by
    rw [bidiagLeftPrefix, List.take_of_length_le (by simp), factoredQ, storedReflectors,
      List.ofFn_eq_map]
  have hR : bidiagRightPrefix hnm n (B, β, γ) = bidiagRightQ hnm γ B := by
    rw [bidiagRightPrefix, List.take_of_length_le (by simp), bidiagRightQ, List.ofFn_eq_map]
  rw [hL, hR] at ha hb hc
  have hdβ' : ∀ j : Fin n, β j = 0 ∨
      β j * (storedHouseholderVec B j ⬝ᵥ storedHouseholderVec B j) = 2 := fun j => hdβ j j.isLt
  have hdγ' : ∀ j : Fin n, γ j = 0 ∨
      γ j * (storedRowVec hnm B j ⬝ᵥ storedRowVec hnm B j) = 2 := fun j => hdγ j j.isLt
  have hU : factoredQ β B ∈ orthogonalGroup (Fin m) ℝ := by
    refine householderProduct_mem_orthogonalGroup fun p hp => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
    exact hdβ' k
  have hV : bidiagRightQ hnm γ B ∈ orthogonalGroup (Fin n) ℝ := by
    refine householderProduct_mem_orthogonalGroup fun p hp => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
    exact hdγ' k
  have hconj : (factoredQ β B)ᵀ * A * bidiagRightQ hnm γ B = bidiagonalPart B := by
    ext i q
    rw [bidiagonalPart, of_apply]
    split_ifs with hiq
    · exact (ha i q (fun h => by omega) (fun h => by omega)).symm
    · rcases lt_or_gt_of_ne (show (q : ℕ) ≠ i from fun h => hiq (Or.inl h)) with h | h
      · exact hb i q q.isLt h
      · exact hc i q (by omega) (by omega)
  refine ⟨⟨hU, hV, ?_, fun i q h1 h2 => ?_⟩, hdβ', hdγ'⟩
  · rw [conjTranspose_eq_transpose_of_trivial]
    exact hconj
  · rw [bidiagonalPart, of_apply, ite_eq_right (show ¬ ((q : ℕ) = i ∨ (q : ℕ) = i + 1) by omega)]

end BidiagonalizationSpec


/-! ### §5.4.9 `R`-bidiagonalization -/

section RBidiagonalization

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **§5.4.9, `R`-bidiagonalization** (unnumbered): "first compute the QR factorization
`QᵀA = [R₁; 0]` and then apply Algorithm 5.4.2 to `R₁`": Algorithm 5.2.1 on `A`, then
Algorithm 5.4.2 on the square top block `R₁ = R(1:n, 1:n)` of its triangular factor. Returns both
programs' arrays and reflector scalars (`(A', β)` of Algorithm 5.2.1, `(R₁', β_R, γ_R)` of
Algorithm 5.4.2; convention 13), from which `U_B = Q diag(U_R, I_{m-n})` and `V_B` are read. -/
noncomputable def rBidiagonalization (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ×
      (Fin n → ℝ)) := do
  let QR ← algorithm_5_2_1 rnd A
  let BR ← algorithm_5_4_2 rnd le_rfl (firstRows (upperPart QR.1) hnm)
  pure (QR.1, QR.2, BR.1, BR.2.1, BR.2.2)

end RBidiagonalization

/-- **`R`-bidiagonalization computes a bidiagonalization** (§5.4.9, exact arithmetic): with the
factored forms `Q` of Algorithm 5.2.1 and `U_R`, `V_B` of Algorithm 5.4.2 on `R₁`,
`U_B = Q diag(U_R, I_{m-n})` and `V_B` bidiagonalize `A` to `[B₁; 0]`, `B₁` the bidiagonal part of
Algorithm 5.4.2's output array (`Matrix.IsBidiagonalization.of_isQR`). -/
theorem rBidiagonalization_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsBidiagonalization A
      (factoredQ (Id.run (rBidiagonalization pure hnm A)).2.1
          (Id.run (rBidiagonalization pure hnm A)).1 *
        padOne (factoredQ (Id.run (rBidiagonalization pure hnm A)).2.2.2.1
          (Id.run (rBidiagonalization pure hnm A)).2.2.1) hnm)
      (bidiagRightQ le_rfl (Id.run (rBidiagonalization pure hnm A)).2.2.2.2
        (Id.run (rBidiagonalization pure hnm A)).2.2.1)
      (padRows (bidiagonalPart (Id.run (rBidiagonalization pure hnm A)).2.2.1) hnm) :=
  IsBidiagonalization.of_isQR hnm (algorithm_5_2_1_spec hnm A).1
    (algorithm_5_4_2_spec le_rfl _).1


/-! ### §5.4.5 The zero-chasing update in exact arithmetic -/

section RevealUpdateSpec

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- `givensRevealUpdate` is the fold of `givensRevealStep` from `(R, v, I, I)`. -/
theorem givensRevealUpdate_eq_foldlM {k : ℕ} (R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (v : Fin (k + 1) → ℝ) :
    givensRevealUpdate rnd R v = (List.finRange k).foldlM (givensRevealStep rnd) (R, v, 1, 1) :=
  rfl

end Programs

/-- **Exact semantics of the vector rotation**: `givensRotateVec` computes `G(i, k, θ)ᵀ x`. -/
theorem givensRotateVec_pure {N : ℕ} {i i' : Fin N} (hii' : i ≠ i') (c s : ℝ) (x : Fin N → ℝ) :
    Id.run (givensRotateVec pure i i' c s x) = (givensRotation i i' c s)ᵀ *ᵥ x := by
  ext t
  rw [givensRotation_transpose_mulVec_apply hii']
  simp only [givensRotateVec, Id.run_bind, Id.run_pure]
  by_cases hti' : t = i'
  · subst hti'
    rw [Function.update_self, ite_eq_right (Ne.symm hii'), ite_eq_left rfl]
  · rw [Function.update_of_ne hti']
    by_cases hti : t = i
    · subst hti
      rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne hti, ite_eq_right hti, ite_eq_right hti']

/-- The invariant of the zero-chasing update after `j` steps from `(R₀, v₀, I, I)`: `Z_G`, `Q_G`
orthogonal, `R = Q_Gᵀ R₀ Z_G` upper triangular, `v = Z_Gᵀ v₀` with `v_p = 0` for `p < j`. -/
private def revealInvariant {k : ℕ} (R₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (v₀ : Fin (k + 1) → ℝ) (j : ℕ)
    (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin (k + 1) → ℝ) ×
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Prop :=
  st.2.2.1 ∈ orthogonalGroup (Fin (k + 1)) ℝ ∧ st.2.2.2 ∈ orthogonalGroup (Fin (k + 1)) ℝ ∧
    st.1 = st.2.2.2ᵀ * R₀ * st.2.2.1 ∧ st.1.IsUpperTriangular ∧ st.2.1 = st.2.2.1ᵀ *ᵥ v₀ ∧
    ∀ p : Fin (k + 1), (p : ℕ) < j → st.2.1 p = 0

/-- One exact step of the zero-chasing update preserves the invariant. -/
private theorem revealInvariant_step {k : ℕ} (R₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (v₀ : Fin (k + 1) → ℝ)
    (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin (k + 1) → ℝ) ×
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (j : Fin k)
    (hI : revealInvariant R₀ v₀ j st) :
    revealInvariant R₀ v₀ ((j : ℕ) + 1) (Id.run (givensRevealStep pure st j)) := by
  obtain ⟨R, V, Z, Q⟩ := st
  obtain ⟨hZ, hQ, hRe, hRu, hVe, hV0⟩ := hI
  dsimp only at hZ hQ hRe hRu hVe hV0
  have hii' : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne
  have hiv : (j.castSucc : ℕ) = j := rfl
  have hi'v : (j.succ : ℕ) = j + 1 := rfl
  obtain ⟨hcs, hz, -⟩ := algorithm_5_1_3_spec (V j.succ) (V j.castSucc)
  simp only [givensRevealStep, Id.run_bind, Id.run_pure]
  generalize Id.run (algorithm_5_1_3 pure (V j.succ) (V j.castSucc)) = cs at hcs hz ⊢
  obtain ⟨c, s⟩ := cs
  dsimp only at hcs hz ⊢
  have hnd : ((List.finRange (k + 1)).filter fun r : Fin (k + 1) => (r : ℕ) ≤ (j.succ : ℕ)).Nodup :=
    (List.nodup_finRange _).filter _
  rw [givensRotateVec_pure hii', givensApplyRight_spec hii' c (-s) hnd,
    givensApplyRight_spec_of_forall_mem hii' c (-s) (List.nodup_finRange _) List.mem_finRange]
  obtain ⟨G, hG⟩ : ∃ G, G = givensRotation j.castSucc j.succ c (-s) := ⟨_, rfl⟩
  rw [← hG]
  have hRz : ∀ p q : Fin (k + 1), q < p → R p q = 0 := fun p q h => hRu h
  -- the rows below `j + 1` are untouched by the column rotation, so it acts on all rows
  have hlow : ∀ p q : Fin (k + 1), q < p → ¬ (p = j.succ ∧ q = j.castSucc) →
      (R * G) p q = 0 := by
    intro p q hqp hpq
    rw [hG, mul_givensRotation_apply hii']
    by_cases hq : q = j.castSucc
    · have hp : j.succ < p := by
        rw [Fin.lt_def] at hqp ⊢
        have hp' : p ≠ j.succ := fun e => hpq ⟨e, hq⟩
        have : (p : ℕ) ≠ j + 1 := fun e => hp' (Fin.ext e)
        rw [hq] at hqp
        change (j : ℕ) < p at hqp
        change (j : ℕ) + 1 < p
        omega
      rw [ite_eq_left hq, hRz p _ (lt_trans Fin.castSucc_lt_succ hp), hRz p _ hp]
      ring
    · rw [ite_eq_right hq]
      by_cases hq' : q = j.succ
      · rw [ite_eq_left hq']
        rw [hq'] at hqp
        rw [hRz p _ (lt_trans Fin.castSucc_lt_succ hqp), hRz p _ hqp]
        ring
      · rw [ite_eq_right hq', hRz p q hqp]
  have hR1 : (of fun r q =>
      if r ∈ (List.finRange (k + 1)).filter (fun r : Fin (k + 1) => (r : ℕ) ≤ (j.succ : ℕ))
      then (R * G) r q else R r q) = R * G := by
    ext r q
    rw [of_apply]
    split_ifs with hr
    · rfl
    · simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, not_le] at hr
      have h1 : R r j.castSucc = 0 := hRz _ _ (by rw [Fin.lt_def]; change (j : ℕ) < r; omega)
      have h2 : R r j.succ = 0 := hRz _ _ (by rw [Fin.lt_def]; exact hr)
      rw [hG, mul_givensRotation_apply hii']
      split_ifs with hq hq'
      · rw [hq, h1, h2]; ring
      · rw [hq', h1, h2]; ring
      · rfl
  rw [hR1]
  obtain ⟨hcs₂, hz₂, -⟩ := algorithm_5_1_3_spec ((R * G) j.castSucc j.castSucc)
    ((R * G) j.succ j.castSucc)
  generalize Id.run (algorithm_5_1_3 pure ((R * G) j.castSucc j.castSucc)
    ((R * G) j.succ j.castSucc)) = cs₂ at hcs₂ hz₂ ⊢
  obtain ⟨c₂, s₂⟩ := cs₂
  dsimp only at hcs₂ hz₂ ⊢
  rw [givensApplyLeft_spec hii' c₂ s₂ (nodup_indexFrom _ _),
    givensApplyRight_spec_of_forall_mem hii' c₂ s₂ (List.nodup_finRange _) List.mem_finRange]
  obtain ⟨H, hH⟩ : ∃ H, H = givensRotation j.castSucc j.succ c₂ s₂ := ⟨_, rfl⟩
  rw [← hH]
  -- the left rotation does not touch the columns before `j`
  have hR2 : (of fun r q => if q ∈ indexFrom (k + 1) (j.castSucc : ℕ) then (Hᵀ * (R * G)) r q
      else (R * G) r q) = Hᵀ * (R * G) := by
    ext r q
    rw [of_apply]
    split_ifs with hq
    · rfl
    · rw [mem_indexFrom, not_le] at hq
      have h1 : (R * G) j.castSucc q = 0 :=
        hlow _ _ (by rw [Fin.lt_def]; exact hq) (fun h => hii' h.1)
      have h2 : (R * G) j.succ q = 0 :=
        hlow _ _ (by rw [Fin.lt_def]; change (q : ℕ) < j + 1; omega)
          (fun h => by have := congrArg Fin.val h.2; change (q : ℕ) = j at this; omega)
      rw [hH, givensRotation_transpose_mul_apply hii']
      split_ifs with hr hr'
      · rw [hr, h1, h2]; ring
      · rw [hr', h1, h2]; ring
      · rfl
  rw [hR2]
  refine ⟨mul_mem hZ (hG ▸ givensRotation_mem_orthogonalGroup hii' (by rw [neg_sq]; exact hcs)),
    mul_mem hQ (hH ▸ givensRotation_mem_orthogonalGroup hii' hcs₂), ?_, ?_, ?_, ?_⟩
  · rw [transpose_mul, hRe]
    simp only [Matrix.mul_assoc]
  · intro p q hqp
    change q < p at hqp
    dsimp only
    rw [hH, givensRotation_transpose_mul_apply hii']
    by_cases hp : p = j.castSucc
    · have hq : (q : ℕ) < j := by rw [Fin.lt_def, hp] at hqp; exact hqp
      rw [ite_eq_left hp, hlow _ _ (by rw [Fin.lt_def]; exact hq) (fun h => hii' h.1),
        hlow _ _ (by rw [Fin.lt_def]; change (q : ℕ) < j + 1; omega)
          (fun h => by have := congrArg Fin.val h.2; change (q : ℕ) = j at this; omega)]
      ring
    · rw [ite_eq_right hp]
      by_cases hp' : p = j.succ
      · rw [ite_eq_left hp']
        have hq : (q : ℕ) ≤ j := by
          rw [Fin.lt_def, hp'] at hqp; change (q : ℕ) < j + 1 at hqp; omega
        by_cases hqj : (q : ℕ) = j
        · have hq' : q = j.castSucc := Fin.ext hqj
          rw [hq']
          linear_combination hz₂
        · rw [hlow _ _ (by rw [Fin.lt_def]; change (q : ℕ) < j; omega) (fun h => hii' h.1),
            hlow _ _ (by rw [Fin.lt_def]; change (q : ℕ) < j + 1; omega)
              (fun h => by have := congrArg Fin.val h.2; exact hqj this)]
          ring
      · rw [ite_eq_right hp']
        exact hlow p q hqp (fun h => hp' h.1)
  · rw [hVe, mulVec_mulVec, transpose_mul]
  · intro p hp
    dsimp only
    rw [hG, givensRotation_transpose_mulVec_apply hii']
    by_cases hpi : p = j.castSucc
    · rw [ite_eq_left hpi]
      linear_combination hz
    · rw [ite_eq_right hpi]
      have hpi' : p ≠ j.succ := fun e => by
        have := congrArg Fin.val e; change (p : ℕ) = j + 1 at this; omega
      rw [ite_eq_right hpi']
      exact hV0 p (by
        have : (p : ℕ) ≠ j := fun e => hpi (Fin.ext e)
        omega)

/-- **§5.4.5, the zero-chasing update in exact arithmetic**: for `R` upper triangular and a unit
vector `v`, with `(R_new, v_new, Z_G, Q_G) = Id.run (givensRevealUpdate pure R v)`: `Z_G` and `Q_G`
are orthogonal, `R_new = Q_Gᵀ R Z_G` is upper triangular, `v_new = Z_Gᵀ v = ±e_n`, hence (the
book's display) `‖R_new e_n‖₂ = ‖R v‖₂`, and a factorization `A Z = Q R` is updated to
`A Z_new = Q_new R_new` with `Z_new = Z Z_G`, `Q_new = Q Q_G`. -/
theorem givensRevealUpdate_spec {k : ℕ} {R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hR : R.IsUpperTriangular) {v : Fin (k + 1) → ℝ}
    (hv : ‖(toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖ = 1) :
    (Id.run (givensRevealUpdate pure R v)).2.2.1 ∈ orthogonalGroup (Fin (k + 1)) ℝ ∧
      (Id.run (givensRevealUpdate pure R v)).2.2.2 ∈ orthogonalGroup (Fin (k + 1)) ℝ ∧
      (Id.run (givensRevealUpdate pure R v)).1 =
        (Id.run (givensRevealUpdate pure R v)).2.2.2ᵀ * R *
          (Id.run (givensRevealUpdate pure R v)).2.2.1 ∧
      (Id.run (givensRevealUpdate pure R v)).1.IsUpperTriangular ∧
      (Id.run (givensRevealUpdate pure R v)).2.1 =
        (Id.run (givensRevealUpdate pure R v)).2.2.1ᵀ *ᵥ v ∧
      (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        (Id.run (givensRevealUpdate pure R v)).2.1 = σ • Pi.single (Fin.last k) 1) ∧
      ‖(toLp 2 ((Id.run (givensRevealUpdate pure R v)).1.col (Fin.last k)) :
          EuclideanSpace ℝ (Fin (k + 1)))‖ =
        ‖(toLp 2 (R *ᵥ v) : EuclideanSpace ℝ (Fin (k + 1)))‖ ∧
      ∀ (A : Matrix (Fin m) (Fin (k + 1)) ℝ) (Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
        (Q : Matrix (Fin m) (Fin (k + 1)) ℝ), A * Z = Q * R →
        A * (Z * (Id.run (givensRevealUpdate pure R v)).2.2.1) =
          Q * (Id.run (givensRevealUpdate pure R v)).2.2.2 *
            (Id.run (givensRevealUpdate pure R v)).1 := by
  set f := fun st j => Id.run (givensRevealStep (k := k) pure st j) with hf
  have hprog : Id.run (givensRevealUpdate pure R v) = (List.finRange k).foldl f (R, v, 1, 1) := by
    rw [givensRevealUpdate_eq_foldlM, List.idRun_foldlM]
  have hall : ∀ j ≤ k, revealInvariant R v j (((List.finRange k).take j).foldl f (R, v, 1, 1)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨one_mem _, one_mem _, ?_, hR, ?_, fun p hp => absurd hp (Nat.not_lt_zero _)⟩
      · simp
      · simp
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h := revealInvariant_step R v _ ⟨j, by omega⟩ (ih (by omega))
      simpa [hf] using h
  have hn := hall k le_rfl
  rw [List.take_of_length_le (by simp), ← hprog] at hn
  generalize Id.run (givensRevealUpdate pure R v) = out at hn ⊢
  obtain ⟨R', V', Z', Q'⟩ := out
  obtain ⟨hZ, hQ, hRe, hRu, hVe, hV0⟩ := hn
  dsimp only at hZ hQ hRe hRu hVe hV0 ⊢
  have hQQ : Q' * Q'ᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hQ
  have hZZ : Z' * Z'ᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hZ
  -- `v_new` is `±e_n`
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = V' (Fin.last k) := ⟨_, rfl⟩
  have hVs : V' = σ • Pi.single (Fin.last k) 1 := by
    ext p
    by_cases hp : p = Fin.last k
    · rw [hp, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hσ]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hp, smul_zero]
      exact hV0 p (by
        have h1 := p.isLt
        have h2 : (p : ℕ) ≠ k := fun e => hp (Fin.ext e)
        omega)
  have hσ2 : σ ^ 2 = 1 := by
    have h1 : V' ⬝ᵥ V' = v ⬝ᵥ v := by
      rw [hVe, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, mulVec_mulVec, hZZ,
        one_mulVec]
    rw [dotProduct_self_eq_norm_sq v, hv, hVs] at h1
    simpa [dotProduct, Pi.single_apply, sq] using h1
  have hσpm : σ = 1 ∨ σ = -1 := by
    have h : (σ - 1) * (σ + 1) = 0 := by linear_combination hσ2
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  -- `R v = σ Q_G R_new e_n`
  have hcol : R'.col (Fin.last k) = R' *ᵥ Pi.single (Fin.last k) 1 := by
    ext i
    simp
  have hRv : R *ᵥ v = σ • (Q' *ᵥ R'.col (Fin.last k)) := by
    have hv' : v = Z' *ᵥ V' := by
      rw [hVe, mulVec_mulVec, hZZ, one_mulVec]
    rw [hcol, hv', hVs, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, hRe,
      ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  refine ⟨hZ, hQ, hRe, hRu, hVe, ⟨σ, hσpm, hVs⟩, ?_, fun A Z Q hAZ => ?_⟩
  · rw [hRv, toLp_smul, norm_smul, norm_toLp_mulVec_of_mem_orthogonalGroup hQ, Real.norm_eq_abs]
    rcases hσpm with h | h <;> simp [h]
  · rw [hRe, ← Matrix.mul_assoc, hAZ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q' Q'ᵀ, hQQ, Matrix.one_mul]

end RevealUpdateSpec

/-! ### §5.4.6 The UTV framework -/

section UTV

open scoped Matrix.Norms.L2Operator

open Chapter02 (sigmaMin subspaceDist)

/-- `σ_min` of a square block is its last sorted singular value. -/
private theorem sigmaMin_square {k : ℕ} (T : Matrix (Fin k) (Fin k) ℝ) :
    sigmaMin T = T.sortedSingularValues (k - 1) := by
  rw [sigmaMin, min_self]

/-- **(5.4.10)** (Stewart 1993): "suppose `σ_k(A) > σ_{k+1}(A)` and `S` is the subspace spanned by
`A`'s right singular vectors `v_{k+1}, …, v_n`" … "if `Uᵀ A V = R = [R₁₁ R₁₂; 0 R₂₂]` and
`V = [V₁ | V₂]` is partitioned conformably, then
`dist(ran(V₂), S) ≤ ‖R₁₂‖₂ / ((1 - ρ_R²) σ_min(R₁₁))` where `ρ_R = ‖R₂₂‖₂ / σ_min(R₁₁)` is
assumed to be less than 1". `R₁₁` is `k × k`; `S` is spanned by the last `n - k` columns of the
right factor `Z` of an SVD `A = W Σ Zᵀ`, and the bound holds for every SVD, so the separation
`σ_k(A) > σ_{k+1}(A)` (which makes `S` unique) is not needed; `σ_min(R₁₁) > 0` is implicit in the
book's `ρ_R`. `dist` is `Chapter02.subspaceDist`; backbone `Matrix.gap_le_of_urv` on the bundle
`Matrix.IsURV`. -/
theorem equation_5_4_10 {A R : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (hR : Uᵀ * A * V = R)
    (hRtri : ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → R i j = 0)
    {W : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {Z : Matrix (Fin n) (Fin n) ℝ} (hA : IsSVD A W σ Z) {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hσ : 0 < sigmaMin (R.submatrix (Fin.castLE hkm) (Fin.castLE hkn)))
    (hρ : ‖R.submatrix (tailIdx hkm) (tailIdx hkn)‖ /
      sigmaMin (R.submatrix (Fin.castLE hkm) (Fin.castLE hkn)) < 1) :
    subspaceDist (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx hkn))))
        (LinearMap.range (toEuclideanLin (Z.submatrix id (tailIdx hkn)))) ≤
      ‖R.submatrix (Fin.castLE hkm) (tailIdx hkn)‖ /
        ((1 - (‖R.submatrix (tailIdx hkm) (tailIdx hkn)‖ /
            sigmaMin (R.submatrix (Fin.castLE hkm) (Fin.castLE hkn))) ^ 2) *
          sigmaMin (R.submatrix (Fin.castLE hkm) (Fin.castLE hkn))) := by
  rw [sigmaMin_square] at hσ hρ ⊢
  exact gap_le_of_urv
    ⟨hU, hV, by rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial], hRtri⟩
    hA hkm hkn ((div_lt_one hσ).1 hρ)

/-- **(5.4.11)** (Stewart 1993): "in the ULV setting we have `Uᵀ A V = L = [L₁₁ 0; L₂₁ L₂₂]`. If
`V = [V₁ | V₂]` is partitioned conformably, then
`dist(ran(V₂), S) ≤ ρ_L ‖L₁₂‖₂ / ((1 - ρ_L²) σ_min(L₁₁))` where `ρ_L = ‖L₂₂‖₂ / σ_min(L₁₁)` is also
assumed to be less than 1", with the printed `L₁₂` (a zero block) read as `L₂₁`. Setting as in
`equation_5_4_10`; backbone `Matrix.gap_le_of_ulv` on the bundle `Matrix.IsULV`. -/
theorem equation_5_4_11 {A L : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (hL : Uᵀ * A * V = L)
    (hLtri : ∀ (i : Fin m) (j : Fin n), (i : ℕ) < j → L i j = 0)
    {W : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {Z : Matrix (Fin n) (Fin n) ℝ} (hA : IsSVD A W σ Z) {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hσ : 0 < sigmaMin (L.submatrix (Fin.castLE hkm) (Fin.castLE hkn)))
    (hρ : ‖L.submatrix (tailIdx hkm) (tailIdx hkn)‖ /
      sigmaMin (L.submatrix (Fin.castLE hkm) (Fin.castLE hkn)) < 1) :
    subspaceDist (LinearMap.range (toEuclideanLin (V.submatrix id (tailIdx hkn))))
        (LinearMap.range (toEuclideanLin (Z.submatrix id (tailIdx hkn)))) ≤
      ‖L.submatrix (tailIdx hkm) (tailIdx hkn)‖ /
          sigmaMin (L.submatrix (Fin.castLE hkm) (Fin.castLE hkn)) *
          ‖L.submatrix (tailIdx hkm) (Fin.castLE hkn)‖ /
        ((1 - (‖L.submatrix (tailIdx hkm) (tailIdx hkn)‖ /
            sigmaMin (L.submatrix (Fin.castLE hkm) (Fin.castLE hkn))) ^ 2) *
          sigmaMin (L.submatrix (Fin.castLE hkm) (Fin.castLE hkn))) := by
  rw [sigmaMin_square] at hσ hρ ⊢
  exact gap_le_of_ulv
    ⟨hU, hV, by rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial], hLtri⟩
    hA hkm hkn ((div_lt_one hσ).1 hρ)

end UTV

end GolubVanLoan.Chapter05
