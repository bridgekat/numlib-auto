import Numlib.Eigen.QRAlgorithm
import Numlib.Eigen.RayleighQuotientIteration
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import NumlibSurface.GolubVanLoan.Chapter08.Section02

/-!
# Golub–Van Loan §8.3: the symmetric QR algorithm

Surface file for [golub2013matrix] §8.3: the tridiagonal decomposition (8.3.1) and the symmetric
Householder update, unreduced tridiagonal matrices and the splitting of the spectrum, the facts of
§8.3.3 about the QR iteration on tridiagonal matrices (preservation of form, shifts, perfect
shifts), the Wilkinson shift (8.3.3), the explicit shifted iteration (8.3.2), the Rayleigh-quotient
connection (§8.3.6) and orthogonal iteration with Ritz acceleration ((8.3.6), §8.3.7).

## Conventions

Tridiagonal matrices are stored as full `Matrix (Fin n) (Fin n) ℝ` (`Matrix.IsTridiagonal`);
"unreduced" is `IsUnreducedTridiagonal`, chapter 7's `Matrix.IsUnreducedUpperHessenberg` together
with tridiagonality. The explicit shifted step is the backbone's `Matrix.shiftedQrStep` (canonical
`Matrix.qrQ`/`Matrix.qrR`).

The numbered algorithms (8.3.1–8.3.3) call chapter 5's `house`/`givens` helpers and the Theorems
8.3.1–8.3.2 restate chapter 7's Krylov-matrix and implicit-Q theorems; they are planned in this
group and wait for those chapters' surfaces.

## Readings

The Wilkinson shift (8.3.3) needs `sign(0) = 1`. The "preservation of form" fact of §8.3.3 holds
for every QR factorization only when `T` is nonsingular (for singular `T` the orthogonal factor is
not unique: `T = 0 = Q · 0`); the node assumes it.

## Not formalized

Wilkinson's cubic convergence of the shifted QR iteration (quoted), Stewart's rate for Ritz
acceleration (quoted), storage and flop counts.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### §8.3.1 Reduction to tridiagonal form -/

/-- **(8.3.1), the tridiagonal decomposition.** For symmetric `A` there is an orthogonal `Q` with
`Qᵀ A Q` symmetric tridiagonal, and `Q` may be taken with first column `e₁`. -/
theorem equation_8_3_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, (Qᵀ * A * Q).IsSymm ∧ (Qᵀ * A * Q).IsTridiagonal ∧
      ∀ h : 0 < n, Q *ᵥ Pi.single ⟨0, h⟩ 1 = Pi.single ⟨0, h⟩ 1 := by
  have hsymm : ∀ Q : Matrix (Fin n) (Fin n) ℝ, (Qᵀ * A * Q).IsSymm := fun Q => by
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hA))
  rcases n with _ | M
  · exact ⟨1, one_mem _, hsymm 1, fun i j _ => Fin.elim0 i, fun h => absurd h (lt_irrefl 0)⟩
  · refine ⟨hessenbergQ A, hessenbergQ_mem_orthogonalGroup A, hsymm _, ?_, fun h => ?_⟩
    · have h := isTridiagonal_hessenbergReduce_of_isHermitian (A := A) (isHermitian_iff_isSymm.2 hA)
      rwa [hessenbergReduce_eq_conj, conjTranspose_eq_transpose_of_trivial] at h
    · rw [mulVec_single_one]
      ext i
      rw [col_apply, show (⟨0, h⟩ : Fin (M + 1)) = 0 from rfl, hessenbergQ_apply_zero A i]
      by_cases hi : i = 0 <;> simp [hi, one_apply]

/-- **§8.3.1, the symmetric Householder update.** For symmetric `B`, `P = I - β v vᵀ`,
`p = β B v` and `w = p - (β pᵀv / 2) v`: `P B P = B - v wᵀ - w vᵀ`. -/
theorem householder_conj_eq_sub_rankTwo {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm)
    (v : Fin n → ℝ) (β : ℝ) :
    let p := β • (B *ᵥ v)
    let w := p - ((β * (v ⬝ᵥ p)) / 2) • v
    (1 - β • vecMulVec v v) * B * (1 - β • vecMulVec v v) =
      B - vecMulVec v w - vecMulVec w v := by
  intro p w
  have hB' : Bᴴ = B := by rw [conjTranspose_eq_transpose_of_trivial]; exact hB
  have h := conj_one_sub_smul_vecMulVec_eq_sub (R := ℝ) two_ne_zero hB' v (β := β)
    (star_trivial β) (p := p) (w := w) rfl (by simp [w])
  simpa using h

/-- **§8.3.1, "unreduced"**: a tridiagonal `T` is unreduced when no subdiagonal entry vanishes. -/
def IsUnreducedTridiagonal (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  T.IsTridiagonal ∧ T.IsUnreducedUpperHessenberg

/-- **§8.3.1, splitting.** If `T` is tridiagonal of order `(k + 1) + (l + 1)` and
`t_{k+1,k} = t_{k,k+1} = 0` (0-based at `k`, `k + 1`), then `T = diag(T₁, T₂)` with
`T₁ = T(1:k+1, 1:k+1)`, `T₂ = T(k+2:n, k+2:n)`, and `λ(T) = λ(T₁) ∪ λ(T₂)` with multiplicity. -/
theorem tridiagonal_spectrum_split {k l : ℕ}
    {T : Matrix (Fin (k + 1 + (l + 1))) (Fin (k + 1 + (l + 1))) ℝ} (hT : T.IsTridiagonal)
    (h₁ : T (Fin.natAdd (k + 1) 0) (Fin.castAdd (l + 1) (Fin.last k)) = 0)
    (h₂ : T (Fin.castAdd (l + 1) (Fin.last k)) (Fin.natAdd (k + 1) 0) = 0) :
    T.submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks (T.submatrix (Fin.castAdd (l + 1)) (Fin.castAdd (l + 1))) 0 0
          (T.submatrix (Fin.natAdd (k + 1)) (Fin.natAdd (k + 1))) ∧
      T.charpoly = (T.submatrix (Fin.castAdd (l + 1)) (Fin.castAdd (l + 1))).charpoly *
        (T.submatrix (Fin.natAdd (k + 1)) (Fin.natAdd (k + 1))).charpoly := by
  have hblock : T.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (T.submatrix (Fin.castAdd (l + 1)) (Fin.castAdd (l + 1))) 0 0
        (T.submatrix (Fin.natAdd (k + 1)) (Fin.natAdd (k + 1))) := by
    ext (i | i) (j | j)
    · rfl
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        fromBlocks_apply₁₂, Matrix.zero_apply]
      by_cases hij : (i : ℕ) = k ∧ (j : ℕ) = 0
      · have hi : i = Fin.last k := Fin.ext hij.1
        have hj : j = 0 := Fin.ext hij.2
        rw [hi, hj]; exact h₂
      · refine hT _ _ (Or.inr ⟨⟨i + 1, by omega⟩, ?_, ?_⟩)
        · simp [Fin.lt_def]
        · simp only [Fin.lt_def, Fin.val_natAdd]; omega
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        fromBlocks_apply₂₁, Matrix.zero_apply]
      by_cases hij : (i : ℕ) = 0 ∧ (j : ℕ) = k
      · have hi : i = 0 := Fin.ext hij.1
        have hj : j = Fin.last k := Fin.ext hij.2
        rw [hi, hj]; exact h₁
      · refine hT _ _ (Or.inl ⟨⟨j + 1, by omega⟩, ?_, ?_⟩)
        · simp [Fin.lt_def]
        · simp only [Fin.lt_def, Fin.val_natAdd]; omega
    · rfl
  refine ⟨hblock, ?_⟩
  rw [← charpoly_fromBlocks_zero₁₂, ← hblock]
  exact (charpoly_reindex finSumFinEquiv.symm T).symm

/-! ### §8.3.3 The QR iteration and tridiagonal matrices -/

/-- **§8.3.3, preservation of form.** If `T` is symmetric tridiagonal and `T = Q R` with `Q`
orthogonal and `R` upper triangular — `T` nonsingular, or `(Q, R)` the Givens QR
`Matrix.hessenbergGivensQR T` (for singular `T` and an arbitrary QR the claim is false,
`T = 0 = Q · 0`) — then `Q` is upper Hessenberg (lower bandwidth `1`), `R` has upper bandwidth `2`,
and `T₊ = R Q = Qᵀ T Q` is symmetric tridiagonal. -/
theorem qr_tridiagonal_preservation {T Q R : Matrix (Fin n) (Fin n) ℝ} (hTs : T.IsSymm)
    (hT : T.IsTridiagonal) (hcase : IsUnit T.det ∨ (Q, R) = hessenbergGivensQR T)
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hR : R.IsUpperTriangular) (hQR : T = Q * R) :
    Q.HasLowerBandwidth 1 ∧ R.HasUpperBandwidth 2 ∧ R * Q = Qᵀ * T * Q ∧
      (R * Q).IsSymm ∧ (R * Q).IsTridiagonal := by
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hQH : Q.IsUpperHessenberg := by
    rcases hcase with hdet | hG
    · exact hT.isUpperHessenberg.isUpperHessenberg_of_eq_mul hdet hR hQR
    · rw [show Q = (hessenbergGivensQR T).1 by rw [← hG]]
      exact (hessenbergGivensQR_spec hT.isUpperHessenberg).2.2.2
  have hRQ : R * Q = Qᵀ * T * Q := by rw [hQR, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hsym : (R * Q).IsSymm := by
    rw [hRQ]
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hTs))
  have hRQH : (R * Q).IsUpperHessenberg := hR.mul_isUpperHessenberg hQH
  refine ⟨isUpperHessenberg_iff_hasLowerBandwidth_one.1 hQH, ?_, hRQ, hsym,
    hRQH.isTridiagonal_of_isSymm hsym⟩
  -- `R = Qᵀ T`, a product of upper bandwidths `1` and `1`
  have hRe : R = Qᵀ * T := by rw [hQR, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hQt : Qᵀ.HasUpperBandwidth 1 := by
    rw [hasUpperBandwidth_iff_transpose, transpose_transpose]
    exact isUpperHessenberg_iff_hasLowerBandwidth_one.1 hQH
  have hTu : T.HasUpperBandwidth 1 := by
    rw [hasUpperBandwidth_iff_transpose, hTs.eq]
    exact isUpperHessenberg_iff_hasLowerBandwidth_one.1 hT.isUpperHessenberg
  rw [hRe]
  exact hQt.mul hTu

/-- **§8.3.3, shifts.** For symmetric tridiagonal `T`, `s ∈ ℝ` and a QR factorization
`T - sI = Q R` (with `T - sI` nonsingular or `(Q, R)` the Givens QR), the shifted step
`T₊ = R Q + s I = Qᵀ T Q` is symmetric tridiagonal. -/
theorem shifted_qr_tridiagonal {T Q R : Matrix (Fin n) (Fin n) ℝ} (hTs : T.IsSymm)
    (hT : T.IsTridiagonal) {s : ℝ}
    (hcase : IsUnit (T - s • 1).det ∨ (Q, R) = hessenbergGivensQR (T - s • 1))
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hR : R.IsUpperTriangular) (hQR : T - s • 1 = Q * R) :
    R * Q + s • 1 = Qᵀ * T * Q ∧ (R * Q + s • 1).IsSymm ∧ (R * Q + s • 1).IsTridiagonal := by
  have hTs' : (T - s • 1).IsSymm := by
    rw [IsSymm, transpose_sub, transpose_smul, transpose_one, hTs.eq]
  have hT' : (T - s • 1).IsTridiagonal := fun i j hij => by
    rw [Matrix.sub_apply, hT i j hij, Matrix.smul_apply, one_apply_ne, smul_zero, sub_zero]
    rintro rfl
    rcases hij with ⟨c, h1, h2⟩ | ⟨c, h1, h2⟩ <;> exact lt_asymm h1 h2
  obtain ⟨-, -, hRQ, hsym, htri⟩ := qr_tridiagonal_preservation hTs' hT' hcase hQ hR hQR
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  refine ⟨?_, ?_, ?_⟩
  · rw [hRQ, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
      hQQ, sub_add_cancel]
  · rw [IsSymm, transpose_add, hsym.eq, transpose_smul, transpose_one]
  · intro i j hij
    rw [Matrix.add_apply, htri i j hij, Matrix.smul_apply, one_apply_ne, smul_zero, add_zero]
    rintro rfl
    rcases hij with ⟨c, h1, h2⟩ | ⟨c, h1, h2⟩ <;> exact lt_asymm h1 h2

/-- **§8.3.3, perfect shifts.** If `T` is symmetric tridiagonal and unreduced, then for every `s`
the first `n - 1` columns of `T - sI` are linearly independent; if moreover `s` is an eigenvalue
and `QR = T - sI` is any QR factorization, then `r_nn = 0` and the last column of
`T₊ = RQ + sI` is `s e_n`. -/
theorem perfect_shift {N : ℕ} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hTs : T.IsSymm)
    (hT : IsUnreducedTridiagonal T) (s : ℝ) :
    LinearIndependent ℝ (fun j : Fin N => (T - s • 1).col j.castSucc) ∧
      (s ∈ spectrum ℝ T → ∀ Q R : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
        Q ∈ orthogonalGroup _ ℝ → R.IsUpperTriangular → T - s • 1 = Q * R →
          R (Fin.last N) (Fin.last N) = 0 ∧
            ∀ i, (R * Q + s • 1) i (Fin.last N) = if i = Fin.last N then s else 0) := by
  have hli := (hT.2.sub_smul_one s).linearIndependent_init_cols
  refine ⟨hli, fun hs Q R hQ hR hQR => ?_⟩
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hQdet : Q.det ≠ 0 := by
    intro h
    have := congrArg det hQQ
    rw [det_mul, det_transpose, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hdet0 : (T - s • 1).det = 0 := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, eval_charpoly] at hs
    have e : T - s • 1 = -(scalar (Fin (N + 1)) s - T) := by
      rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
    rw [e, det_neg, hs, mul_zero]
  have hRdet : R.det = 0 := by
    rw [hQR, det_mul] at hdet0
    exact (mul_eq_zero.1 hdet0).resolve_left hQdet
  -- the first `N` columns of `R` are independent, and supported in the first `N` rows
  have hliR : LinearIndependent ℝ (fun j : Fin N => R.col j.castSucc) := by
    refine LinearIndependent.of_comp Q.mulVecLin ?_
    convert hli using 1
    funext j
    simp [hQR, col_mul_eq_mulVec_col]
  set R' := R.submatrix Fin.castSucc Fin.castSucc
  set P : Matrix (Fin (N + 1)) (Fin N) ℝ := (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ).submatrix
    id Fin.castSucc
  have hcolR : ∀ j : Fin N, R.col j.castSucc = P *ᵥ R'.col j := fun j => by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · have h0 : R (Fin.last N) j.castSucc = 0 := hR (Fin.castSucc_lt_last j)
      simp [P, R', col_apply, mulVec, dotProduct, one_apply, h0,
        (Fin.castSucc_ne_last _).symm]
    · simp [P, R', col_apply, mulVec, dotProduct, one_apply, Fin.castSucc_inj]
  have hliR' : LinearIndependent ℝ (fun j : Fin N => R'.col j) := by
    refine LinearIndependent.of_comp P.mulVecLin ?_
    convert hliR using 1
    funext j
    simp [hcolR]
  have hR'det : R'.det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).1 (linearIndependent_cols_iff_isUnit.1 hliR')).ne_zero
  have hRtri : R'.IsUpperTriangular := fun i j hij => hR (Fin.castSucc_lt_castSucc_iff.2 hij)
  have hlast : R (Fin.last N) (Fin.last N) = 0 := by
    rw [det_of_isUpperTriangular hR, Fin.prod_univ_castSucc] at hRdet
    rw [det_of_isUpperTriangular hRtri] at hR'det
    exact (mul_eq_zero.1 hRdet).resolve_left hR'det
  refine ⟨hlast, fun i => ?_⟩
  have hrow : ∀ j, R (Fin.last N) j = 0 := fun j => by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · exact hR (Fin.castSucc_lt_last j)
    · exact hlast
  have hsym : (R * Q + s • 1).IsSymm := by
    have e : R * Q + s • 1 = Qᵀ * T * Q := by
      have hRe : R = Qᵀ * (T - s • 1) := by rw [hQR, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      rw [hRe, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
        hQQ, sub_add_cancel]
    rw [e]
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hTs))
  rw [← hsym.apply]
  by_cases hi : i = Fin.last N
  · subst hi
    simp [Matrix.add_apply, mul_apply, hrow]
  · simp [Matrix.add_apply, mul_apply, hrow, one_apply, hi, Ne.symm hi]

/-! ### §8.3.4 Explicit single-shift QR iteration -/

/-- **The Wilkinson shift (8.3.3)**: for `T` of order `n ≥ 2` with trailing `2 × 2` block
`[a_{n-1} b_{n-1}; b_{n-1} a_n]`, `μ = a_n + d - sign(d) √(d² + b_{n-1}²)`, `d = (a_{n-1} - a_n)/2`,
with `sign(0) = 1`. -/
noncomputable def wilkinsonShift {N : ℕ} (T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : ℝ :=
  let a := T (Fin.last (N + 1)) (Fin.last (N + 1))
  let a' := T (Fin.last N).castSucc (Fin.last N).castSucc
  let b := T (Fin.last (N + 1)) (Fin.last N).castSucc
  let d := (a' - a) / 2
  a + d - (if 0 ≤ d then 1 else -1) * Real.sqrt (d ^ 2 + b ^ 2)

/-- **(8.3.3).** The Wilkinson shift `μ` is an eigenvalue of the trailing `2 × 2` block,
`(μ - a_{n-1})(μ - a_n) - b² = 0`, the one closer to `a_n` (`|μ - a_n| ≤ |μ' - a_n|` for the other
root `μ' = a_n + d + sign(d)√(d² + b²)`), and it equals Algorithm 8.3.2's form
`a_n - b² / (d + sign(d) √(d² + b²))`. -/
theorem equation_8_3_3 {N : ℕ} (T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) :
    let a := T (Fin.last (N + 1)) (Fin.last (N + 1))
    let a' := T (Fin.last N).castSucc (Fin.last N).castSucc
    let b := T (Fin.last (N + 1)) (Fin.last N).castSucc
    let d := (a' - a) / 2
    let σ : ℝ := if 0 ≤ d then 1 else -1
    (wilkinsonShift T - a') * (wilkinsonShift T - a) - b ^ 2 = 0 ∧
      |wilkinsonShift T - a| ≤ |(a + d + σ * Real.sqrt (d ^ 2 + b ^ 2)) - a| ∧
      wilkinsonShift T = a - b ^ 2 / (d + σ * Real.sqrt (d ^ 2 + b ^ 2)) := by
  intro a a' b d σ
  have hμ : wilkinsonShift T = a + d - σ * Real.sqrt (d ^ 2 + b ^ 2) := rfl
  have ha' : a' = a + 2 * d := by simp only [d]; ring
  have hσ : σ ^ 2 = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hσa : |σ| = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hσd : 0 ≤ σ * d := by
    simp only [σ]; split_ifs with h
    · linarith
    · nlinarith
  rw [hμ]
  clear_value σ d b a' a
  set S := Real.sqrt (d ^ 2 + b ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSS : S ^ 2 = d ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · rw [ha']
    linear_combination S ^ 2 * hσ + hSS
  · have e1 : a + d - σ * S - a = σ * (σ * d - S) := by linear_combination (-d) * hσ
    have e2 : a + d + σ * S - a = σ * (σ * d + S) := by linear_combination (-d) * hσ
    rw [e1, e2, abs_mul, abs_mul, hσa, one_mul, one_mul, abs_of_nonneg (add_nonneg hσd hS0)]
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · by_cases hden : d + σ * S = 0
    · have hd0 : σ * d + S = 0 := by linear_combination σ * hden - S * hσ
      have hSz : S = 0 := by linarith
      have hdz : σ * d = 0 := by linarith
      have hdz' : d = 0 := by
        have : σ ^ 2 * d = 0 := by rw [sq, mul_assoc, hdz, mul_zero]
        rwa [hσ, one_mul] at this
      rw [hden, div_zero, hSz, hdz']
      ring
    · have hq : b ^ 2 / (d + σ * S) = σ * S - d := by
        rw [div_eq_iff hden]
        linear_combination (-S ^ 2) * hσ - hSS
      rw [hq]
      ring

/-- **(8.3.2), the explicit single-shift QR iteration**: `T_{k+1} = R U + μ I` for the QR
factorization `U R = T_k - μ I` (the backbone's canonical `Matrix.shiftedQrStep`), with the shift
chosen by a rule `shift` (`T ↦ t_nn` or the Wilkinson shift). -/
noncomputable def explicitShiftedQR (shift : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (T₀ : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => T₀
  | k + 1 => shiftedQrStep (shift (explicitShiftedQR shift T₀ k)) (explicitShiftedQR shift T₀ k)

/-- Each iterate of (8.3.2) is orthogonally similar to `T₀`; for symmetric `T₀` it is symmetric,
and for symmetric tridiagonal `T₀` with every shifted matrix nonsingular it stays tridiagonal. -/
theorem explicitShiftedQR_spec (shift : Matrix (Fin n) (Fin n) ℝ → ℝ)
    {T₀ : Matrix (Fin n) (Fin n) ℝ} (hT₀ : T₀.IsSymm) (k : ℕ) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, explicitShiftedQR shift T₀ k = Qᵀ * T₀ * Q ∧
      (explicitShiftedQR shift T₀ k).IsSymm := by
  induction k with
  | zero => exact ⟨1, one_mem _, by simp [explicitShiftedQR], hT₀⟩
  | succ k ih =>
    obtain ⟨Q, hQ, hk, hs⟩ := ih
    set T := explicitShiftedQR shift T₀ k
    set U := qrQ (T - shift T • 1)
    have hU : U ∈ orthogonalGroup (Fin n) ℝ := by
      have := conjTranspose_qrQ_mul_self (T - shift T • 1)
      rw [conjTranspose_eq_transpose_of_trivial] at this
      exact (mem_orthogonalGroup_iff' _ ℝ).2 this
    have hstep : explicitShiftedQR shift T₀ (k + 1) = Uᵀ * T * U := by
      rw [explicitShiftedQR, shiftedQrStep_eq_conj, conjTranspose_eq_transpose_of_trivial]
    refine ⟨Q * U, Submonoid.mul_mem _ hQ hU, ?_, ?_⟩
    · rw [hstep, hk, transpose_mul]
      simp only [Matrix.mul_assoc]
    · rw [hstep]
      simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
        (isHermitian_conjTranspose_mul_mul U (isHermitian_iff_isSymm.2 hs))

/-! ### §8.3.5 Implicit shift version -/

/-- **§8.3.5, one bulge-chasing step.** Let `T` be symmetric and tridiagonal except for a bulge at
`(k + 2, k)` and `(k, k + 2)` (0-based; the book's `z_k`), and let `(c, s)` satisfy
`s b_k + c z_k = 0` with `b_k = t_{k+1,k}`, `z_k = t_{k+2,k}`. Then after the rotation
`G(k + 1, k + 2, θ)` of the book (`Matrix.planeRotation (k+1) (k+2) c (-s)`), `Gᵀ T G` is
tridiagonal except for a bulge at `(k + 3, k + 1)` and `(k + 1, k + 3)`, of value
`z_{k+1} = -s b_{k+2}` (`b_{k+2} = t_{k+3,k+2}`): the bulge moves one step down the band. -/
theorem bulgeChase_step {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm) {k : ℕ}
    (hk : k + 3 < n)
    (hband : ∀ i j : Fin n, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      ¬ ((i : ℕ) = k + 2 ∧ (j : ℕ) = k) → ¬ ((i : ℕ) = k ∧ (j : ℕ) = k + 2) → T i j = 0)
    {c s : ℝ}
    (hzero : s * T ⟨k + 1, by omega⟩ ⟨k, by omega⟩ + c * T ⟨k + 2, by omega⟩ ⟨k, by omega⟩ = 0) :
    let G := planeRotation (⟨k + 1, by omega⟩ : Fin n) ⟨k + 2, by omega⟩ c (-s)
    (∀ i j : Fin n, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      ¬ ((i : ℕ) = k + 3 ∧ (j : ℕ) = k + 1) → ¬ ((i : ℕ) = k + 1 ∧ (j : ℕ) = k + 3) →
        (Gᵀ * T * G) i j = 0) ∧
      (Gᵀ * T * G) ⟨k + 3, hk⟩ ⟨k + 1, by omega⟩ = -s * T ⟨k + 3, hk⟩ ⟨k + 2, by omega⟩ := by
  intro G
  set a : Fin n := ⟨k + 1, by omega⟩ with ha
  set b : Fin n := ⟨k + 2, by omega⟩ with hb
  set z : Fin n := ⟨k, by omega⟩ with hz
  have ha' : (a : ℕ) = k + 1 := rfl
  have hb' : (b : ℕ) = k + 2 := rfl
  have hz' : (z : ℕ) = k := rfl
  have hab : a ≠ b := fun h => by rw [Fin.ext_iff, ha', hb'] at h; omega
  have hsym : ∀ i j, T i j = T j i := fun i j => (hT.apply i j).symm
  have hT0 : ∀ i j : Fin n, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      ¬ ((i : ℕ) = k + 2 ∧ (j : ℕ) = k) → ¬ ((i : ℕ) = k ∧ (j : ℕ) = k + 2) → T i j = 0 := hband
  have hbase : s * T a z + c * T b z = 0 := hzero
  refine ⟨fun i j hij hn1 hn2 => ?_, ?_⟩
  · by_cases hia : i = a
    · subst hia
      have hja : j ≠ a := by rintro rfl; omega
      have hjb : j ≠ b := by rintro rfl; omega
      rw [conj_planeRotation_apply_row_j hab T hja hjb,
        hT0 _ _ (by omega) (by omega) (by omega), hT0 _ _ (by omega) (by omega) (by omega)]
      ring
    by_cases hib : i = b
    · subst hib
      have hja : j ≠ a := by rintro rfl; omega
      have hjb : j ≠ b := by rintro rfl; omega
      rw [conj_planeRotation_apply_row_k hab T hja hjb]
      by_cases hjk : (j : ℕ) = k
      · have hj : j = z := Fin.ext hjk
        rw [hj, neg_neg]
        linear_combination hbase
      · rw [hT0 _ _ (by omega) (by omega) (by omega), hT0 _ _ (by omega) (by omega) (by omega)]
        ring
    by_cases hja : j = a
    · subst hja
      have hia' : (i : ℕ) ≠ k + 1 := fun h => hia (Fin.ext h)
      have hib' : (i : ℕ) ≠ k + 2 := fun h => hib (Fin.ext h)
      rw [conj_planeRotation_apply_col_j hab T hia hib,
        hT0 _ _ (by omega) (by omega) (by omega), hT0 _ _ (by omega) (by omega) (by omega)]
      ring
    by_cases hjb : j = b
    · subst hjb
      have hia' : (i : ℕ) ≠ k + 1 := fun h => hia (Fin.ext h)
      have hib' : (i : ℕ) ≠ k + 2 := fun h => hib (Fin.ext h)
      rw [conj_planeRotation_apply_col_k hab T hia hib]
      by_cases hik : (i : ℕ) = k
      · have hi : i = z := Fin.ext hik
        rw [hi, neg_neg, hsym z a, hsym z b]
        linear_combination hbase
      · rw [hT0 _ _ (by omega) (by omega) (by omega), hT0 _ _ (by omega) (by omega) (by omega)]
        ring
    have hia' : (i : ℕ) ≠ k + 1 := fun h => hia (Fin.ext h)
    have hib' : (i : ℕ) ≠ k + 2 := fun h => hib (Fin.ext h)
    have hja' : (j : ℕ) ≠ k + 1 := fun h => hja (Fin.ext h)
    have hjb' : (j : ℕ) ≠ k + 2 := fun h => hjb (Fin.ext h)
    rw [conj_planeRotation_apply_of_ne hab T hia hib hja hjb]
    exact hT0 i j hij (by omega) (by omega)
  · have h3a : (⟨k + 3, hk⟩ : Fin n) ≠ a := fun h => by rw [Fin.ext_iff, ha'] at h; simp at h
    have h3b : (⟨k + 3, hk⟩ : Fin n) ≠ b := fun h => by rw [Fin.ext_iff, hb'] at h; simp at h
    rw [conj_planeRotation_apply_col_j hab T h3a h3b,
      hT0 ⟨k + 3, hk⟩ a (Or.inr (by rw [ha'])) (by simp [ha']) (by simp [ha'])]
    ring

/-! ### §8.3.6 The Rayleigh quotient connection -/

/-- **§8.3.6.** For symmetric `T` of order `N + 1`, the shift `σ = t_nn` and the QR factorization
`T - σI = QR` (`Matrix.qrQ`, `Matrix.qrR`): `(T - σI) q_n = r_nn e_n` for the last column `q_n` of
`Q`, `r(e_n) = t_nn`, and if `T - σI` is nonsingular, one step of Rayleigh quotient iteration
(8.2.6) from `x_0 = e_n` gives `x_1 = ± q_n`. -/
theorem rayleigh_qr_connection {N : ℕ} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT : T.IsSymm) :
    let σ := T (Fin.last N) (Fin.last N)
    let Q := qrQ (T - σ • 1)
    (T - σ • 1) *ᵥ Q.col (Fin.last N) =
        qrR (T - σ • 1) (Fin.last N) (Fin.last N) • Pi.single (Fin.last N) 1 ∧
      rayleighQuotient T (Pi.single (Fin.last N) 1) = σ ∧
      (IsUnit (T - σ • 1) →
        rayleighQuotientIteration T (Pi.single (Fin.last N) 1) 1 = Q.col (Fin.last N) ∨
          rayleighQuotientIteration T (Pi.single (Fin.last N) 1) 1 = -Q.col (Fin.last N)) := by
  intro σ Q
  have hsym : (T - σ • 1)ᵀ = T - σ • 1 := by
    rw [transpose_sub, transpose_smul, transpose_one, hT.eq]
  have h1 : (T - σ • 1) *ᵥ Q.col (Fin.last N) =
      qrR (T - σ • 1) (Fin.last N) (Fin.last N) • Pi.single (Fin.last N) 1 := by
    have h := toEuclideanLin_transpose_euclideanCol_qrQ_last (T - σ • 1)
    rw [hsym] at h
    exact congrArg WithLp.ofLp h
  have hr : rayleighQuotient T (Pi.single (Fin.last N) 1) = σ := by
    simp [rayleighQuotient, σ, col_apply]
  refine ⟨h1, hr, fun hu => ?_⟩
  set r := qrR (T - σ • 1) (Fin.last N) (Fin.last N)
  have hQQ : Qᴴ * Q = 1 := conjTranspose_qrQ_mul_self _
  have hqn : ‖(WithLp.toLp 2 (Q.col (Fin.last N)) : EuclideanSpace ℝ (Fin (N + 1)))‖ = 1 := by
    rw [← mulVec_single_one, ← toEuclideanLin_toLp,
      norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hQQ]
    have := PiLp.norm_single (p := 2) (β := fun _ : Fin (N + 1) => ℝ) (Fin.last N) (1 : ℝ)
    rwa [norm_one] at this
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h1
    have hinj := (Matrix.mulVec_injective_iff_isUnit).2 hu
    have : Q.col (Fin.last N) = 0 := hinj (by rw [h1, mulVec_zero])
    rw [this] at hqn
    simp at hqn
  -- `z = (T - σI)⁻¹ e_n = q_n / r`
  have hz : (T - rayleighQuotient T (Pi.single (Fin.last N) 1) • 1)⁻¹ *ᵥ
      Pi.single (Fin.last N) 1 = r⁻¹ • Q.col (Fin.last N) := by
    rw [hr]
    have hdet := (isUnit_iff_isUnit_det _).1 hu
    have : Pi.single (Fin.last N) (1 : ℝ) = r⁻¹ • ((T - σ • 1) *ᵥ Q.col (Fin.last N)) := by
      rw [h1, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  simp only [rayleighQuotientIteration]
  rw [hz, WithLp.toLp_smul, norm_smul, hqn, mul_one, smul_smul, Real.norm_eq_abs, abs_inv,
    inv_inv]
  rcases lt_or_gt_of_ne hr0 with h | h
  · right
    rw [abs_of_neg h, neg_mul, mul_inv_cancel₀ hr0, neg_smul, one_smul]
  · left
    rw [abs_of_pos h, mul_inv_cancel₀ hr0, one_smul]

/-! ### §8.3.7 Orthogonal iteration with Ritz acceleration -/

/-- **(8.3.6), orthogonal iteration with Ritz acceleration**: `Q_0` with orthonormal columns; for
`k ≥ 1`, `A Q_{k-1} = Q̃_k R_k` (a thin QR, `Matrix.IsOrthogonalIterationStep`),
`S_k = Q̃_kᵀ A Q̃_k`, `U_kᵀ S_k U_k = D_k` diagonal with `U_k` orthogonal (Schur),
`Q_k = Q̃_k U_k`. -/
def IsRitzAcceleration {r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Q Qt : ℕ → Matrix (Fin n) (Fin r) ℝ) (S U D : ℕ → Matrix (Fin r) (Fin r) ℝ) : Prop :=
  (Q 0)ᵀ * Q 0 = 1 ∧ ∀ k, IsOrthogonalIterationStep A (Q k) (Qt (k + 1)) ∧
    S (k + 1) = (Qt (k + 1))ᵀ * A * Qt (k + 1) ∧ U (k + 1) ∈ orthogonalGroup (Fin r) ℝ ∧
    (U (k + 1))ᵀ * S (k + 1) * U (k + 1) = D (k + 1) ∧ (D (k + 1)).IsDiag ∧
    Q (k + 1) = Qt (k + 1) * U (k + 1)

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§8.3.7.** For a Ritz-accelerated iteration, `‖A Q_k - Q_k D_k‖_F = ‖A Q̃_k - Q̃_k S_k‖_F`,
and this is `min_S ‖A Q̃_k - Q̃_k S‖_F` (Theorem 8.1.14): the columns of `Q_k` are the best basis
from the standpoint of minimizing the residual. -/
theorem ritzAcceleration_residual {r : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q Qt : ℕ → Matrix (Fin n) (Fin r) ℝ} {S U D : ℕ → Matrix (Fin r) (Fin r) ℝ}
    (h : IsRitzAcceleration A Q Qt S U D) (k : ℕ) :
    ‖A * Q (k + 1) - Q (k + 1) * D (k + 1)‖ = ‖A * Qt (k + 1) - Qt (k + 1) * S (k + 1)‖ ∧
      IsLeast (Set.range fun B : Matrix (Fin r) (Fin r) ℝ => ‖A * Qt (k + 1) - Qt (k + 1) * B‖)
        ‖A * Qt (k + 1) - Qt (k + 1) * S (k + 1)‖ := by
  obtain ⟨-, hk⟩ := h
  obtain ⟨⟨R, hQR⟩, hS, hU, hD, -, hQ⟩ := hk k
  have hUU : U (k + 1) * (U (k + 1))ᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hQQ : (Qt (k + 1))ᵀ * Qt (k + 1) = 1 := by
    have := hQR.conjTranspose_mul_self
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨?_, ?_⟩
  · have e : A * Q (k + 1) - Q (k + 1) * D (k + 1) =
        (A * Qt (k + 1) - Qt (k + 1) * S (k + 1)) * U (k + 1) := by
      rw [hQ, ← hD, Matrix.sub_mul]
      congr 1
      · rw [Matrix.mul_assoc]
      · simp only [← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (Qt (k + 1)) (U (k + 1)), hUU, Matrix.mul_one]
    rw [e]
    have := frobenius_norm_unitary_mul_mul_unitary (one_mem (unitaryGroup (Fin n) ℝ))
      (A * Qt (k + 1) - Qt (k + 1) * S (k + 1)) hU
    rwa [Matrix.one_mul] at this
  · have e : A * Qt (k + 1) - Qt (k + 1) * S (k + 1) =
        (1 - Qt (k + 1) * (Qt (k + 1))ᵀ) * A * Qt (k + 1) := by
      rw [hS, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    rw [e]
    exact theorem_8_1_14 A hQQ

end Frobenius

end GolubVanLoan.Chapter08
