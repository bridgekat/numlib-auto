/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside `Mathlib.LinearAlgebra.Matrix.Circulant`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Toeplitz, Hankel and persymmetric matrices

Matrices on `Fin n` that are constant along diagonals or antidiagonals, or symmetric about the
antidiagonal ([golub2013matrix] §4.7, §4.8.2, §12.1.7):

* persymmetry, `Matrix.IsPersymmetric A : ∀ i j, A (rev j) (rev i) = A i j` — symmetry about the
  antidiagonal, `A.submatrix rev rev = Aᵀ` (`Matrix.isPersymmetric_iff_submatrix_rev`), preserved by
  inversion (`Matrix.IsPersymmetric.inv`);
* the Toeplitz matrix of a two-sided sequence, `Matrix.toeplitz r` with entries `r (j - i)`, and the
  predicate `Matrix.IsToeplitz` (constant along each diagonal, `Matrix.isToeplitz_iff`); a square
  Toeplitz matrix is persymmetric (`Matrix.IsToeplitz.isPersymmetric`);
* the symmetric Toeplitz matrix `Matrix.symmToeplitz n r = (r_{|i-j|})` of the
  Levinson–Durbin–Trench theory, with its nesting `T_k ⊂ T_n`
  (`Matrix.leadingPrincipal_symmToeplitz`);
* the Hankel matrix `Matrix.hankel h = (h_{i+j})` and the predicate `Matrix.IsHankel`; reversing the
  rows of a Hankel matrix gives a Toeplitz matrix (`Matrix.IsHankel.isToeplitz_submatrix_rev`);
* and the facts that the tridiagonal Toeplitz matrices of
  `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz` are Toeplitz
  (`Matrix.symmTridiagonalToeplitz_eq_toeplitz`), that Mathlib's `Matrix.circulant` is Toeplitz
  (`Matrix.isToeplitz_circulant`, "a Toeplitz matrix with wraparound"), and that the periodic second
  difference is a circulant (`Matrix.secondDifferencePeriodic_eq_circulant`).

## Design

Everything is on `Fin n`, entrywise. The Toeplitz matrix is rectangular and indexed by an
integer-valued offset, so that unsymmetric Toeplitz matrices (`r_{j-i}` above the diagonal,
`p_{i-j}` below, [golub2013matrix] §4.7.8) need no second definition. The book states persymmetry
and the Hankel–Toeplitz correspondence with the exchange matrix `ℰ_n` (`ℰ A ℰ = Aᵀ`, "`ℰ H` is
Toeplitz"); here they are statements about the reversal `Fin.rev` of rows and columns, which
`Matrix.exchange` of `Numlib.LinearAlgebra.Matrix.Permutation` implements as a matrix.

The diagonalization of a circulant by the discrete Fourier transform is in
`Numlib.Analysis.Fourier.Circulant`, so that this module — and the displacement and Levinson
theories built on it — do not depend on the discrete Fourier transform.
-/

open scoped Fin.IntCast Fin.CommRing

namespace Matrix

variable {R : Type*} {m n : ℕ}

/-! ### Persymmetry -/

/-- Persymmetry, symmetry about the antidiagonal ([golub2013matrix] §4.7.1):
`IsPersymmetric A := ∀ i j, A (rev j) (rev i) = A i j`. The book's definition `ℰ_n A ℰ_n = Aᵀ` is
`Matrix.isPersymmetric_iff_submatrix_rev`. -/
def IsPersymmetric (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, A (Fin.rev j) (Fin.rev i) = A i j

/-- Persymmetry is invariance of the transpose under the reversal of rows and columns:
`A.submatrix rev rev = Aᵀ`, the book's `ℰ A ℰ = Aᵀ` without the permutation matrices. -/
theorem isPersymmetric_iff_submatrix_rev {A : Matrix (Fin n) (Fin n) R} :
    A.IsPersymmetric ↔ A.submatrix Fin.rev Fin.rev = Aᵀ := by
  constructor
  · intro h
    ext i j
    exact h j i
  · intro h i j
    exact congrFun (congrFun h j) i

/-- **The inverse of a persymmetric matrix is persymmetric** ([golub2013matrix] §4.7.1,
`ℰ B⁻¹ ℰ = (ℰ B ℰ)⁻¹ = (Bᵀ)⁻¹ = (B⁻¹)ᵀ`), over a commutative ring and with Mathlib's inverse (junk
value included). -/
theorem IsPersymmetric.inv [CommRing R] {A : Matrix (Fin n) (Fin n) R}
    (hA : A.IsPersymmetric) : A⁻¹.IsPersymmetric := by
  rw [isPersymmetric_iff_submatrix_rev] at hA ⊢
  have h : (A.submatrix Fin.rev Fin.rev)⁻¹ = A⁻¹.submatrix Fin.rev Fin.rev :=
    inv_submatrix_equiv A Fin.revPerm Fin.revPerm
  rw [← h, hA, transpose_nonsing_inv]

/-! ### Toeplitz matrices -/

/-- The Toeplitz matrix of a two-sided sequence ([golub2013matrix] §4.7, `a_ij = r_{j-i}`):
`toeplitz r i j = r (j - i)`, rectangular. -/
def toeplitz (r : ℤ → R) : Matrix (Fin m) (Fin n) R :=
  of fun (i : Fin m) (j : Fin n) => r ((j : ℤ) - i)

/-- The entries of a Toeplitz matrix. -/
theorem toeplitz_apply (r : ℤ → R) (i : Fin m) (j : Fin n) :
    (toeplitz r : Matrix (Fin m) (Fin n) R) i j = r ((j : ℤ) - i) := rfl

/-- A matrix is Toeplitz, constant along each diagonal, when it is `toeplitz r` for some
two-sided sequence `r`. -/
def IsToeplitz (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ r : ℤ → R, A = toeplitz r

/-- A Toeplitz matrix is one constant along each diagonal: entries with the same offset `j - i`
agree. -/
theorem isToeplitz_iff [Zero R] {A : Matrix (Fin m) (Fin n) R} :
    A.IsToeplitz ↔ ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      (j : ℤ) - i = (l : ℤ) - k → A i j = A k l := by
  classical
  constructor
  · rintro ⟨r, rfl⟩ i j k l h
    rw [toeplitz_apply, toeplitz_apply, h]
  · intro hA
    refine ⟨fun d => if h : ∃ p : Fin m × Fin n, (p.2 : ℤ) - p.1 = d then
      A h.choose.1 h.choose.2 else 0, ?_⟩
    ext i j
    have hex : ∃ p : Fin m × Fin n, (p.2 : ℤ) - p.1 = (j : ℤ) - i := ⟨(i, j), rfl⟩
    rw [toeplitz_apply, dite_eq_left hex]
    exact hA _ _ _ _ hex.choose_spec.symm

/-- **A square Toeplitz matrix is persymmetric**: `(rev j) - (rev i) = j - i`. -/
theorem IsToeplitz.isPersymmetric {A : Matrix (Fin n) (Fin n) R} (hA : A.IsToeplitz) :
    A.IsPersymmetric := by
  obtain ⟨r, rfl⟩ := hA
  intro i j
  rw [toeplitz_apply, toeplitz_apply, Fin.val_rev, Fin.val_rev]
  congr 1
  omega

/-- The symmetric tridiagonal Toeplitz matrix `tridiag(a, b, a)` of
`Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz` is Toeplitz. -/
theorem symmTridiagonalToeplitz_eq_toeplitz (n : ℕ) (a b : ℝ) :
    symmTridiagonalToeplitz n a b
      = toeplitz fun d : ℤ => if d = 0 then b else if |d| = 1 then a else 0 := by
  ext i j
  rw [symmTridiagonalToeplitz_apply', toeplitz_apply]
  simp only [abs_eq (zero_le_one' ℤ)]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The tridiagonal Toeplitz matrix `tridiag(a, b, c)` (subdiagonal `a`, superdiagonal `c`) is
Toeplitz. -/
theorem tridiagonalToeplitz_eq_toeplitz (n : ℕ) (a b c : ℝ) :
    tridiagonalToeplitz n a b c
      = toeplitz fun d : ℤ =>
        if d = 0 then b else if d = -1 then a else if d = 1 then c else 0 := by
  ext i j
  rw [tridiagonalToeplitz_apply, toeplitz_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The tridiagonal Toeplitz matrices are Toeplitz in the sense of `Matrix.IsToeplitz`. -/
theorem isToeplitz_symmTridiagonalToeplitz (n : ℕ) (a b : ℝ) :
    (symmTridiagonalToeplitz n a b).IsToeplitz :=
  ⟨_, symmTridiagonalToeplitz_eq_toeplitz n a b⟩

/-! ### Symmetric Toeplitz matrices -/

/-- The symmetric Toeplitz matrix `T = (r_{|i-j|})` ([golub2013matrix] §4.7.2, where `r 0 = 1`):
`symmToeplitz n r i j = r |i - j|`. -/
def symmToeplitz (n : ℕ) (r : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  of fun (i j : Fin n) => r ((i : ℤ) - j).natAbs

/-- The entries of a symmetric Toeplitz matrix. -/
theorem symmToeplitz_apply (r : ℕ → R) (i j : Fin n) :
    symmToeplitz n r i j = r ((i : ℤ) - j).natAbs := rfl

/-- A symmetric Toeplitz matrix is the Toeplitz matrix of the even sequence `d ↦ r |d|`. -/
theorem symmToeplitz_eq_toeplitz (n : ℕ) (r : ℕ → R) :
    symmToeplitz n r = toeplitz fun d => r d.natAbs := by
  ext i j
  rw [symmToeplitz_apply, toeplitz_apply, ← Int.natAbs_neg, neg_sub]

/-- A symmetric Toeplitz matrix is symmetric. -/
theorem symmToeplitz_isSymm (n : ℕ) (r : ℕ → R) : (symmToeplitz n r).IsSymm := by
  ext i j
  rw [transpose_apply, symmToeplitz_apply, symmToeplitz_apply, ← Int.natAbs_neg, neg_sub]

/-- A symmetric Toeplitz matrix is Toeplitz. -/
theorem symmToeplitz_isToeplitz (n : ℕ) (r : ℕ → R) : (symmToeplitz n r).IsToeplitz :=
  ⟨_, symmToeplitz_eq_toeplitz n r⟩

/-- A symmetric Toeplitz matrix is persymmetric. -/
theorem symmToeplitz_isPersymmetric (n : ℕ) (r : ℕ → R) : (symmToeplitz n r).IsPersymmetric :=
  (symmToeplitz_isToeplitz n r).isPersymmetric

/-- A symmetric Toeplitz matrix is invariant under the reversal of rows and columns — the book's
`ℰ T ℰ = T` ([golub2013matrix] §4.7.3), which with `ℰ² = I` is `ℰ T = T ℰ`. -/
theorem symmToeplitz_submatrix_rev (n : ℕ) (r : ℕ → R) :
    (symmToeplitz n r).submatrix Fin.rev Fin.rev = symmToeplitz n r := by
  rw [isPersymmetric_iff_submatrix_rev.mp (symmToeplitz_isPersymmetric n r), symmToeplitz_isSymm]

/-- **The nesting of the `T_k`** ([golub2013matrix] §4.7.2): the leading `k × k` block of `T_n` is
`T_k`. -/
theorem leadingPrincipal_symmToeplitz {k : ℕ} (h : k ≤ n) (r : ℕ → R) :
    (symmToeplitz n r).submatrix (Fin.castLE h) (Fin.castLE h) = symmToeplitz k r := by
  ext i j
  rfl

/-! ### Hankel matrices -/

/-- The Hankel matrix `hankel h = (h_{i+j})`, constant along antidiagonals ([golub2013matrix]
§12.1.7). -/
def hankel (h : ℕ → R) : Matrix (Fin m) (Fin n) R :=
  of fun (i : Fin m) (j : Fin n) => h (i + j)

/-- The entries of a Hankel matrix. -/
theorem hankel_apply (h : ℕ → R) (i : Fin m) (j : Fin n) :
    (hankel h : Matrix (Fin m) (Fin n) R) i j = h (i + j) := rfl

/-- A matrix is Hankel, constant along each antidiagonal, when it is `hankel h` for some `h`. -/
def IsHankel (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ h : ℕ → R, A = hankel h

/-- **Reversing the rows of a Hankel matrix gives a Toeplitz matrix** — the book's "`ℰ_m H` is
Toeplitz" ([golub2013matrix] §12.1.7) without the permutation matrix: the entry `h (m - 1 - i + j)`
depends on `j - i` only. -/
theorem IsHankel.isToeplitz_submatrix_rev {A : Matrix (Fin m) (Fin n) R} (hA : A.IsHankel) :
    (A.submatrix Fin.rev id).IsToeplitz := by
  obtain ⟨h, rfl⟩ := hA
  refine ⟨fun d => h ((m - 1 : ℤ) + d).toNat, ?_⟩
  ext i j
  rw [submatrix_apply, hankel_apply, toeplitz_apply, Fin.val_rev, id]
  congr 1
  omega

/-! ### Circulant matrices -/

/-- **A circulant is a Toeplitz matrix with wraparound** ([golub2013matrix] §4.8.2): Mathlib's
`circulant v`, with entries `v (i - j)`, is Toeplitz, of the sequence `d ↦ v (-d)`. -/
theorem isToeplitz_circulant [Zero R] (v : Fin n → R) : (circulant v).IsToeplitz := by
  rcases n with _ | n
  · exact ⟨0, by ext i; exact i.elim0⟩
  · refine ⟨fun d => v ((-d : ℤ) : Fin (n + 1)), ?_⟩
    ext i j
    rw [circulant_apply, toeplitz_apply]
    congr 1
    push_cast
    simp

/-- The value of a difference in `Fin n`: `i - j` if `j ≤ i`, `n + i - j` otherwise. -/
private theorem val_sub_fin (i j : Fin n) :
    ((i - j : Fin n) : ℕ) = if (j : ℕ) ≤ i then (i : ℕ) - j else n + i - j := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.mpr h
  · exact Fin.coe_sub_iff_lt.mpr (by omega)

/-- **The periodic second difference is a circulant** ([golub2013matrix] §4.8.6): for `3 ≤ n`,
`𝒯^{(P)}_n` is the circulant of its first column `(2, −1, 0, …, 0, −1)`. (For `n = 2` the two
corrections fall on the off-diagonal and the claim fails: `𝒯^{(P)}_2 = [2 −2; −2 2]`.) -/
theorem secondDifferencePeriodic_eq_circulant (hn : 3 ≤ n) :
    secondDifferencePeriodic n = circulant fun k : Fin n =>
      if (k : ℕ) = 0 then 2 else if (k : ℕ) = 1 ∨ (k : ℕ) + 1 = n then -1 else 0 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [secondDifferencePeriodic, sub_apply, of_apply, symmTridiagonalToeplitz_apply',
    circulant_apply, val_sub_fin]
  split_ifs <;> first | (exfalso; omega) | ring

end Matrix
