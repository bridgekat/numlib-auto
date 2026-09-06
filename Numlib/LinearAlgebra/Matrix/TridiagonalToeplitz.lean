/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside `Mathlib.LinearAlgebra.Matrix.Circulant`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.Hessenberg

/-!
# The symmetric tridiagonal Toeplitz matrix and its discrete sine eigenbasis

`Matrix.symmTridiagonalToeplitz n a b` is `tridiag(a, b, a)`: the `n × n` real matrix with `b`
on the diagonal and `a` on both off-diagonals.  It is diagonalized, for every `a` and `b` at
once, by the **discrete sine vectors** `Matrix.sineVec n k`, whose `j`-th entry is
`sin((j + 1)(k + 1)π / (n + 1))`, with eigenvalue `b + 2 a cos((k + 1)π / (n + 1))`.

The whole content is the trigonometric identity
`sin((j - 1)θ) + sin((j + 1)θ) = 2 cos θ sin(jθ)`, applied at `θ_k = (k + 1)π / (n + 1)`.  The
first and last rows of the matrix are the same identity with the missing neighbour supplied by
the boundary values `sin 0 = 0` and `sin((n + 1)θ_k) = 0`, which is exactly why the sine vectors
are the eigenvectors of a *tridiagonal* Toeplitz matrix.

Everything else follows: the sine vectors are pairwise orthogonal, of squared length
`(n + 1) / 2` (`Matrix.dotProduct_sineVec`), so after the normalization `√(2 / (n + 1))` they
form an orthonormal basis (`Matrix.sineOrthonormalBasis`); the spectrum consists of exactly the
`n` numbers `b + 2 a cos θ_k` (`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff`); the
quadratic form is enclosed in `[b - 2|a| cos(π/(n+1)), b + 2|a| cos(π/(n+1))]`
(`Matrix.isSymmetricBoundedBy_symmTridiagonalToeplitz`); and `tridiag(-1, 2, -1)`, whose
eigenvalues are `4 sin²((k + 1)π / (2(n + 1)))`, is positive definite.

This is the model problem of Saad, *Iterative Methods for Sparse Linear
Systems*[^saad-iterative], §2.2.3 and §2.2.6, and of Kress, *Numerical Analysis*[^kress], §4.
The module knows nothing about differential equations: the claim that these matrices discretize
`-u''` belongs to a textbook surface, and the two-dimensional five-point Laplacian is the
Kronecker sum of two of them, in `Numlib.LinearAlgebra.Matrix.KroneckerSum`.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
-/

open Finset
open scoped Real Matrix

namespace Matrix

variable {n : ℕ} (a b : ℝ)

/-! ### The matrix -/

/-- The symmetric tridiagonal Toeplitz matrix `tridiag(a, b, a)`: `b` on the diagonal, `a` on
both off-diagonals and `0` elsewhere. -/
def symmTridiagonalToeplitz (n : ℕ) (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then b else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then a else 0

/-- The entries of `tridiag(a, b, a)`. -/
theorem symmTridiagonalToeplitz_apply (i j : Fin n) :
    symmTridiagonalToeplitz n a b i j =
      if i = j then b else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then a else 0 := rfl

/-- The entries, with every condition read off the natural-number indices. -/
theorem symmTridiagonalToeplitz_apply' (i j : Fin n) :
    symmTridiagonalToeplitz n a b i j =
      if (i : ℕ) = j then b else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then a else 0 := by
  rw [symmTridiagonalToeplitz_apply]
  simp only [Fin.ext_iff]

/-- The diagonal entries are `b`. -/
@[simp]
theorem symmTridiagonalToeplitz_apply_self (i : Fin n) :
    symmTridiagonalToeplitz n a b i i = b := by simp [symmTridiagonalToeplitz_apply]

/-- The entries on the first superdiagonal are `a`. -/
theorem symmTridiagonalToeplitz_apply_succ {i j : Fin n} (h : (i : ℕ) + 1 = j) :
    symmTridiagonalToeplitz n a b i j = a := by
  rw [symmTridiagonalToeplitz_apply']
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Away from the three central diagonals the entries vanish. -/
theorem symmTridiagonalToeplitz_apply_of_one_lt {i j : Fin n}
    (h : (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) : symmTridiagonalToeplitz n a b i j = 0 := by
  rw [symmTridiagonalToeplitz_apply']
  split_ifs <;> first | rfl | (exfalso; omega)

/-- A symmetric tridiagonal Toeplitz matrix is symmetric. -/
theorem symmTridiagonalToeplitz_isSymm : (symmTridiagonalToeplitz n a b).IsSymm := by
  ext i j
  rw [transpose_apply, symmTridiagonalToeplitz_apply', symmTridiagonalToeplitz_apply']
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Over the reals, symmetry is Hermitian symmetry. -/
theorem symmTridiagonalToeplitz_isHermitian : (symmTridiagonalToeplitz n a b).IsHermitian := by
  ext i j
  rw [conjTranspose_apply, star_trivial, symmTridiagonalToeplitz_apply',
    symmTridiagonalToeplitz_apply']
  split_ifs <;> first | rfl | (exfalso; omega)

/-- A symmetric tridiagonal Toeplitz matrix is tridiagonal in the sense of
`Matrix.IsTridiagonal`. -/
theorem symmTridiagonalToeplitz_isTridiagonal :
    (symmTridiagonalToeplitz n a b).IsTridiagonal := by
  rintro i j (⟨k, hjk, hki⟩ | ⟨k, hik, hkj⟩)
  · exact symmTridiagonalToeplitz_apply_of_one_lt a b
      (Or.inr (by have h1 : (j : ℕ) < k := hjk; have h2 : (k : ℕ) < i := hki; omega))
  · exact symmTridiagonalToeplitz_apply_of_one_lt a b
      (Or.inl (by have h1 : (i : ℕ) < k := hik; have h2 : (k : ℕ) < j := hkj; omega))

/-! ### The action on a vector -/

/-- A vector on `Fin n`, shifted up by one and extended by zero to all of `ℕ`.  It turns the
three-term row of a tridiagonal matrix into a uniform formula: the missing neighbours at the
first and last rows are supplied by the padding. -/
private def padZero (v : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => if h : m < n then v ⟨m, h⟩ else 0

private theorem padZero_zero (v : Fin n → ℝ) : padZero v 0 = 0 := rfl

private theorem padZero_succ (v : Fin n → ℝ) (m : ℕ) :
    padZero v (m + 1) = if h : m < n then v ⟨m, h⟩ else 0 := rfl

private theorem padZero_val_succ (v : Fin n → ℝ) (i : Fin n) :
    padZero v ((i : ℕ) + 1) = v i := by
  rw [padZero_succ, dite_eq_left i.isLt]

private theorem padZero_of_lt (v : Fin n → ℝ) {m : ℕ} (hm : n < m) : padZero v m = 0 := by
  cases m with
  | zero => rfl
  | succ m => rw [padZero_succ, dite_eq_right (by omega)]

/-- The sum picking out the entry at natural index `m`, in the padded form. -/
private theorem sum_ite_val_eq (c : ℝ) (v : Fin n → ℝ) (m : ℕ) :
    ∑ j : Fin n, (if (j : ℕ) = m then c * v j else 0) = c * padZero v (m + 1) := by
  have h : ∀ j : Fin n, (if (j : ℕ) = m then c * v j else 0)
      = if (j : ℕ) = m then c * padZero v ((j : ℕ) + 1) else 0 := by
    intro j; rw [padZero_val_succ]
  rw [Finset.sum_congr rfl fun j _ => h j,
    Fin.sum_univ_eq_sum_range fun j => if j = m then c * padZero v (j + 1) else 0,
    Finset.sum_ite_eq' (Finset.range n) m fun j => c * padZero v (j + 1)]
  by_cases hm : m < n
  · rw [ite_eq_left (Finset.mem_range.2 hm)]
  · rw [ite_eq_right fun hmem => hm (Finset.mem_range.1 hmem), padZero_of_lt v (by omega),
      mul_zero]

/-- The sum picking out the entry just below natural index `m`, in the padded form. -/
private theorem sum_ite_val_succ_eq (c : ℝ) (v : Fin n → ℝ) (m : ℕ) :
    ∑ j : Fin n, (if (j : ℕ) + 1 = m then c * v j else 0) = c * padZero v m := by
  cases m with
  | zero => simp [padZero_zero]
  | succ m =>
    have h : ∀ j : Fin n, ((j : ℕ) + 1 = m + 1) = ((j : ℕ) = m) := fun j => by simp
    simp only [h]
    exact sum_ite_val_eq c v m

/-- The three-term row of a symmetric tridiagonal Toeplitz matrix, uniformly across the first,
the last and the interior rows. -/
private theorem symmTridiagonalToeplitz_mulVec_apply (v : Fin n → ℝ) (i : Fin n) :
    (symmTridiagonalToeplitz n a b *ᵥ v) i
      = a * padZero v (i : ℕ) + b * padZero v ((i : ℕ) + 1) + a * padZero v ((i : ℕ) + 2) := by
  have hsplit : ∀ j : Fin n, symmTridiagonalToeplitz n a b i j * v j
      = (if (j : ℕ) + 1 = (i : ℕ) then a * v j else 0)
        + (if (j : ℕ) = (i : ℕ) then b * v j else 0)
        + (if (j : ℕ) = (i : ℕ) + 1 then a * v j else 0) := by
    intro j
    rw [symmTridiagonalToeplitz_apply']
    split_ifs <;> first | (exfalso; omega) | ring
  rw [mulVec, dotProduct]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_val_succ_eq, sum_ite_val_eq,
    sum_ite_val_eq]

/-! ### The discrete sine vectors -/

/-- The `k`-th discrete sine vector on `Fin n`, `j ↦ sin((j + 1)(k + 1)π / (n + 1))`: an
eigenvector of every `Matrix.symmTridiagonalToeplitz n a b`. -/
noncomputable def sineVec (n : ℕ) (k : Fin n) : Fin n → ℝ :=
  fun j => Real.sin (((j : ℕ) + 1) * (((k : ℕ) + 1) * π / (n + 1)))

/-- The entries of a discrete sine vector. -/
theorem sineVec_apply (k j : Fin n) :
    sineVec n k j = Real.sin (((j : ℕ) + 1) * (((k : ℕ) + 1) * π / (n + 1))) := rfl

/-- The angle `θ_k = (k + 1)π / (n + 1)` is positive, which is why every discrete sine vector is
nonzero. -/
theorem angle_pos (n : ℕ) (k : Fin n) : 0 < (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  positivity

/-- The angle `θ_k = (k + 1)π / (n + 1)` is below `π`, which is why the `n` eigenvalues
`b + 2 a cos θ_k` are distinct. -/
theorem angle_lt_pi (n : ℕ) (k : Fin n) : (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1) < π := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk : ((k : ℕ) : ℝ) + 1 < (n : ℝ) + 1 := by
    have : ((k : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast k.isLt
    linarith
  rw [div_lt_iff₀ hn]
  nlinarith [Real.pi_pos]

/-- Distinct indices give distinct angles. -/
private theorem angle_inj {k l : Fin n}
    (h : (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)
      = (((l : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) : k = l := by
  have hc : π / ((n : ℝ) + 1) ≠ 0 := ne_of_gt (div_pos Real.pi_pos (by positivity))
  have h1 : (((k : ℕ) : ℝ) + 1) * (π / ((n : ℝ) + 1))
      = (((l : ℕ) : ℝ) + 1) * (π / ((n : ℝ) + 1)) := by
    rw [← mul_div_assoc, ← mul_div_assoc]; exact h
  have h3 : ((k : ℕ) : ℝ) = ((l : ℕ) : ℝ) := by
    have := mul_right_cancel₀ hc h1; linarith
  exact Fin.ext (by exact_mod_cast h3)

/-- The padded sine vector is the sine at every natural index up to `n + 1`: `sin 0 = 0` at the
bottom and `sin((n + 1)θ_k) = sin((k + 1)π) = 0` at the top are exactly the padding. -/
private theorem padZero_sineVec (k : Fin n) {m : ℕ} (hm : m ≤ n + 1) :
    padZero (sineVec n k) m = Real.sin ((m : ℝ) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) := by
  cases m with
  | zero => simp [padZero_zero]
  | succ m =>
    rw [padZero_succ]
    by_cases h : m < n
    · rw [dite_eq_left h, sineVec_apply]
      push_cast
      ring_nf
    · rw [dite_eq_right h]
      have hmn : m = n := by omega
      subst hmn
      have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hrw : ((m : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((m : ℝ) + 1))
          = ((((k : ℕ) : ℤ) + 1 : ℤ) : ℝ) * π := by
        field_simp
        push_cast
        ring
      push_cast
      rw [hrw, Real.sin_int_mul_pi]

/-- The eigenpairs of the symmetric tridiagonal Toeplitz matrix: the `k`-th discrete sine vector
is an eigenvector with eigenvalue `b + 2 a cos((k + 1)π / (n + 1))`, for every `a` and `b` at
once.  Row by row this is `sin((j - 1)θ) + sin((j + 1)θ) = 2 cos θ sin(jθ)`, the first and last
rows included thanks to `sin 0 = 0` and `sin((n + 1)θ_k) = 0`. -/
theorem symmTridiagonalToeplitz_mulVec_sineVec (k : Fin n) :
    symmTridiagonalToeplitz n a b *ᵥ sineVec n k
      = (b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) • sineVec n k := by
  funext i
  have hi : (i : ℕ) + 2 ≤ n + 1 := by omega
  rw [symmTridiagonalToeplitz_mulVec_apply, padZero_sineVec k (by omega),
    padZero_sineVec k (by omega), padZero_sineVec k hi]
  have hkey : Real.sin (((i : ℕ) : ℝ)
        * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
      + Real.sin ((((i : ℕ) : ℝ) + 2) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
      = 2 * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
        * Real.sin ((((i : ℕ) : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) := by
    set θ : ℝ := (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1) with hθ
    have h1 : ((i : ℕ) : ℝ) * θ = ((((i : ℕ) : ℝ) + 1) * θ) - θ := by ring
    have h2 : (((i : ℕ) : ℝ) + 2) * θ = ((((i : ℕ) : ℝ) + 1) * θ) + θ := by ring
    rw [h1, h2, Real.sin_sub, Real.sin_add]
    ring
  simp only [Pi.smul_apply, smul_eq_mul, sineVec_apply]
  push_cast at hkey ⊢
  linear_combination a * hkey

/-- The discrete sine vectors are nonzero: the first entry is `sin θ_k` with `0 < θ_k < π`. -/
theorem sineVec_ne_zero (k : Fin n) : sineVec n k ≠ 0 := by
  have hpos : 0 < sineVec n k ⟨0, k.pos⟩ := by
    rw [sineVec_apply]
    simpa using Real.sin_pos_of_pos_of_lt_pi (angle_pos n k) (angle_lt_pi n k)
  intro h
  rw [h] at hpos
  simp at hpos

/-! ### Orthogonality of the sine basis -/

/-- The telescoping identity `2 sin φ ∑_{j<M} cos(2(j+1)φ) = sin((2M+1)φ) - sin φ`, from
`sin(x + φ) - sin(x - φ) = 2 cos x sin φ`. -/
private theorem two_sin_mul_sum_cos (φ : ℝ) (M : ℕ) :
    2 * Real.sin φ * ∑ j ∈ Finset.range M, Real.cos (2 * ((j : ℝ) + 1) * φ)
      = Real.sin ((2 * (M : ℝ) + 1) * φ) - Real.sin φ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : (2 * ((M : ℝ) + 1) + 1) * φ = (2 * (M : ℝ) + 2) * φ + φ := by ring
    have h2 : (2 * (M : ℝ) + 1) * φ = (2 * (M : ℝ) + 2) * φ - φ := by ring
    push_cast
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring_nf

/-- The cosine sum at a sine-basis angle: `∑_{j<n} cos(2(j+1)θ_k) = -1`, because
`sin((2n+1)θ_k) = -sin θ_k`. -/
private theorem sum_cos_two_mul_angle (k : Fin n) :
    ∑ j ∈ Finset.range n,
        Real.cos (2 * ((j : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) = -1 := by
  have hs : Real.sin ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (angle_pos n k) (angle_lt_pi n k))
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hend : (2 * (n : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      = -((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) + (((k : ℕ) : ℤ) + 1 : ℤ) * (2 * π) := by
    push_cast
    field_simp
    ring
  have h := two_sin_mul_sum_cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) n
  rw [hend, Real.sin_add_int_mul_two_pi, Real.sin_neg] at h
  have h2 : 2 * Real.sin ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      * (∑ j ∈ Finset.range n,
          Real.cos (2 * ((j : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))))
      = 2 * Real.sin ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) * (-1) := by
    rw [h]; ring
  exact mul_left_cancel₀ (by simpa using hs) h2

/-- The squared length of a discrete sine vector, `∑_j sin²((j+1)θ_k) = (n+1)/2`. -/
private theorem sum_sineVec_mul_self (k : Fin n) :
    ∑ j : Fin n, sineVec n k j * sineVec n k j = ((n : ℝ) + 1) / 2 := by
  have hterm : ∀ j : Fin n, sineVec n k j * sineVec n k j
      = 1 / 2 - Real.cos (2 * (((j : ℕ) : ℝ) + 1)
          * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) / 2 := by
    intro j
    have h := Real.cos_two_mul_eq_one_sub
      ((((j : ℕ) : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
    rw [sineVec_apply, ← sq, show 2 * (((j : ℕ) : ℝ) + 1)
      * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      = 2 * ((((j : ℕ) : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) by ring]
    linarith
  have hsum : ∑ j ∈ Finset.range n,
      (1 / 2 - Real.cos (2 * ((j : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) / 2)
      = (n : ℝ) / 2 - (∑ j ∈ Finset.range n,
        Real.cos (2 * ((j : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))) / 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j,
    Fin.sum_univ_eq_sum_range fun j =>
      1 / 2 - Real.cos (2 * ((j : ℝ) + 1) * ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) / 2,
    hsum, sum_cos_two_mul_angle k]
  ring

/-- Orthogonality of the discrete sine basis:
`sineVec n k ⬝ᵥ sineVec n l = if k = l then (n + 1) / 2 else 0`.  Off the diagonal this is the
orthogonality of eigenvectors of the symmetric matrix `tridiag(1, 0, 1)` belonging to the
distinct eigenvalues `2 cos θ_k`; on the diagonal it is a telescoping cosine sum. -/
theorem dotProduct_sineVec (k l : Fin n) :
    sineVec n k ⬝ᵥ sineVec n l = if k = l then ((n : ℝ) + 1) / 2 else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, dotProduct]
    exact sum_sineVec_mul_self k
  rw [ite_eq_right hkl]
  have hsymm : ∀ v w : Fin n → ℝ, v ⬝ᵥ (symmTridiagonalToeplitz n 1 0 *ᵥ w)
      = (symmTridiagonalToeplitz n 1 0 *ᵥ v) ⬝ᵥ w := by
    intro v w
    rw [dotProduct_mulVec]
    congr 1
    rw [← vecMul_transpose, symmTridiagonalToeplitz_isSymm]
  have heig : ∀ m : Fin n, symmTridiagonalToeplitz n 1 0 *ᵥ sineVec n m
      = (2 * Real.cos ((((m : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) • sineVec n m := by
    intro m
    rw [symmTridiagonalToeplitz_mulVec_sineVec]
    norm_num
  have hcos : Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      ≠ Real.cos ((((l : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) := fun h =>
    hkl (angle_inj (Real.injOn_cos ⟨(angle_pos n k).le, (angle_lt_pi n k).le⟩
      ⟨(angle_pos n l).le, (angle_lt_pi n l).le⟩ h))
  have h1 := hsymm (sineVec n k) (sineVec n l)
  rw [heig l, heig k, dotProduct_smul, smul_dotProduct] at h1
  simp only [smul_eq_mul] at h1
  have h2 : (2 * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      - 2 * Real.cos ((((l : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
      * (sineVec n k ⬝ᵥ sineVec n l) = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h' | h'
  · exact absurd (by linarith : Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      = Real.cos ((((l : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) hcos
  · exact h'

/-! ### The orthonormal sine basis -/

/-- The inner product of two discrete sine vectors, in the `EuclideanSpace` form that the
spectral statements need. -/
theorem inner_toLp_sineVec (k l : Fin n) :
    inner ℝ (WithLp.toLp 2 (sineVec n k)) (WithLp.toLp 2 (sineVec n l))
      = if k = l then ((n : ℝ) + 1) / 2 else 0 := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm, dotProduct_sineVec]

/-- The normalized discrete sine vectors `√(2/(n+1)) q_k` are orthonormal. -/
theorem orthonormal_sineVec (n : ℕ) :
    Orthonormal ℝ fun k : Fin n =>
      Real.sqrt (2 / ((n : ℝ) + 1)) • (WithLp.toLp 2 (sineVec n k)) := by
  have hsq : Real.sqrt (2 / ((n : ℝ) + 1)) * Real.sqrt (2 / ((n : ℝ) + 1))
      = 2 / ((n : ℝ) + 1) := Real.mul_self_sqrt (by positivity)
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  refine orthonormal_iff_ite.2 fun k l => ?_
  rw [real_inner_smul_left, real_inner_smul_right, inner_toLp_sineVec]
  by_cases h : k = l
  · rw [ite_eq_left h, ite_eq_left h, ← mul_assoc, hsq]
    field_simp
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]

/-- The normalized discrete sine vectors as an orthonormal basis of `EuclideanSpace ℝ (Fin n)`.
It diagonalizes every `Matrix.symmTridiagonalToeplitz n a b` at once: the symmetric tridiagonal
Toeplitz matrices are a family with this one common eigenbasis. -/
noncomputable def sineOrthonormalBasis (n : ℕ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  OrthonormalBasis.mk (orthonormal_sineVec n)
    ((orthonormal_sineVec n).linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge

/-- The vectors of the orthonormal sine basis are the normalized discrete sine vectors. -/
@[simp]
theorem sineOrthonormalBasis_apply (k : Fin n) :
    sineOrthonormalBasis n k = Real.sqrt (2 / ((n : ℝ) + 1)) • (WithLp.toLp 2 (sineVec n k)) := by
  rw [sineOrthonormalBasis, OrthonormalBasis.coe_mk]

/-- The eigenpairs, read on the orthonormal sine basis. -/
theorem toEuclideanLin_symmTridiagonalToeplitz_apply_sineOrthonormalBasis (k : Fin n) :
    toEuclideanLin (symmTridiagonalToeplitz n a b) (sineOrthonormalBasis n k)
      = (b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
        • sineOrthonormalBasis n k := by
  have hmul : toEuclideanLin (symmTridiagonalToeplitz n a b)
      (WithLp.toLp 2 (sineVec n k))
      = WithLp.toLp 2 (symmTridiagonalToeplitz n a b *ᵥ sineVec n k) := rfl
  have hsmul : (WithLp.toLp 2
        ((b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) • sineVec n k) :
        EuclideanSpace ℝ (Fin n))
      = (b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
        • WithLp.toLp 2 (sineVec n k) := rfl
  rw [sineOrthonormalBasis_apply, map_smul, hmul, symmTridiagonalToeplitz_mulVec_sineVec, hsmul,
    smul_comm]

/-- The eigenpairs of `Matrix.symmTridiagonalToeplitz`, as `Module.End.HasEigenvector`. -/
theorem sineOrthonormalBasis_hasEigenvector (k : Fin n) :
    Module.End.HasEigenvector (toEuclideanLin (symmTridiagonalToeplitz n a b))
      (b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
      (sineOrthonormalBasis n k) :=
  ⟨Module.End.mem_eigenspace_iff.2
    (toEuclideanLin_symmTridiagonalToeplitz_apply_sineOrthonormalBasis a b k),
   (sineOrthonormalBasis n).orthonormal.ne_zero k⟩

/-! ### The spectrum and the quadratic form -/

/-- The sine basis exhausts the spectrum: the eigenvalues of `tridiag(a, b, a)` are exactly the
`n` numbers `b + 2 a cos((k + 1)π / (n + 1))`. -/
theorem symmTridiagonalToeplitz_hasEigenvalue_iff (μ : ℝ) :
    Module.End.HasEigenvalue (toEuclideanLin (symmTridiagonalToeplitz n a b)) μ ↔
      ∃ k : Fin n, μ = b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) := by
  refine ⟨fun hμ => ?_, ?_⟩
  · by_contra hne
    push Not at hne
    obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hx
    have hsymm : (toEuclideanLin (symmTridiagonalToeplitz n a b)).IsSymmetric :=
      isSymmetric_toEuclideanLin_iff.2 (symmTridiagonalToeplitz_isHermitian a b)
    have hzero : ∀ k : Fin n, inner ℝ (sineOrthonormalBasis n k) x = 0 := by
      intro k
      have h1 : inner ℝ (sineOrthonormalBasis n k)
          (toEuclideanLin (symmTridiagonalToeplitz n a b) x)
          = μ * inner ℝ (sineOrthonormalBasis n k) x := by
        rw [hx, real_inner_smul_right]
      have h2 : inner ℝ (sineOrthonormalBasis n k)
          (toEuclideanLin (symmTridiagonalToeplitz n a b) x)
          = (b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
            * inner ℝ (sineOrthonormalBasis n k) x := by
        rw [← hsymm (sineOrthonormalBasis n k) x,
          toEuclideanLin_symmTridiagonalToeplitz_apply_sineOrthonormalBasis,
          real_inner_smul_left]
      have h3 : (μ - (b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))))
          * inner ℝ (sineOrthonormalBasis n k) x = 0 := by
        rw [sub_mul, ← h1, h2, sub_self]
      rcases mul_eq_zero.1 h3 with h' | h'
      · exact absurd (by linarith : μ
          = b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) (hne k)
      · exact h'
    refine hx0 ?_
    rw [← (sineOrthonormalBasis n).sum_repr' x]
    exact Finset.sum_eq_zero fun k _ => by rw [hzero k, zero_smul]
  · rintro ⟨k, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector (sineOrthonormalBasis_hasEigenvector a b k)

/-- The quadratic-form bounds of `tridiag(a, b, a)` from bounds on its eigenvalues, through the
sine eigenbasis.  This is the shape in which every convergence estimate consumes the spectrum of
the model problem: no eigenvalue is ever named. -/
theorem isSymmetricBoundedBy_symmTridiagonalToeplitz_of_mem_Icc {lmin lmax : ℝ}
    (h : ∀ k : Fin n, b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      ∈ Set.Icc lmin lmax) :
    (toEuclideanLin (symmTridiagonalToeplitz n a b)).IsSymmetricBoundedBy lmin lmax := by
  have hsymm : (toEuclideanLin (symmTridiagonalToeplitz n a b)).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.2 (symmTridiagonalToeplitz_isHermitian a b)
  have hquad : ∀ x : EuclideanSpace ℝ (Fin n),
      inner ℝ (toEuclideanLin (symmTridiagonalToeplitz n a b) x) x
        = ∑ k : Fin n, (b + 2 * a * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)))
            * inner ℝ (sineOrthonormalBasis n k) x ^ 2 := by
    intro x
    rw [← (sineOrthonormalBasis n).sum_inner_mul_inner
      (toEuclideanLin (symmTridiagonalToeplitz n a b) x) x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsymm x (sineOrthonormalBasis n k),
      toEuclideanLin_symmTridiagonalToeplitz_apply_sineOrthonormalBasis,
      real_inner_smul_right, real_inner_comm (sineOrthonormalBasis n k) x]
    ring
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x‖ ^ 2 = ∑ k : Fin n, inner ℝ (sineOrthonormalBasis n k) x ^ 2 := by
    intro x
    rw [← real_inner_self_eq_norm_sq, ← (sineOrthonormalBasis n).sum_inner_mul_inner x x]
    exact Finset.sum_congr rfl fun k _ => by
      rw [real_inner_comm (sineOrthonormalBasis n k) x, sq]
  refine ⟨hsymm, fun x => ?_, fun x => ?_⟩
  · rw [RCLike.re_to_real, hquad, hnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h k).1 (sq_nonneg _)
  · rw [RCLike.re_to_real, hquad, hnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h k).2 (sq_nonneg _)

/-- The spectrum of `tridiag(a, b, a)` in quadratic-form form: it is enclosed in
`[b - 2|a| cos(π/(n+1)), b + 2|a| cos(π/(n+1))]`, and both ends are attained, at `k = n - 1` and
at `k = 0`.  This is the sharp version of the crude bound `[b - 2|a|, b + 2|a|]`, and it is what
makes the condition number of the model problem grow like `(n + 1)²`. -/
theorem isSymmetricBoundedBy_symmTridiagonalToeplitz (n : ℕ) (a b : ℝ) :
    (toEuclideanLin (symmTridiagonalToeplitz n a b)).IsSymmetricBoundedBy
      (b - 2 * |a| * Real.cos (π / ((n : ℝ) + 1)))
      (b + 2 * |a| * Real.cos (π / ((n : ℝ) + 1))) := by
  refine isSymmetricBoundedBy_symmTridiagonalToeplitz_of_mem_Icc a b fun k => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk1 : π / ((n : ℝ) + 1) ≤ (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1) := by
    rw [div_le_div_iff_of_pos_right hn]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  have hupper : Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      ≤ Real.cos (π / ((n : ℝ) + 1)) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (angle_lt_pi n k).le hk1
  have hk2 : (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1) ≤ π - π / ((n : ℝ) + 1) := by
    have hkn : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast k.isLt
    have hrw : π - π / ((n : ℝ) + 1) = (n : ℝ) * π / ((n : ℝ) + 1) := by field_simp; ring
    rw [hrw, div_le_div_iff_of_pos_right hn]
    nlinarith [Real.pi_pos]
  have hlower : -Real.cos (π / ((n : ℝ) + 1))
      ≤ Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (angle_pos n k).le
      (by linarith [div_nonneg Real.pi_pos.le hn.le] : π - π / ((n : ℝ) + 1) ≤ π) hk2
    rwa [Real.cos_pi_sub] at h
  rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;>
    exact ⟨by nlinarith [hupper, hlower], by nlinarith [hupper, hlower]⟩

/-- `tridiag(a, b, a)` is positive definite when the diagonal dominates strictly, `2|a| < b`.
The boundary case `2|a| = b`, which is the model Laplacian `tridiag(-1, 2, -1)`, needs the sharp
cosine bound instead: see `Matrix.posDef_symmTridiagonalToeplitz_neg_one_two`. -/
theorem posDef_symmTridiagonalToeplitz (n : ℕ) {a b : ℝ} (h : 2 * |a| < b) :
    (symmTridiagonalToeplitz n a b).PosDef := by
  rw [posDef_iff_isSymmetricCoercive]
  refine (isSymmetricBoundedBy_symmTridiagonalToeplitz n a b).isSymmetricCoercive ?_
  nlinarith [Real.cos_le_one (π / ((n : ℝ) + 1)), abs_nonneg a]

/-- The one-dimensional model Laplacian `tridiag(-1, 2, -1)` is positive definite: its
eigenvalues are `2 - 2 cos θ_k = 4 sin²(θ_k / 2)`, which lie in `(0, 4)`.  Its diagonal
dominance is not strict, so what does the work is `cos(π/(n+1)) < 1`. -/
theorem posDef_symmTridiagonalToeplitz_neg_one_two (n : ℕ) :
    (symmTridiagonalToeplitz n (-1) 2).PosDef := by
  rw [posDef_iff_isSymmetricCoercive]
  refine (isSymmetricBoundedBy_symmTridiagonalToeplitz n (-1) 2).isSymmetricCoercive ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hhalf : 0 < Real.sin (π / (2 * ((n : ℝ) + 1))) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (π / ((n : ℝ) + 1)) = 1 - 2 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
    rw [← Real.cos_two_mul_eq_one_sub]
    congr 1
    field_simp
  rw [hcos]
  simp only [abs_neg, abs_one]
  nlinarith [hhalf]

end Matrix
