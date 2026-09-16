/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside `Mathlib.LinearAlgebra.Matrix.Circulant`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.MMatrix

/-!
# The symmetric tridiagonal Toeplitz matrix and its discrete sine eigenbasis

`Matrix.symmTridiagonalToeplitz n a b` is `tridiag(a, b, a)`: the `n × n` real matrix with `b` on
the diagonal and `a` on both off-diagonals.  It is diagonalized, for every `a` and `b` at once, by
the **discrete sine vectors** `Matrix.sineVec n k`, whose `j`-th entry is `sin((j + 1)(k + 1)π / (n
+ 1))`, with eigenvalue `b + 2 a cos((k + 1)π / (n + 1))`.

The whole content is the trigonometric identity `sin((j - 1)θ) + sin((j + 1)θ) = 2 cos θ sin(jθ)`,
applied at `θ_k = (k + 1)π / (n + 1)`.  The first and last rows of the matrix are the same identity
with the missing neighbour supplied by the boundary values `sin 0 = 0` and `sin((n + 1)θ_k) = 0`,
which is exactly why the sine vectors are the eigenvectors of a *tridiagonal* Toeplitz matrix.

Everything else follows: the sine vectors are pairwise orthogonal, of squared length `(n + 1) / 2`
(`Matrix.dotProduct_sineVec`), so after the normalization `√(2 / (n + 1))` they form an orthonormal
basis (`Matrix.sineOrthonormalBasis`); the spectrum consists of exactly the `n` numbers `b + 2 a cos
θ_k` (`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff`); the quadratic form is enclosed in `[b -
2|a| cos(π/(n+1)), b + 2|a| cos(π/(n+1))]` (`Matrix.isSymmetricBoundedBy_symmTridiagonalToeplitz`);
and `tridiag(-1, 2, -1)`, whose eigenvalues are `4 sin²((k + 1)π / (2(n + 1)))`, is positive
definite. For that model Laplacian the module also gives the explicit inverse — the discrete
Green's function `(min(j, k) + 1)(n - max(j, k)) / (n + 1)`
(`Matrix.inv_symmTridiagonalToeplitz_neg_one_two_apply`) — with its row sums, the discrete
parabola `(j + 1)(n - j) / 2`; its M-matrix property
(`Matrix.isMMatrix_symmTridiagonalToeplitz_neg_one_two`); and its spectral condition number
`cot²(π / (2(n + 1)))` (`Matrix.condNumber_symmTridiagonalToeplitz_neg_one_two`).

`Matrix.tridiagonalToeplitz n a b c` is the general `tridiag(a, b, c)`, with possibly different
off-diagonals. When they have the same sign, `a c ≥ 0`, the diagonal similarity `diag(1, d, d², …)`
with `d² = a / c` turns it into a symmetric one whose off-diagonal squares to `a c`, so its
eigenvalues are again a cosine family, `b + 2 √(a c) cos((k + 1)π / (n + 1))`
(`Matrix.tridiagonalToeplitz_hasEigenvalue_iff`). A sign in the off-diagonal only reflects the
family, `k ↦ n - 1 - k`, and the degenerate case `a c = 0` is a triangular matrix whose only
eigenvalue is `b` — which the same formula gives.

This is the model problem of [saad2003iterative], §2.2.3 and §2.2.6, and of [kress1998numerical],
§4. The module knows nothing about differential equations: the claim that these matrices discretize
`-u''` belongs to a textbook surface, and the two-dimensional five-point Laplacian is the Kronecker
sum of two of them, in `Numlib.LinearAlgebra.Matrix.KroneckerSum`.
-/

open Finset
open scoped Real Matrix

namespace Matrix

variable {n : ℕ} (a b : ℝ)

/-! ### The matrix -/

/-- The symmetric tridiagonal Toeplitz matrix `tridiag(a, b, a)`: `b` on the diagonal, `a` on both
off-diagonals and `0` elsewhere. -/
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

/-- A symmetric tridiagonal Toeplitz matrix is tridiagonal in the sense of `Matrix.IsTridiagonal`.
-/
theorem symmTridiagonalToeplitz_isTridiagonal :
    (symmTridiagonalToeplitz n a b).IsTridiagonal := by
  rintro i j (⟨k, hjk, hki⟩ | ⟨k, hik, hkj⟩)
  · exact symmTridiagonalToeplitz_apply_of_one_lt a b
      (Or.inr (by have h1 : (j : ℕ) < k := hjk; have h2 : (k : ℕ) < i := hki; omega))
  · exact symmTridiagonalToeplitz_apply_of_one_lt a b
      (Or.inl (by have h1 : (i : ℕ) < k := hik; have h2 : (k : ℕ) < j := hkj; omega))

/-! ### The action on a vector -/

/-- A vector on `Fin n`, shifted up by one and extended by zero to all of `ℕ`.  It turns the
three-term row of a tridiagonal matrix into a uniform formula: the missing neighbours at the first
and last rows are supplied by the padding. -/
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

/-- The three-term row of a symmetric tridiagonal Toeplitz matrix, uniformly across the first, the
last and the interior rows. -/
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

/-- The `k`-th discrete sine vector on `Fin n`, `j ↦ sin((j + 1)(k + 1)π / (n + 1))`: an eigenvector
of every `Matrix.symmTridiagonalToeplitz n a b`. -/
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

/-- The angle `θ_k = (k + 1)π / (n + 1)` is below `π`, which is why the `n` eigenvalues `b + 2 a cos
θ_k` are distinct. -/
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

/-- The eigenpairs of the symmetric tridiagonal Toeplitz matrix: the `k`-th discrete sine vector is
an eigenvector with eigenvalue `b + 2 a cos((k + 1)π / (n + 1))`, for every `a` and `b` at once.
Row by row this is `sin((j - 1)θ) + sin((j + 1)θ) = 2 cos θ sin(jθ)`, the first and last rows
included thanks to `sin 0 = 0` and `sin((n + 1)θ_k) = 0`. -/
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

/-- The telescoping identity `2 sin φ ∑_{j<M} cos(2(j+1)φ) = sin((2M+1)φ) - sin φ`, from `sin(x + φ)
- sin(x - φ) = 2 cos x sin φ`. -/
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

/-- The cosine sum at a sine-basis angle: `∑_{j<n} cos(2(j+1)θ_k) = -1`, because `sin((2n+1)θ_k) =
-sin θ_k`. -/
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

/-- Orthogonality of the discrete sine basis: `sineVec n k ⬝ᵥ sineVec n l = if k = l then (n + 1) /
2 else 0`.  Off the diagonal this is the orthogonality of eigenvectors of the symmetric matrix
`tridiag(1, 0, 1)` belonging to the distinct eigenvalues `2 cos θ_k`; on the diagonal it is a
telescoping cosine sum. -/
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

/-- The inner product of two discrete sine vectors, in the `EuclideanSpace` form that the spectral
statements need. -/
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

/-- The normalized discrete sine vectors as an orthonormal basis of `EuclideanSpace ℝ (Fin n)`. It
diagonalizes every `Matrix.symmTridiagonalToeplitz n a b` at once: the symmetric tridiagonal
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

/-- The sine basis exhausts the spectrum: the eigenvalues of `tridiag(a, b, a)` are exactly the `n`
numbers `b + 2 a cos((k + 1)π / (n + 1))`. -/
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

/-- The quadratic-form bounds of `tridiag(a, b, a)` from bounds on its eigenvalues, through the sine
eigenbasis.  This is the shape in which every convergence estimate consumes the spectrum of the
model problem: no eigenvalue is ever named. -/
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

/-- The spectrum of `tridiag(a, b, a)` in quadratic-form form: it is enclosed in `[b - 2|a|
cos(π/(n+1)), b + 2|a| cos(π/(n+1))]`, and both ends are attained, at `k = n - 1` and at `k = 0`.
This is the sharp version of the crude bound `[b - 2|a|, b + 2|a|]`, and it is what makes the
condition number of the model problem grow like `(n + 1)²`. -/
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

/-- `tridiag(a, b, a)` is positive definite when the diagonal dominates strictly, `2|a| < b`. The
boundary case `2|a| = b`, which is the model Laplacian `tridiag(-1, 2, -1)`, needs the sharp cosine
bound instead: see `Matrix.posDef_symmTridiagonalToeplitz_neg_one_two`. -/
theorem posDef_symmTridiagonalToeplitz (n : ℕ) {a b : ℝ} (h : 2 * |a| < b) :
    (symmTridiagonalToeplitz n a b).PosDef := by
  rw [posDef_iff_isSymmetricCoercive]
  refine (isSymmetricBoundedBy_symmTridiagonalToeplitz n a b).isSymmetricCoercive ?_
  nlinarith [Real.cos_le_one (π / ((n : ℝ) + 1)), abs_nonneg a]

/-- The one-dimensional model Laplacian `tridiag(-1, 2, -1)` is positive definite: its eigenvalues
are `2 - 2 cos θ_k = 4 sin²(θ_k / 2)`, which lie in `(0, 4)`.  Its diagonal dominance is not strict,
so what does the work is `cos(π/(n+1)) < 1`. -/
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

/-! ### The model Laplacian `tridiag(-1, 2, -1)`: inverse, comparison vector, M-matrix, conditioning

The matrix `T = tridiag(-1, 2, -1)` has the explicit inverse
`T⁻¹ j k = (min(j, k) + 1)(n - max(j, k)) / (n + 1)`, the discrete Green's function of `-u'' = f`
with homogeneous Dirichlet data: with `x_j = (j + 1) / (n + 1)` it is `(n + 1) G(x_j, x_k)` for
`G(x, s) = min(x, s)(1 - max(x, s))`. Its row sums are the discrete parabola `(j + 1)(n - j) / 2`,
which is the *comparison vector* `w` with `T w = 1` that the stability estimate
`Matrix.IsMMatrix.norm_inv_mulVec_le` consumes. `T` is an M-matrix, by positive definiteness, and
its spectral condition number is `cot²(π / (2(n + 1)))`, of order `(n + 1)²`. -/

section NegOneTwo

/-- The three-term row of `tridiag(-1, 2, -1)` applied to `v`, in padded form. -/
private theorem neg_one_two_mulVec_apply (v : Fin n → ℝ) (i : Fin n) :
    (symmTridiagonalToeplitz n (-1) 2 *ᵥ v) i
      = 2 * padZero v ((i : ℕ) + 1) - padZero v (i : ℕ) - padZero v ((i : ℕ) + 2) := by
  rw [symmTridiagonalToeplitz_mulVec_apply]
  ring

/-- The padded discrete parabola `m ↦ m (n + 1 - m) / 2`, which vanishes at both ends `m = 0` and
`m = n + 1`. -/
private theorem padZero_parabola {m : ℕ} (hm : m ≤ n + 1) :
    padZero (fun j : Fin n => (((j : ℕ) : ℝ) + 1) * ((n : ℝ) - (j : ℕ)) / 2) m
      = (m : ℝ) * ((n : ℝ) + 1 - m) / 2 := by
  cases m with
  | zero => simp [padZero_zero]
  | succ m =>
    rw [padZero_succ]
    by_cases h : m < n
    · rw [dite_eq_left h]
      push_cast
      ring
    · rw [dite_eq_right h]
      have hmn : m = n := by omega
      subst hmn
      push_cast
      ring

/-- **The comparison vector of the model Laplacian**: `tridiag(-1, 2, -1)` maps the discrete
parabola `w_j = (j + 1)(n - j) / 2` to the all-ones vector, because the second difference of a
quadratic sequence is constant and the parabola vanishes at the padded ends `j = -1` and `j = n`.
With `x_j = (j + 1) h`, `h = 1 / (n + 1)`, this is `h⁻² · x_j (1 - x_j) / 2`, the function
[quarteroni2000numerical] Exercise 12.7 exhibits (`T_h 1 (x_j) = x_j (1 - x_j) / 2`), and it is
the vector `w` of `Matrix.IsMMatrix.norm_inv_mulVec_le` for the two-point boundary value problem.
-/
theorem symmTridiagonalToeplitz_neg_one_two_mulVec_parabola (n : ℕ) :
    symmTridiagonalToeplitz n (-1) 2
      *ᵥ (fun j : Fin n => (((j : ℕ) : ℝ) + 1) * ((n : ℝ) - (j : ℕ)) / 2) = 1 := by
  funext i
  have hi : (i : ℕ) + 2 ≤ n + 1 := by omega
  rw [neg_one_two_mulVec_apply, padZero_parabola (by omega), padZero_parabola (by omega),
    padZero_parabola hi, Pi.one_apply]
  push_cast
  ring

/-- The candidate inverse of `tridiag(-1, 2, -1)`: the discrete Green's function
`(min(j, k) + 1)(n - max(j, k)) / (n + 1)`. -/
private noncomputable def negOneTwoInv (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun j k =>
    (((min (j : ℕ) k : ℕ) : ℝ) + 1) * ((n : ℝ) - (max (j : ℕ) k : ℕ)) / ((n : ℝ) + 1)

/-- The `k`-th column of the Green's function, padded and scaled by `n + 1`, in the piecewise-affine
form `m ↦ m (n - k)` for `m ≤ k + 1` and `m ↦ (k + 1)(n + 1 - m)` beyond: affine on each side of
`m = k + 1`, and vanishing at the ends `m = 0` and `m = n + 1`. -/
private theorem padZero_negOneTwoInv_col (k : Fin n) {m : ℕ} (hm : m ≤ n + 1) :
    padZero (fun j => negOneTwoInv n j k) m
      = (if m ≤ (k : ℕ) + 1 then (m : ℝ) * ((n : ℝ) - (k : ℕ))
          else (((k : ℕ) : ℝ) + 1) * ((n : ℝ) + 1 - m)) / ((n : ℝ) + 1) := by
  cases m with
  | zero => simp [padZero_zero]
  | succ m =>
    rw [padZero_succ]
    by_cases h : m < n
    · rw [dite_eq_left h]
      simp only [negOneTwoInv, of_apply]
      rcases le_or_gt m k with hmk | hmk
      · rw [min_eq_left hmk, max_eq_right hmk, ite_eq_left (by omega)]
        push_cast
        ring
      · rw [min_eq_right hmk.le, max_eq_left hmk.le, ite_eq_right (by omega)]
        push_cast
        ring
    · rw [dite_eq_right h]
      have hmn : m = n := by omega
      subst hmn
      rw [ite_eq_right (by have := k.isLt; omega)]
      push_cast
      ring

/-- `tridiag(-1, 2, -1)` times the Green's function is the identity: column by column, the second
difference of the piecewise-affine column `k` vanishes off `j = k` and is `n + 1` there. -/
private theorem symmTridiagonalToeplitz_neg_one_two_mul_negOneTwoInv (n : ℕ) :
    symmTridiagonalToeplitz n (-1) 2 * negOneTwoInv n = 1 := by
  ext i k
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hi : (i : ℕ) + 2 ≤ n + 1 := by omega
  change (symmTridiagonalToeplitz n (-1) 2 *ᵥ fun j => negOneTwoInv n j k) i = _
  rw [neg_one_two_mulVec_apply, padZero_negOneTwoInv_col k (by omega),
    padZero_negOneTwoInv_col k (by omega), padZero_negOneTwoInv_col k hi, one_apply]
  rcases lt_trichotomy (i : ℕ) k with hik | hik | hik
  · have hne : i ≠ k := fun h => by rw [h] at hik; exact lt_irrefl _ hik
    have h1 : (i : ℕ) + 1 ≤ k + 1 := by omega
    have h2 : (i : ℕ) ≤ k + 1 := by omega
    have h3 : (i : ℕ) + 2 ≤ k + 1 := by omega
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, ite_eq_right hne]
    push_cast
    ring
  · obtain rfl : i = k := Fin.ext hik
    have h1 : (i : ℕ) + 1 ≤ i + 1 := le_rfl
    have h2 : (i : ℕ) ≤ i + 1 := by omega
    have h3 : ¬ ((i : ℕ) + 2 ≤ i + 1) := by omega
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3, ite_eq_left rfl]
    field_simp
    push_cast
    ring
  · have hne : i ≠ k := fun h => by rw [h] at hik; exact lt_irrefl _ hik
    have h1 : ¬ ((i : ℕ) + 1 ≤ k + 1) := by omega
    have h3 : ¬ ((i : ℕ) + 2 ≤ k + 1) := by omega
    rw [ite_eq_right h1, ite_eq_right h3, ite_eq_right hne]
    -- at `i = k + 1` the two affine pieces agree, so the row `i` may use either
    rcases eq_or_ne (i : ℕ) (k + 1) with h2 | h2
    · rw [ite_eq_left h2.le, h2]
      push_cast
      ring
    · rw [ite_eq_right (by omega)]
      push_cast
      ring

/-- **The inverse of the model Laplacian**: `tridiag(-1, 2, -1)⁻¹ j k = (min(j, k) + 1)(n - max(j,
k)) / (n + 1)`. With `x_j = (j + 1) / (n + 1)` this is `(n + 1) G(x_j, x_k)` for the Green's
function `G(x, s) = min(x, s)(1 - max(x, s))` of `-u'' = f` on `(0, 1)` with homogeneous Dirichlet
data — the discrete Green's function of [quarteroni2000numerical] Exercise 12.6 (`G^k(x_j) = h
G(x_j, x_k)`, with `L_h = h⁻² T`). -/
theorem inv_symmTridiagonalToeplitz_neg_one_two_apply (j k : Fin n) :
    (symmTridiagonalToeplitz n (-1) 2)⁻¹ j k
      = (((min (j : ℕ) k : ℕ) : ℝ) + 1) * ((n : ℝ) - (max (j : ℕ) k : ℕ)) / ((n : ℝ) + 1) := by
  rw [inv_eq_right_inv (symmTridiagonalToeplitz_neg_one_two_mul_negOneTwoInv n)]
  rfl

/-- The model Laplacian is nonsingular. -/
theorem isUnit_symmTridiagonalToeplitz_neg_one_two (n : ℕ) :
    IsUnit (symmTridiagonalToeplitz n (-1) 2) :=
  ⟨⟨_, negOneTwoInv n, symmTridiagonalToeplitz_neg_one_two_mul_negOneTwoInv n,
    mul_eq_one_comm.1 (symmTridiagonalToeplitz_neg_one_two_mul_negOneTwoInv n)⟩, rfl⟩

/-- The row sums of the inverse of the model Laplacian are the discrete parabola:
`∑_k tridiag(-1, 2, -1)⁻¹ j k = (j + 1)(n - j) / 2`. This is `T⁻¹ 1 = w` for the comparison vector
`w` of `Matrix.symmTridiagonalToeplitz_neg_one_two_mulVec_parabola`; it bounds the discrete Green's
function sum of [quarteroni2000numerical] Theorem 12.1 by `(n + 1)² / 8`. -/
theorem inv_symmTridiagonalToeplitz_neg_one_two_sum (j : Fin n) :
    ∑ k, (symmTridiagonalToeplitz n (-1) 2)⁻¹ j k
      = (((j : ℕ) : ℝ) + 1) * ((n : ℝ) - (j : ℕ)) / 2 := by
  have hdet : IsUnit (symmTridiagonalToeplitz n (-1) 2).det :=
    (isUnit_iff_isUnit_det _).1 (isUnit_symmTridiagonalToeplitz_neg_one_two n)
  have h : (symmTridiagonalToeplitz n (-1) 2)⁻¹ *ᵥ (1 : Fin n → ℝ)
      = fun j : Fin n => (((j : ℕ) : ℝ) + 1) * ((n : ℝ) - (j : ℕ)) / 2 := by
    rw [← symmTridiagonalToeplitz_neg_one_two_mulVec_parabola n, mulVec_mulVec,
      nonsing_inv_mul _ hdet, one_mulVec]
  have h' := congrFun h j
  simpa [mulVec_apply_eq_sum] using h'

/-- The off-diagonal entries of `tridiag(a, b, a)` are nonpositive when `a ≤ 0`. -/
theorem symmTridiagonalToeplitz_offDiag_nonpos {a : ℝ} (ha : a ≤ 0) (b : ℝ) {i j : Fin n}
    (hij : i ≠ j) : symmTridiagonalToeplitz n a b i j ≤ 0 := by
  rw [symmTridiagonalToeplitz_apply, ite_eq_right hij]
  split_ifs
  · exact ha
  · exact le_rfl

/-- **Diagonally dominant symmetric tridiagonal Toeplitz matrices with nonpositive off-diagonals
are M-matrices**: `tridiag(a, b, a)` with `a ≤ 0` and `2|a| < b`, through positive definiteness
(`Matrix.posDef_symmTridiagonalToeplitz`) and the Stieltjes criterion
`Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos`. -/
theorem isMMatrix_symmTridiagonalToeplitz (n : ℕ) {a b : ℝ} (h : 2 * |a| < b) (ha : a ≤ 0) :
    (symmTridiagonalToeplitz n a b).IsMMatrix :=
  IsMMatrix.of_posDef_of_offDiag_nonpos (posDef_symmTridiagonalToeplitz n h)
    fun _ _ hij => symmTridiagonalToeplitz_offDiag_nonpos ha b hij

/-- **The model Laplacian is an M-matrix** ([quarteroni2000numerical] Exercise 12.2): it is
positive definite with nonpositive off-diagonal entries. The explicit inverse
`Matrix.inv_symmTridiagonalToeplitz_neg_one_two_apply` is visibly nonnegative as well; the book's
hint, continuity of the inverse of `T + αI` in `α`, is needed by neither route. -/
theorem isMMatrix_symmTridiagonalToeplitz_neg_one_two (n : ℕ) :
    (symmTridiagonalToeplitz n (-1) 2).IsMMatrix :=
  IsMMatrix.of_posDef_of_offDiag_nonpos (posDef_symmTridiagonalToeplitz_neg_one_two n)
    fun _ _ hij => symmTridiagonalToeplitz_offDiag_nonpos (by norm_num) 2 hij

section SpectralNorm

open scoped Matrix.Norms.L2Operator

/-- The half-angle `π / (2(n + 1))` of the model problem has positive sine. -/
private theorem sin_half_angle_pos (n : ℕ) : 0 < Real.sin (π / (2 * ((n : ℝ) + 1))) := by
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- The half-angle `π / (2(n + 1))` of the model problem has nonnegative cosine (it vanishes at
`n = 0`). -/
private theorem cos_half_angle_nonneg (n : ℕ) : 0 ≤ Real.cos (π / (2 * ((n : ℝ) + 1))) := by
  refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · have : 0 < π / (2 * ((n : ℝ) + 1)) := by positivity
    linarith [Real.pi_pos]
  · rw [div_le_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- `1 + cos(π / (n + 1)) = 2 cos²(π / (2(n + 1)))`. -/
private theorem one_add_cos_angle (n : ℕ) :
    1 + Real.cos (π / ((n : ℝ) + 1)) = 2 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  have h : π / ((n : ℝ) + 1) = 2 * (π / (2 * ((n : ℝ) + 1))) := by
    field_simp
  rw [h, Real.cos_sq]
  ring

/-- `1 - cos(π / (n + 1)) = 2 sin²(π / (2(n + 1)))`. -/
private theorem one_sub_cos_angle (n : ℕ) :
    1 - Real.cos (π / ((n : ℝ) + 1)) = 2 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  have h : π / ((n : ℝ) + 1) = 2 * (π / (2 * ((n : ℝ) + 1))) := by
    field_simp
  rw [h, Real.cos_two_mul, Real.cos_sq']
  ring

/-- Every eigenvalue of the model Laplacian lies in `[4 sin²(π/(2(n+1))), 4 cos²(π/(2(n+1)))]`. -/
private theorem eigenvalue_neg_one_two_mem_Icc {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (toEuclideanLin (symmTridiagonalToeplitz n (-1) 2)) μ) :
    μ ∈ Set.Icc (4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2)
      (4 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2) := by
  have h := (isSymmetricBoundedBy_symmTridiagonalToeplitz n (-1) 2).re_mem_Icc_of_hasEigenvalue hμ
  rw [RCLike.re_to_real] at h
  simp only [abs_neg, abs_one] at h
  exact ⟨by linarith [h.1, one_sub_cos_angle n], by linarith [h.2, one_add_cos_angle n]⟩

/-- **The spectral norm of the model Laplacian**: `‖tridiag(-1, 2, -1)‖₂ = 4 cos²(π / (2(n + 1)))`,
its largest eigenvalue, attained by the last discrete sine vector. -/
theorem l2_opNorm_symmTridiagonalToeplitz_neg_one_two (hn : 0 < n) :
    ‖symmTridiagonalToeplitz n (-1) 2‖ = 4 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  refine (symmTridiagonalToeplitz_isHermitian (-1) 2).l2_opNorm_eq (fun μ hμ => ?_) ?_
  · rw [RCLike.re_to_real]
    have h := eigenvalue_neg_one_two_mem_Icc hμ
    rw [abs_le]
    constructor <;> nlinarith [h.1, h.2, sq_nonneg (Real.sin (π / (2 * ((n : ℝ) + 1))))]
  · refine ⟨_, (symmTridiagonalToeplitz_hasEigenvalue_iff (-1) 2 _).2 ⟨⟨n - 1, by omega⟩, rfl⟩, ?_⟩
    rw [RCLike.re_to_real]
    have hcast : ((((⟨n - 1, by omega⟩ : Fin n) : ℕ) : ℝ) + 1) = (n : ℝ) := by
      rw [Fin.val_mk, Nat.cast_sub hn, Nat.cast_one]
      ring
    have hrw : ((((⟨n - 1, by omega⟩ : Fin n) : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)
        = π - π / ((n : ℝ) + 1) := by
      rw [hcast]
      field_simp
      ring
    have hnn : 0 ≤ 2 + 2 * -1 * -Real.cos (π / ((n : ℝ) + 1)) := by
      nlinarith [one_add_cos_angle n, sq_nonneg (Real.cos (π / (2 * ((n : ℝ) + 1))))]
    rw [hrw, Real.cos_pi_sub, abs_of_nonneg hnn]
    linarith [one_add_cos_angle n]

/-- **The spectral norm of the inverse of the model Laplacian**: `‖tridiag(-1, 2, -1)⁻¹‖₂ = 1 / (4
sin²(π / (2(n + 1))))`, the reciprocal of its smallest eigenvalue, attained by the first discrete
sine vector. -/
theorem l2_opNorm_inv_symmTridiagonalToeplitz_neg_one_two (hn : 0 < n) :
    ‖(symmTridiagonalToeplitz n (-1) 2)⁻¹‖ = (4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2)⁻¹ := by
  have hpos : 0 < 4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
    have := sin_half_angle_pos n
    positivity
  refine (symmTridiagonalToeplitz_isHermitian (-1) 2).l2_opNorm_inv_eq hpos (fun μ hμ => ?_) ?_
  · rw [RCLike.re_to_real]
    exact (eigenvalue_neg_one_two_mem_Icc hμ).1.trans (le_abs_self μ)
  · refine ⟨_, (symmTridiagonalToeplitz_hasEigenvalue_iff (-1) 2 _).2 ⟨⟨0, hn⟩, rfl⟩, ?_⟩
    rw [RCLike.re_to_real]
    simp only [Nat.cast_zero, zero_add, one_mul]
    have hnn : 0 ≤ 2 + 2 * -1 * Real.cos (π / ((n : ℝ) + 1)) := by
      nlinarith [one_sub_cos_angle n, sq_nonneg (Real.sin (π / (2 * ((n : ℝ) + 1))))]
    rw [abs_of_nonneg hnn]
    linarith [one_sub_cos_angle n]

/-- **The spectral condition number of the model Laplacian**: `‖T‖₂ ‖T⁻¹‖₂ = cot²(π / (2(n + 1)))`
for `T = tridiag(-1, 2, -1)`, the ratio of its extreme eigenvalues `4 cos²(π/(2(n+1)))` and `4
sin²(π/(2(n+1)))`. This is the `K₂ = O(h⁻²)` of [quarteroni2000numerical] §12.4.5 for the model
stiffness matrix `h⁻¹ T` (the scaling cancels), and the growth `(n + 1)²` that motivates
preconditioning. On no indices both norms and `cot(π / 2)` vanish, so the identity holds for every
`n`. -/
theorem condNumber_symmTridiagonalToeplitz_neg_one_two (n : ℕ) :
    ‖symmTridiagonalToeplitz n (-1) 2‖ * ‖(symmTridiagonalToeplitz n (-1) 2)⁻¹‖
      = Real.cot (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : symmTridiagonalToeplitz 0 (-1) 2 = 0 := Subsingleton.elim _ _
    rw [h0, inv_zero, norm_zero, zero_mul, Real.cot_eq_cos_div_sin]
    norm_num
  · rw [l2_opNorm_symmTridiagonalToeplitz_neg_one_two hn,
      l2_opNorm_inv_symmTridiagonalToeplitz_neg_one_two hn, Real.cot_eq_cos_div_sin, div_pow]
    have := sin_half_angle_pos n
    field_simp

/-- The spectral condition number of the model Laplacian is at most `(2(n + 1) / π)²`: `cot x ≤
1/x` on `(0, π/2)`, since `x < tan x` there. -/
theorem condNumber_symmTridiagonalToeplitz_neg_one_two_le (n : ℕ) :
    ‖symmTridiagonalToeplitz n (-1) 2‖ * ‖(symmTridiagonalToeplitz n (-1) 2)⁻¹‖
      ≤ (2 * ((n : ℝ) + 1) / π) ^ 2 := by
  rw [condNumber_symmTridiagonalToeplitz_neg_one_two]
  have h0 : 0 ≤ Real.cot (π / (2 * ((n : ℝ) + 1))) := by
    rw [Real.cot_eq_cos_div_sin]
    exact div_nonneg (cos_half_angle_nonneg n) (sin_half_angle_pos n).le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_add, mul_one]
    rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, zero_div, zero_pow two_ne_zero]
    positivity
  have hx : 0 < π / (2 * ((n : ℝ) + 1)) := by positivity
  have hlt : π / (2 * ((n : ℝ) + 1)) < π / 2 := by
    rw [div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have htan := Real.lt_tan hx hlt
  have hcot : Real.cot (π / (2 * ((n : ℝ) + 1))) = (Real.tan (π / (2 * ((n : ℝ) + 1))))⁻¹ := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, inv_div]
  have hinv : (2 * ((n : ℝ) + 1) / π) = (π / (2 * ((n : ℝ) + 1)))⁻¹ := by rw [inv_div]
  rw [hcot] at h0 ⊢
  rw [hinv]
  exact pow_le_pow_left₀ h0 (inv_anti₀ hx htan.le) 2

end SpectralNorm

end NegOneTwo

/-! ### The general tridiagonal Toeplitz matrix

A tridiagonal Toeplitz matrix with off-diagonals of the *same sign* is a diagonal similarity away
from a symmetric one, so its spectrum is again a cosine family.  The similarity is
`diag(1, d, d², …)` with `d² = a / c`, which turns the pair `(a, c)` of off-diagonals into the
constant `c d`, whose square is `a c`. -/

section General

variable (c : ℝ)

/-- The tridiagonal Toeplitz matrix `tridiag(a, b, c)`: `b` on the diagonal, `a` on the
subdiagonal, `c` on the superdiagonal and `0` elsewhere.  `Matrix.symmTridiagonalToeplitz n a b` is
the case `c = a`. -/
def tridiagonalToeplitz (n : ℕ) (a b c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then b else if (j : ℕ) + 1 = i then a else if (i : ℕ) + 1 = j then c else 0

/-- The entries of `tridiag(a, b, c)`. -/
theorem tridiagonalToeplitz_apply (i j : Fin n) :
    tridiagonalToeplitz n a b c i j =
      if (i : ℕ) = j then b else if (j : ℕ) + 1 = i then a else
        if (i : ℕ) + 1 = j then c else 0 := rfl

/-- The symmetric tridiagonal Toeplitz matrix is the case of equal off-diagonals. -/
theorem symmTridiagonalToeplitz_eq_tridiagonalToeplitz (n : ℕ) (a b : ℝ) :
    symmTridiagonalToeplitz n a b = tridiagonalToeplitz n a b a := by
  ext i j
  rw [symmTridiagonalToeplitz_apply', tridiagonalToeplitz_apply]
  split_ifs with h1 h2 h3 h4 <;> first | rfl | omega

/-- The constant-coefficient tridiagonal matrix is the variable-coefficient
`Matrix.tridiagonalOf` of `Numlib/LinearAlgebra/Matrix/Hessenberg` with constant bands, so that
its API (products, bandwidths, `mulVec`) applies to `tridiag(β, δ, γ)`. -/
theorem tridiagonalToeplitz_eq_tridiagonalOf (N : ℕ) (β δ γ : ℝ) :
    tridiagonalToeplitz (N + 1) β δ γ = tridiagonalOf (fun _ => β) (fun _ => δ) fun _ => γ := by
  ext i j
  simp only [tridiagonalToeplitz_apply, tridiagonalOf, of_apply]
  split_ifs <;> first | rfl | omega

/-- Transposition exchanges the two off-diagonals. -/
theorem tridiagonalToeplitz_transpose (n : ℕ) (a b c : ℝ) :
    (tridiagonalToeplitz n a b c)ᵀ = tridiagonalToeplitz n c b a := by
  ext i j
  rw [transpose_apply, tridiagonalToeplitz_apply, tridiagonalToeplitz_apply]
  split_ifs <;> first | rfl | omega

/-- `diag(1, d, d², …)` as a unit of the matrix ring, for `d ≠ 0`. -/
private noncomputable def diagPowUnit (n : ℕ) {d : ℝ} (hd : d ≠ 0) :
    (Matrix (Fin n) (Fin n) ℝ)ˣ where
  val := diagonal fun i : Fin n => d ^ (i : ℕ)
  inv := diagonal fun i : Fin n => (d ^ (i : ℕ))⁻¹
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp [mul_inv_cancel₀ (pow_ne_zero (i : ℕ) hd)]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp [inv_mul_cancel₀ (pow_ne_zero (i : ℕ) hd)]

/-- The symmetrizing similarity: with `d² = a / c`, `tridiag(a, b, c) · diag(1, d, d², …)` and
`diag(1, d, d², …) · tridiag(c d, b, c d)` agree.  The scaling multiplies the superdiagonal by `d`
and divides the subdiagonal by `d`, and `d² = a / c` is exactly what makes the two results equal. -/
private theorem tridiagonalToeplitz_mul_diagonal_pow (n : ℕ) (a b c d : ℝ) (hc : c ≠ 0)
    (hd : d ^ 2 = a / c) :
    tridiagonalToeplitz n a b c * diagonal (fun i : Fin n => d ^ (i : ℕ))
      = diagonal (fun i : Fin n => d ^ (i : ℕ)) * symmTridiagonalToeplitz n (c * d) b := by
  have hac : c * d ^ 2 = a := by rw [hd]; field_simp
  ext i j
  rw [mul_diagonal, diagonal_mul, tridiagonalToeplitz_apply, symmTridiagonalToeplitz_apply']
  by_cases h1 : (i : ℕ) = j
  · rw [ite_eq_left h1, ite_eq_left h1, h1]
    ring
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h2 : (j : ℕ) + 1 = i
  · rw [ite_eq_left h2, ite_eq_left (Or.inr h2), ← h2, pow_succ]
    rw [← hac]
    ring
  rw [ite_eq_right h2]
  by_cases h3 : (i : ℕ) + 1 = j
  · rw [ite_eq_left h3, ite_eq_left (Or.inl h3), ← h3, pow_succ]
    ring
  · rw [ite_eq_right h3, ite_eq_right (by tauto)]
    ring

/-- Reflecting the index `k ↦ n - 1 - k` negates `cos((k + 1)π/(n + 1))`, so the cosine family is
unchanged when the amplitude changes sign. -/
private theorem exists_eq_add_cos_neg_iff (n : ℕ) (b t μ : ℝ) :
    (∃ k : Fin n, μ = b + 2 * (-t) * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))) ↔
      ∃ k : Fin n, μ = b + 2 * t * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hcos : ∀ k : Fin n, Real.cos ((((k.rev : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))
      = -Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) := by
    intro k
    have hval : ((k.rev : ℕ) : ℝ) + 1 = ((n : ℝ) + 1) - (((k : ℕ) : ℝ) + 1) := by
      have hle : (k : ℕ) + 1 ≤ n := k.isLt
      rw [Fin.val_rev, Nat.cast_sub hle]
      push_cast
      ring
    rw [hval, ← Real.cos_pi_sub]
    congr 1
    field_simp
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.rev, by rw [hcos]; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k.rev, by rw [hcos]; ring⟩

/-- A tridiagonal Toeplitz matrix with a vanishing superdiagonal is lower triangular, so its
spectrum is the single diagonal entry (and is empty for `n = 0`). -/
private theorem mem_spectrum_tridiagonalToeplitz_super_zero (n : ℕ) (a b μ : ℝ) :
    μ ∈ spectrum ℝ (tridiagonalToeplitz n a b 0) ↔ ∃ _k : Fin n, μ = b := by
  set M : Matrix (Fin n) (Fin n) ℝ :=
    algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) μ - tridiagonalToeplitz n a b 0 with hM
  have hentry : ∀ i j : Fin n, M i j
      = (if i = j then μ else 0) - tridiagonalToeplitz n a b 0 i j := by
    intro i j
    rw [hM, sub_apply, algebraMap_matrix_apply]
    simp
  have hlow : M.IsLowerTriangular := by
    intro i j hij
    rw [OrderDual.toDual_lt_toDual] at hij
    have hne : ¬ (i = j) := ne_of_lt hij
    have hne' : ¬ ((i : ℕ) = j) := fun h => hne (Fin.ext h)
    rw [hentry, ite_eq_right hne, tridiagonalToeplitz_apply, ite_eq_right hne',
      ite_eq_right (by omega)]
    split_ifs <;> ring
  have hdiag : ∀ i : Fin n, M i i = μ - b := by
    intro i
    rw [hentry, ite_eq_left rfl, tridiagonalToeplitz_apply, ite_eq_left rfl]
  have hdet : M.det = (μ - b) ^ n := by
    rw [det_of_isLowerTriangular M hlow]
    simp [hdiag]
  rw [spectrum.mem_iff, ← hM, Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero, not_not,
    pow_eq_zero_iff', sub_eq_zero]
  constructor
  · rintro ⟨hμ, hn⟩
    exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩, hμ⟩
  · rintro ⟨k, hμ⟩
    exact ⟨hμ, by have := k.isLt; omega⟩

/-- **The spectrum of a tridiagonal Toeplitz matrix** whose two off-diagonals have the same sign:
the eigenvalues of `tridiag(a, b, c)` with `a c ≥ 0` are the `n` numbers
`b + 2 √(a c) cos((k + 1)π/(n + 1))`.

For `a c > 0` the matrix is `diag(1, d, d², …)`-similar to `tridiag(√(ac), b, √(ac))` up to a sign
in the off-diagonal, and a sign there only reflects the cosine family; for `a c = 0` the matrix is
triangular and its only eigenvalue is `b`, which the formula also gives. -/
theorem tridiagonalToeplitz_hasEigenvalue_iff (n : ℕ) (a b c : ℝ) (hac : 0 ≤ a * c) (μ : ℝ) :
    Module.End.HasEigenvalue (toEuclideanLin (tridiagonalToeplitz n a b c)) μ ↔
      ∃ k : Fin n, μ = b + 2 * Real.sqrt (a * c)
        * Real.cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)) := by
  rw [hasEigenvalue_toEuclideanLin_iff]
  rcases eq_or_ne c 0 with rfl | hc
  · rw [mem_spectrum_tridiagonalToeplitz_super_zero]
    simp
  rcases eq_or_ne a 0 with rfl | ha
  · have htr : tridiagonalToeplitz n 0 b c = (tridiagonalToeplitz n c b 0)ᵀ := by
      rw [tridiagonalToeplitz_transpose]
    rw [htr, spectrum_transpose, mem_spectrum_tridiagonalToeplitz_super_zero]
    simp
  -- the nondegenerate case: a diagonal similarity to a symmetric tridiagonal Toeplitz matrix
  have hacpos : 0 < a * c := lt_of_le_of_ne hac (Ne.symm (mul_ne_zero ha hc))
  have hc2 : 0 < c ^ 2 := lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc))
  have hdiv : 0 < a / c := by
    have hrw : a / c = a * c / c ^ 2 := by field_simp
    rw [hrw]
    exact div_pos hacpos hc2
  set d : ℝ := Real.sqrt (a / c) with hddef
  have hd : d ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdiv)
  have hd2 : d ^ 2 = a / c := Real.sq_sqrt hdiv.le
  set u : (Matrix (Fin n) (Fin n) ℝ)ˣ := diagPowUnit n hd with hu
  have huval : (u : Matrix (Fin n) (Fin n) ℝ) = diagonal fun i : Fin n => d ^ (i : ℕ) := rfl
  have hconj : (u : Matrix (Fin n) (Fin n) ℝ) * symmTridiagonalToeplitz n (c * d) b
      * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) = tridiagonalToeplitz n a b c := by
    rw [huval, ← tridiagonalToeplitz_mul_diagonal_pow n a b c d hc hd2, mul_assoc, ← huval,
      u.mul_inv, mul_one]
  rw [← hconj, spectrum.units_conjugate, ← hasEigenvalue_toEuclideanLin_iff,
    symmTridiagonalToeplitz_hasEigenvalue_iff]
  have hsq : (c * d) ^ 2 = a * c := by
    rw [mul_pow, hd2]
    field_simp
  have habs : |c * d| = Real.sqrt (a * c) := by
    rw [← hsq, Real.sqrt_sq_eq_abs]
  rcases abs_choice (c * d) with h | h
  · rw [← habs, h]
  · rw [← habs, ← exists_eq_add_cos_neg_iff, h]

/-! ### The centred advection-diffusion matrix `tridiag(-(1 + p), 2, -(1 - p))` -/

/-- Negating a tridiagonal Toeplitz matrix negates its three bands. -/
theorem neg_tridiagonalToeplitz (m : ℕ) (x y z : ℝ) :
    -Matrix.tridiagonalToeplitz m x y z = Matrix.tridiagonalToeplitz m (-x) (-y) (-z) := by
  ext i j
  rw [Matrix.neg_apply, Matrix.tridiagonalToeplitz_apply, Matrix.tridiagonalToeplitz_apply]
  split_ifs <;> simp

/-- The matrix of the stabilized centred scheme splits into the symmetric model Laplacian and the
antisymmetric centred advection matrix:
`tridiag(-(1 + p), 2, -(1 - p)) = tridiag(-1, 2, -1) + p tridiag(-1, 0, 1)`. -/
theorem tridiagonalToeplitz_eq_add_smul (m : ℕ) (p : ℝ) :
    Matrix.tridiagonalToeplitz m (-(1 + p)) 2 (-(1 - p))
      = Matrix.symmTridiagonalToeplitz m (-1) 2 + p • Matrix.tridiagonalToeplitz m (-1) 0 1 := by
  rw [Matrix.symmTridiagonalToeplitz_eq_tridiagonalToeplitz]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.tridiagonalToeplitz_apply,
    Matrix.tridiagonalToeplitz_apply, Matrix.tridiagonalToeplitz_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The centred advection matrix `tridiag(-1, 0, 1)` is antisymmetric, so its quadratic form
vanishes: the advective term contributes nothing to the energy of the discrete operator. -/
theorem dotProduct_mulVec_tridiagonalToeplitz_antisymm {m : ℕ} (x : Fin m → ℝ) :
    x ⬝ᵥ (Matrix.tridiagonalToeplitz m (-1) 0 1 *ᵥ x) = 0 := by
  have htr : (Matrix.tridiagonalToeplitz m (-1) 0 1)ᵀ = -Matrix.tridiagonalToeplitz m (-1) 0 1 := by
    rw [Matrix.tridiagonalToeplitz_transpose, neg_tridiagonalToeplitz]
    norm_num
  have h1 : x ⬝ᵥ (Matrix.tridiagonalToeplitz m (-1) 0 1 *ᵥ x)
      = x ⬝ᵥ ((Matrix.tridiagonalToeplitz m (-1) 0 1)ᵀ *ᵥ x) := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [htr, Matrix.neg_mulVec, dotProduct_neg] at h1
  linarith

/-- The quadratic form of the stabilized scheme's matrix is that of the model Laplacian, hence
positive: `xᵀ tridiag(-(1 + p), 2, -(1 - p)) x = xᵀ tridiag(-1, 2, -1) x > 0` for `x ≠ 0`,
whatever `p`. -/
theorem dotProduct_mulVec_tridiagonalToeplitz_pos {m : ℕ} (p : ℝ) {x : Fin m → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (Matrix.tridiagonalToeplitz m (-(1 + p)) 2 (-(1 - p)) *ᵥ x) := by
  rw [tridiagonalToeplitz_eq_add_smul, Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_mulVec_tridiagonalToeplitz_antisymm, mul_zero, add_zero]
  simpa using (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two m).dotProduct_mulVec_pos hx

/-- **The matrix of the stabilized scheme is an M-matrix** whenever `|Pe*| ≤ 1`
([quarteroni2000numerical] Exercise 12.13): its off-diagonal entries `-(1 ± Pe*)` are
nonpositive, and its quadratic form is that of the model Laplacian, which is positive definite. -/
theorem isMMatrix_smul_tridiagonalToeplitz {m : ℕ} {c p : ℝ} (hc : 0 < c) (hp : |p| ≤ 1) :
    (c • Matrix.tridiagonalToeplitz m (-(1 + p)) 2 (-(1 - p))).IsMMatrix := by
  obtain ⟨hp1, hp2⟩ := abs_le.1 hp
  refine Matrix.isMMatrix_of_forall_dotProduct_mulVec_pos (fun x hx => ?_) fun i j hij => ?_
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hc (dotProduct_mulVec_tridiagonalToeplitz_pos p hx)
  · rw [Matrix.smul_apply, smul_eq_mul, Matrix.tridiagonalToeplitz_apply]
    split_ifs with h1 h2 h3
    · exact absurd (Fin.val_injective h1) hij
    · nlinarith
    · nlinarith
    · simp

end General

end Matrix
