import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.MonotoneConvergence
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.Order
import Numlib.LinearAlgebra.Matrix.PerronFrobenius

/-!
# The nonnegative Neumann criterion, and M-matrices

For an entrywise nonnegative real matrix `B`, the spectral radius is below `1` exactly when `1 - B`
is invertible with an entrywise nonnegative inverse ([saad2003iterative], Theorem 1.29), and an
*M-matrix* is a matrix with nonpositive off-diagonal entries that is invertible with a nonnegative
inverse (his Definition 1.30). Both are statements about the entrywise order of
`Numlib/LinearAlgebra/Matrix/Order` and the spectral radius of
`Numlib/LinearAlgebra/Matrix/Complexify`, and neither mentions an iteration; the splittings that
consume them are in `Numlib/Stationary/RegularSplitting`.

## Main definitions

* `Matrix.IsMMatrix`: [saad2003iterative] Definition 1.30, as a three-field structure; the remaining
  clause of the book, positivity of the diagonal, is the derived `Matrix.IsMMatrix.diag_pos`.

## Main results

* `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff`: the nonnegative Neumann criterion.
* `Matrix.isMMatrix_iff_complexSpectralRadius_lt_one`: the spectral characterization, through the
  Jacobi operator `1 - D⁻¹ A`.
* `Matrix.IsMMatrix.of_entrywiseLE`: the comparison theorem, which is what makes the dropping step
  of an incomplete factorization legitimate.
* `Matrix.IsMMatrix.nonneg_of_mulVec_nonneg` and `Matrix.IsMMatrix.norm_inv_mulVec_le`: the
  discrete maximum principle `A x ≥ 0 ⇒ x ≥ 0` and the comparison principle
  `‖A⁻¹ τ‖_∞ ≤ ‖w‖_∞ ‖τ‖_∞` for a comparison vector `A w = 1`, the two facts a finite-difference
  convergence proof draws from an M-matrix.
* `Matrix.isMMatrix_iff_exists_pos_mulVec_pos`: the M-criterion of [quarteroni2000numerical]
  Property 1.19, `A` is an M-matrix iff `A w > 0` for some `w > 0`; with it the sufficient
  conditions — strict diagonal dominance (their Property 1.20,
  `Matrix.IsStrictDiagDominant.isMMatrix`), weak diagonal dominance with nonsingularity
  (`Matrix.isMMatrix_of_isDiagDominant_of_isUnit`, hence the irreducibly dominant case), and
  positive definiteness (`Matrix.isMMatrix_of_forall_dotProduct_mulVec_pos`, the Stieltjes case
  `Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos`).

## Implementation notes

The proof of the criterion, and the Perron–Frobenius theorem it does *not* use.

Both directions of the criterion come from one identity — with `C` a right inverse of `1 - B`,
```
∑_{j < k} Bʲ = C - Bᵏ C,
```
`Matrix.geom_sum_eq_sub_pow_mul` — read in two ways.

Forwards, `ρ(B) < 1` makes `Bᵏ → 0`, so the partial sums converge to `C`; each is entrywise
nonnegative and the nonnegative matrices are closed, so `C` is nonnegative.

Backwards is where the textbooks invoke Perron–Frobenius: `ρ(B)` is an eigenvalue of a nonnegative
`B` with a nonnegative eigenvector, and testing `C` against it forces `ρ(B) < 1`. That is not
needed. If `C` is nonnegative then `Bᵏ C` is too, so the identity exhibits every partial sum `∑_{j <
k} Bʲ` as *bounded above by `C`*, entry by entry; the partial sums are also nondecreasing, because
the terms are nonnegative. A bounded monotone sequence of reals converges, so its increments `Bᵏ`
tend to `0` entrywise, which is `ρ(B) < 1`. The whole argument is monotone convergence in `ℝ`, one
entry at a time, and it needs no eigenvector, no irreducibility and no compactness.

The irreducible Perron–Frobenius theorem is a separate development, in
`Numlib/LinearAlgebra/Matrix/PerronFrobenius`; neither statement implies the other cheaply.
-/

open Filter Finset
open scoped Topology Matrix

namespace Matrix

variable {m n : Type*}

/-- A limit of entrywise nonnegative matrices is entrywise nonnegative: the nonnegative cone is
closed. Stated for a filter rather than for sequences, since the proof is `ge_of_tendsto` in each
entry.

This is the one fact about the entrywise order that needs a topology, which is why it is here and
not in `Numlib/LinearAlgebra/Matrix/Order`; that module is kept free of analysis so that it can be
upstreamed as pure order theory. -/
theorem EntrywiseNonneg.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → Matrix m n ℝ}
    {A : Matrix m n ℝ} (hf : ∀ i, (f i).EntrywiseNonneg) (h : Tendsto f l (𝓝 A)) :
    A.EntrywiseNonneg :=
  entrywiseNonneg_iff.2 fun i j =>
    ge_of_tendsto (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) j)
      (.of_forall fun k => (hf k).apply i j)

variable [Fintype n] [DecidableEq n]

/-- The partial sums of the Neumann series of `B`, in closed form: if `C` is a right inverse of `1 -
B` then `∑_{j < k} Bʲ = C - Bᵏ C`.

Only a right inverse is needed, and the proof is `Finset.geom_sum_mul_neg` multiplied by `C`. -/
theorem geom_sum_eq_sub_pow_mul {B C : Matrix n n ℝ} (hC : (1 - B) * C = 1) (k : ℕ) :
    ∑ j ∈ range k, B ^ j = C - B ^ k * C :=
  calc ∑ j ∈ range k, B ^ j
      = (∑ j ∈ range k, B ^ j) * ((1 - B) * C) := by rw [hC, mul_one]
    _ = ((∑ j ∈ range k, B ^ j) * (1 - B)) * C := (mul_assoc _ _ _).symm
    _ = (1 - B ^ k) * C := by rw [geom_sum_mul_neg]
    _ = C - B ^ k * C := by rw [sub_mul, one_mul]

/-- **The nonnegative Neumann criterion** ([saad2003iterative], Theorem 1.29): an entrywise
nonnegative real matrix `B` has spectral radius less than `1` if and only if `1 - B` is invertible
with an entrywise nonnegative inverse.

The forward direction is the Neumann series with nonnegative terms; the backward direction reads the
same series as a monotone sequence bounded above by `(1 - B)⁻¹`. See the module documentation: no
Perron–Frobenius theorem is involved. -/
theorem EntrywiseNonneg.complexSpectralRadius_lt_one_iff {B : Matrix n n ℝ}
    (hB : B.EntrywiseNonneg) :
    B.complexSpectralRadius < 1 ↔ IsUnit (1 - B) ∧ (1 - B)⁻¹.EntrywiseNonneg := by
  have hsum : ∀ k, (∑ j ∈ range k, B ^ j).EntrywiseNonneg := fun k =>
    EntrywiseNonneg.sum fun j _ => hB.pow j
  constructor
  · intro h
    have hu : IsUnit (1 - B) := isUnit_one_sub_of_complexSpectralRadius_lt_one h
    have hC : (1 - B) * (1 - B)⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.1 hu)
    refine ⟨hu, ?_⟩
    have hmul : Continuous fun X : Matrix n n ℝ => X * (1 - B)⁻¹ :=
      continuous_id.matrix_mul continuous_const
    have hpow : Tendsto (fun k => B ^ k * (1 - B)⁻¹) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (hmul.tendsto 0).comp ((tendsto_pow_iff_complexSpectralRadius_lt_one B).2 h)
    refine EntrywiseNonneg.of_tendsto hsum (l := atTop) ?_
    simpa [geom_sum_eq_sub_pow_mul hC] using tendsto_const_nhds.sub hpow
  · rintro ⟨hu, hCnn⟩
    have hC : (1 - B) * (1 - B)⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.1 hu)
    -- Every partial sum is bounded above by `(1 - B)⁻¹`, entry by entry.
    have hle : ∀ k i j, (∑ x ∈ range k, B ^ x) i j ≤ (1 - B)⁻¹ i j := fun k i j => by
      rw [geom_sum_eq_sub_pow_mul hC k, sub_apply]
      simpa using ((hB.pow k).mul hCnn).apply i j
    have hmono : ∀ i j, Monotone fun k => (∑ x ∈ range k, B ^ x) i j := fun i j =>
      monotone_nat_of_le_succ fun k => by
        rw [sum_range_succ, add_apply]
        simpa using (hB.pow k).apply i j
    refine (tendsto_pow_iff_complexSpectralRadius_lt_one B).1 ?_
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have hlim := tendsto_atTop_ciSup (hmono i j) ⟨(1 - B)⁻¹ i j, by
      rintro _ ⟨k, rfl⟩; exact hle k i j⟩
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa [Function.comp_def, sum_range_succ] using this

/-- **M-matrix** ([saad2003iterative], Definition 1.30): the off-diagonal entries are nonpositive,
the matrix is invertible, and the inverse is entrywise nonnegative. [saad2003iterative] definition
also lists `0 < A i i`, which follows: see `Matrix.IsMMatrix.diag_pos`. -/
structure IsMMatrix (A : Matrix n n ℝ) : Prop where
  /-- The off-diagonal entries are nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  /-- The matrix is invertible. -/
  isUnit : IsUnit A
  /-- The inverse is entrywise nonnegative. -/
  inv_entrywiseNonneg : A⁻¹.EntrywiseNonneg

namespace IsMMatrix

variable {A : Matrix n n ℝ} (hA : A.IsMMatrix)
include hA

/-- The diagonal entries of an M-matrix are positive — the *first* clause of [saad2003iterative]
Definition 1.30, which his Theorem 1.32 shows the other three to imply. Reading `(A A⁻¹) i i = 1`
entrywise, every off-diagonal term `A i k * A⁻¹ k i` is nonpositive, so `A i i * A⁻¹ i i ≥ 1`, which
forces both factors positive. -/
theorem diag_pos (i : n) : 0 < A i i := by
  have hdet : IsUnit A.det := isUnit_iff_isUnit_det _ |>.1 hA.isUnit
  have hrow : ∑ k, A i k * A⁻¹ k i = 1 := by
    have := congrArg (fun M : Matrix n n ℝ => M i i) (mul_nonsing_inv A hdet)
    simpa [mul_apply] using this
  have hoff : ∑ k ∈ univ.erase i, A i k * A⁻¹ k i ≤ 0 :=
    sum_nonpos fun k hk =>
      mul_nonpos_of_nonpos_of_nonneg (hA.offDiag_nonpos i k (mem_erase.1 hk).1.symm)
        (hA.inv_entrywiseNonneg.apply k i)
  have hdiag : 1 ≤ A i i * A⁻¹ i i := by
    rw [← add_sum_erase _ _ (mem_univ i)] at hrow
    linarith
  by_contra hle
  exact absurd (hdiag.trans (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hle)
    (hA.inv_entrywiseNonneg.apply i i))) (by norm_num)

end IsMMatrix

/-! ### Equivalent characterizations, and the comparison theorem -/

section Comparison

variable {A B : Matrix n n ℝ}

/-- The entries of the Jacobi operator `1 - D⁻¹ A`, with `D` the diagonal of `A`. -/
private theorem one_sub_diagInv_mul_apply (A : Matrix n n ℝ) (i j : n) :
    ((1 : Matrix n n ℝ) - diagonal (fun i => (A i i)⁻¹) * A) i j
      = (1 : Matrix n n ℝ) i j - (A i i)⁻¹ * A i j := by
  rw [sub_apply, diagonal_mul]

/-- The Jacobi operator `1 - D⁻¹ A` of a matrix with positive diagonal and nonpositive off-diagonal
entries is entrywise nonnegative. -/
private theorem entrywiseNonneg_one_sub_diagInv_mul (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hdiag : ∀ i, 0 < A i i) :
    ((1 : Matrix n n ℝ) - diagonal (fun i => (A i i)⁻¹) * A).EntrywiseNonneg := by
  refine entrywiseNonneg_iff.2 fun i j => ?_
  rw [one_sub_diagInv_mul_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [one_apply_eq, inv_mul_cancel₀ (hdiag i).ne', sub_self]
  · have h : (A i i)⁻¹ * A i j ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hdiag i).le) (hoff i j hij)
    rw [one_apply_ne hij]
    linarith

/-- `D⁻¹ D = 1` for the diagonal `D` of a matrix with a nowhere vanishing diagonal. -/
private theorem diagInv_mul_diag (hdiag : ∀ i, A i i ≠ 0) :
    (diagonal fun i => (A i i)⁻¹) * (diagonal fun i => A i i) = 1 := by
  rw [diagonal_mul_diagonal,
    show (fun i => (A i i)⁻¹ * A i i) = fun _ : n => (1 : ℝ) from
      funext fun i => inv_mul_cancel₀ (hdiag i),
    diagonal_one]

/-- `D D⁻¹ = 1` for the diagonal `D` of a matrix with a nowhere vanishing diagonal. -/
private theorem diag_mul_diagInv (hdiag : ∀ i, A i i ≠ 0) :
    (diagonal fun i => A i i) * (diagonal fun i => (A i i)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal,
    show (fun i => A i i * (A i i)⁻¹) = fun _ : n => (1 : ℝ) from
      funext fun i => mul_inv_cancel₀ (hdiag i),
    diagonal_one]

/-- **The spectral characterization of an M-matrix** ([saad2003iterative], Theorem 1.31): a real
matrix with positive diagonal and nonpositive off-diagonal entries is an M-matrix exactly when the
spectral radius of its Jacobi operator `1 - D⁻¹ A` is less than one, `D` being the diagonal of `A`.

Both directions are the nonnegative Neumann criterion
`Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff` applied to `B = 1 - D⁻¹ A`, whose
complement is `1 - B = D⁻¹ A`: nonsingularity of `D⁻¹ A` is nonsingularity of `A`, and `(D⁻¹ A)⁻¹ =
A⁻¹ D` is entrywise nonnegative exactly when `A⁻¹` is, the diagonal being positive. -/
theorem isMMatrix_iff_complexSpectralRadius_lt_one (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hdiag : ∀ i, 0 < A i i) :
    A.IsMMatrix
      ↔ ((1 : Matrix n n ℝ) - diagonal (fun i => (A i i)⁻¹) * A).complexSpectralRadius < 1 := by
  have hne : ∀ i, A i i ≠ 0 := fun i => (hdiag i).ne'
  have hDU : IsUnit (diagonal fun i => (A i i)⁻¹ : Matrix n n ℝ) :=
    ⟨⟨_, _, diagInv_mul_diag hne, diag_mul_diagInv hne⟩, rfl⟩
  rw [(entrywiseNonneg_one_sub_diagInv_mul hoff hdiag).complexSpectralRadius_lt_one_iff,
    sub_sub_cancel]
  constructor
  · intro hA
    have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hA.isUnit
    refine ⟨hDU.mul hA.isUnit, ?_⟩
    have hinv : ((diagonal fun i => (A i i)⁻¹) * A)⁻¹ = A⁻¹ * diagonal fun i => A i i := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, mul_nonsing_inv A hdet, Matrix.one_mul,
        diagInv_mul_diag hne]
    refine entrywiseNonneg_iff.2 fun i j => ?_
    rw [hinv, mul_diagonal]
    exact mul_nonneg (hA.inv_entrywiseNonneg.apply i j) (hdiag j).le
  · rintro ⟨hu, hnn⟩
    have hdetA : IsUnit A.det := by
      have h := (isUnit_iff_isUnit_det _).1 hu
      rw [det_mul] at h
      exact isUnit_of_mul_isUnit_right h
    refine ⟨hoff, (isUnit_iff_isUnit_det _).2 hdetA, ?_⟩
    have hinv : A⁻¹ = ((diagonal fun i => (A i i)⁻¹) * A)⁻¹ * diagonal fun i => (A i i)⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hu)]
    refine entrywiseNonneg_iff.2 fun i j => ?_
    rw [hinv, mul_diagonal]
    exact mul_nonneg (hnn.apply i j) (inv_nonneg.2 (hdiag j).le)

/-- **The comparison theorem for M-matrices** ([saad2003iterative], Theorem 1.33): a matrix that
dominates an M-matrix entrywise and still has nonpositive off-diagonal entries is itself an
M-matrix.

The diagonals satisfy `0 < A i i ≤ B i i`, and entrywise `0 ≤ₑ 1 - D_B⁻¹ B ≤ₑ 1 - D_A⁻¹ A`, because
`A i j / A i i ≤ B i j / B i i` for a nonpositive numerator that increases and a positive
denominator that increases with it. Monotonicity of the spectral radius
(`Matrix.complexSpectralRadius_le_of_entrywiseLE`) and
`Matrix.isMMatrix_iff_complexSpectralRadius_lt_one` do the rest.

This is what makes the *dropping* step of an incomplete factorization legitimate: discarding a
nonpositive off-diagonal entry moves the matrix up in the entrywise order. -/
theorem IsMMatrix.of_entrywiseLE (hA : A.IsMMatrix) (hAB : A ≤ₑ B)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) : B.IsMMatrix := by
  have hdiagA : ∀ i, 0 < A i i := hA.diag_pos
  have hdiagB : ∀ i, 0 < B i i := fun i => (hdiagA i).trans_le (hAB i i)
  refine (isMMatrix_iff_complexSpectralRadius_lt_one hoff hdiagB).2 ?_
  refine lt_of_le_of_lt (complexSpectralRadius_le_of_entrywiseLE
    (entrywiseNonneg_one_sub_diagInv_mul hoff hdiagB) fun i j => ?_)
    ((isMMatrix_iff_complexSpectralRadius_lt_one hA.offDiag_nonpos hdiagA).1 hA)
  rw [one_sub_diagInv_mul_apply, one_sub_diagInv_mul_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [inv_mul_cancel₀ (hdiagA i).ne', inv_mul_cancel₀ (hdiagB i).ne']
  · have hb : B i j ≤ 0 := hoff i j hij
    have h1 : A i j * (A i i)⁻¹ ≤ B i j * (A i i)⁻¹ :=
      mul_le_mul_of_nonneg_right (hAB i j) (inv_nonneg.2 (hdiagA i).le)
    have h2 : B i j * (A i i)⁻¹ ≤ B i j * (B i i)⁻¹ := by
      have hinv : (B i i)⁻¹ ≤ (A i i)⁻¹ := inv_anti₀ (hdiagA i) (hAB i i)
      nlinarith
    have : (A i i)⁻¹ * A i j ≤ (B i i)⁻¹ * B i j := by
      rw [mul_comm ((A i i)⁻¹), mul_comm ((B i i)⁻¹)]
      linarith
    linarith

end Comparison

/-! ### The discrete maximum principle, and the comparison principle -/

section MaximumPrinciple

variable {A : Matrix n n ℝ} (hA : A.IsMMatrix)
include hA

/-- `A⁻¹ (A x) = x` for an M-matrix: the identity every consequence of `A⁻¹ ≥ 0` starts from. -/
private theorem IsMMatrix.inv_mulVec_mulVec (x : n → ℝ) : A⁻¹ *ᵥ (A *ᵥ x) = x := by
  rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hA.isUnit), one_mulVec]

/-- **The discrete maximum principle** of an M-matrix, in the form the finite-difference theory
uses: `A x ≥ 0` entrywise forces `x ≥ 0` entrywise, because `x = A⁻¹ (A x)` and `A⁻¹ ≥ 0`. This is
the property [quarteroni2000numerical] §12.2 and §12.5.2 call the discrete maximum principle ("the
discrete solution is nonnegative when the datum is"). -/
theorem IsMMatrix.nonneg_of_mulVec_nonneg {x : n → ℝ} (hx : 0 ≤ A *ᵥ x) : 0 ≤ x := by
  rw [← hA.inv_mulVec_mulVec x]
  exact hA.inv_entrywiseNonneg.mulVec_nonneg hx

/-- The discrete maximum principle as [quarteroni2000numerical] §1.12 state it: `A x ≤ 0` entrywise
forces `x ≤ 0` entrywise. -/
theorem IsMMatrix.nonpos_of_mulVec_nonpos {x : n → ℝ} (hx : A *ᵥ x ≤ 0) : x ≤ 0 :=
  neg_nonneg.1 (hA.nonneg_of_mulVec_nonneg (x := -x) (by rw [mulVec_neg]; exact neg_nonneg.2 hx))

/-- The inverse of an M-matrix is monotone for the entrywise order of vectors. -/
theorem IsMMatrix.inv_mulVec_le_inv_mulVec {σ τ : n → ℝ} (h : σ ≤ τ) : A⁻¹ *ᵥ σ ≤ A⁻¹ *ᵥ τ :=
  hA.inv_entrywiseNonneg.mulVec_mono h

/-- The entrywise triangle inequality for the inverse of an M-matrix, `|A⁻¹ τ| ≤ A⁻¹ |τ|`: the
absolute value of `A⁻¹` is `A⁻¹` itself. -/
theorem IsMMatrix.abs_inv_mulVec_le (τ : n → ℝ) : |A⁻¹ *ᵥ τ| ≤ A⁻¹ *ᵥ |τ| := by
  have habs : A⁻¹.abs = A⁻¹ :=
    Matrix.ext fun i j => abs_of_nonneg (hA.inv_entrywiseNonneg.apply i j)
  simpa [habs] using abs_mulVec_le A⁻¹ τ

/-- **The comparison principle.** If `w` is a *comparison vector* for the M-matrix `A`, meaning
`A w = 1` (the all-ones vector), then `‖A⁻¹ τ‖_∞ ≤ ‖w‖_∞ ‖τ‖_∞` for every `τ`. Entrywise,
`|A⁻¹ τ| ≤ A⁻¹ |τ| ≤ ‖τ‖_∞ A⁻¹ 1 = ‖τ‖_∞ w`, by the nonnegativity of `A⁻¹` used twice.

This is the stability half of the convergence proof for the finite-difference discretization of a
two-point boundary value problem ([quarteroni2000numerical] Theorem 12.1, whose (12.28) is the
instance `w_j = x_j (1 - x_j) / 2`, `‖w‖_∞ ≤ 1/8`, for the matrix `tridiag(-1, 2, -1) / h²`), and
of its two-dimensional counterpart in their §12.6; it replaces the book's explicit discrete Green's
function by the comparison vector alone. -/
theorem IsMMatrix.norm_inv_mulVec_le {w : n → ℝ} (hw : A *ᵥ w = 1) (τ : n → ℝ) :
    ‖A⁻¹ *ᵥ τ‖ ≤ ‖w‖ * ‖τ‖ := by
  have hw' : A⁻¹ *ᵥ 1 = w := by rw [← hw, hA.inv_mulVec_mulVec]
  have hτ : |τ| ≤ ‖τ‖ • (1 : n → ℝ) := fun i => by
    simpa using norm_le_pi_norm τ i
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(A⁻¹ *ᵥ τ) i‖ = |A⁻¹ *ᵥ τ| i := Real.norm_eq_abs _
    _ ≤ (A⁻¹ *ᵥ |τ|) i := hA.abs_inv_mulVec_le τ i
    _ ≤ (A⁻¹ *ᵥ (‖τ‖ • (1 : n → ℝ))) i := hA.inv_mulVec_le_inv_mulVec hτ i
    _ = ‖τ‖ * w i := by rw [mulVec_smul, hw']; rfl
    _ ≤ ‖τ‖ * ‖w‖ := by
        gcongr
        exact (le_abs_self _).trans (by simpa using norm_le_pi_norm w i)
    _ = ‖w‖ * ‖τ‖ := mul_comm _ _

end MaximumPrinciple

/-! ### The M-criterion, and the sufficient conditions

The criterion of [quarteroni2000numerical] Property 1.19: a matrix with nonpositive off-diagonal
entries is an M-matrix exactly when some entrywise positive `w` has `A w` entrywise positive. The
backward direction is a spectral-radius bound for the Jacobi operator `B = 1 - D⁻¹ A`, which is
nonnegative with `B w < w`: conjugating by `diag(w)` gives a nonnegative matrix whose row sums are
`(B w)_i / w_i < 1`, so its maximum absolute row sum is below one. Everything downstream — strict
diagonal dominance, irreducible diagonal dominance with nonsingularity, positive definiteness — is
a choice of `w`. -/

section Criterion

/-- Conjugation by a nonsingular matrix does not change the spectral radius: the spectrum of
`C⁻¹ B C` is that of `B`. -/
theorem complexSpectralRadius_conj {C : Matrix n n ℝ} (hC : IsUnit C) (B : Matrix n n ℝ) :
    complexSpectralRadius (C⁻¹ * B * C) = complexSpectralRadius B := by
  have hC' : IsUnit (complexify C) := (isUnit_complexify_iff C).2 hC
  simp only [complexSpectralRadius, spectralRadius, complexify_mul, complexify_inv]
  rw [← hC'.unit_spec, ← coe_units_inv, spectrum.units_conjugate']

section Operator

open scoped Matrix.Norms.Operator

/-- **The strict Collatz–Wielandt bound**: an entrywise nonnegative matrix `B` that strictly
decreases some entrywise positive vector, `B w < w` entrywise, has spectral radius less than one.
The diagonal similarity `W⁻¹ B W` with `W = diag(w)` is nonnegative with row sums `(B w)_i / w_i <
1`, so its maximum absolute row sum, which bounds the spectral radius, is below one. -/
theorem EntrywiseNonneg.complexSpectralRadius_lt_one_of_mulVec_lt {B : Matrix n n ℝ}
    (hB : B.EntrywiseNonneg) {w : n → ℝ} (hw : ∀ i, 0 < w i) (hBw : ∀ i, (B *ᵥ w) i < w i) :
    complexSpectralRadius B < 1 := by
  have hne : ∀ i, w i ≠ 0 := fun i => (hw i).ne'
  set W : Matrix n n ℝ := diagonal w with hW
  set W' : Matrix n n ℝ := diagonal fun i => (w i)⁻¹ with hW'
  have hWW' : W * W' = 1 := by
    rw [hW, hW', diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun i => mul_inv_cancel₀ (hne i))
  have hW'W : W' * W = 1 := by
    rw [hW, hW', diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun i => inv_mul_cancel₀ (hne i))
  have hunit : IsUnit W := ⟨⟨W, W', hWW', hW'W⟩, rfl⟩
  rw [← complexSpectralRadius_conj hunit B, inv_eq_right_inv hWW']
  refine lt_of_le_of_lt (complexSpectralRadius_le_linfty_opNNNorm _) ?_
  rw [ENNReal.coe_lt_one_iff, linfty_opNNNorm_def, Finset.sup_lt_iff (by simp)]
  intro i _
  have hentry : ∀ j, (W' * B * W) i j = (w i)⁻¹ * (B i j * w j) := fun j => by
    rw [hW, hW', mul_diagonal, diagonal_mul, mul_assoc]
  have hrow : ∑ j, |(w i)⁻¹ * (B i j * w j)| = (w i)⁻¹ * (B *ᵥ w) i := by
    rw [mulVec_apply_eq_sum, mul_sum]
    exact sum_congr rfl fun j _ => abs_of_nonneg
      (mul_nonneg (inv_nonneg.2 (hw i).le) (mul_nonneg (hB.apply i j) (hw j).le))
  rw [← NNReal.coe_lt_coe, NNReal.coe_sum, NNReal.coe_one]
  simp only [coe_nnnorm, hentry, Real.norm_eq_abs]
  rw [hrow, inv_mul_lt_iff₀ (hw i), mul_one]
  exact hBw i

end Operator

/-- **The M-criterion** ([quarteroni2000numerical] Property 1.19): a real matrix with nonpositive
off-diagonal entries is an M-matrix if and only if there is an entrywise positive vector `w` with
`A w` entrywise positive.

Forwards, `w = A⁻¹ 1` has `A w = 1`, and each `w i` is a row sum of the nonnegative `A⁻¹`, positive
because no row of an invertible matrix vanishes. Backwards, `(A w)_i > 0` forces `a_ii > 0` since
the off-diagonal contributions are nonpositive, and the nonnegative Jacobi operator `B = 1 - D⁻¹ A`
has `B w = w - D⁻¹ (A w) < w` entrywise, so `ρ(B) < 1` by
`Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_of_mulVec_lt` and
`Matrix.isMMatrix_iff_complexSpectralRadius_lt_one` concludes. -/
theorem isMMatrix_iff_exists_pos_mulVec_pos {A : Matrix n n ℝ} (hoff : ∀ i j, i ≠ j → A i j ≤ 0) :
    A.IsMMatrix ↔ ∃ w : n → ℝ, (∀ i, 0 < w i) ∧ ∀ i, 0 < (A *ᵥ w) i := by
  constructor
  · intro hA
    have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hA.isUnit
    refine ⟨A⁻¹ *ᵥ 1, fun i => ?_, fun i => ?_⟩
    · have hnn : ∀ j ∈ univ, 0 ≤ A⁻¹ i j := fun j _ => hA.inv_entrywiseNonneg.apply i j
      rw [mulVec_apply_eq_sum]
      simp only [Pi.one_apply, mul_one]
      refine (sum_nonneg hnn).lt_of_ne fun h => ?_
      have hzero : ∀ j, A⁻¹ i j = 0 := fun j =>
        (sum_eq_zero_iff_of_nonneg hnn).1 h.symm j (mem_univ j)
      have h1 := congrFun (congrFun (nonsing_inv_mul A hdet) i) i
      rw [mul_apply, one_apply_eq] at h1
      simp [hzero] at h1
    · rw [mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]
      exact zero_lt_one
  · rintro ⟨w, hw, hAw⟩
    have hdiag : ∀ i, 0 < A i i := fun i => by
      have h : (A *ᵥ w) i = A i i * w i + ∑ j ∈ univ.erase i, A i j * w j := by
        rw [mulVec_apply_eq_sum, ← add_sum_erase _ _ (mem_univ i)]
      have hoffsum : ∑ j ∈ univ.erase i, A i j * w j ≤ 0 :=
        sum_nonpos fun j hj =>
          mul_nonpos_of_nonpos_of_nonneg (hoff i j (mem_erase.1 hj).1.symm) (hw j).le
      have hpos : 0 < A i i * w i := by linarith [hAw i]
      by_contra hle
      exact absurd hpos (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hle) (hw i).le))
    rw [isMMatrix_iff_complexSpectralRadius_lt_one hoff hdiag]
    refine EntrywiseNonneg.complexSpectralRadius_lt_one_of_mulVec_lt
      (entrywiseNonneg_one_sub_diagInv_mul hoff hdiag) hw fun i => ?_
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, Pi.sub_apply, mulVec_diagonal]
    have := mul_pos (inv_pos.2 (hdiag i)) (hAw i)
    linarith

/-- [quarteroni2000numerical] Property 1.20 in row-sum form: a matrix with nonpositive
off-diagonal entries and positive row sums is an M-matrix. For such a matrix positive row sums are
exactly strict row diagonal dominance with a positive diagonal, the book's hypothesis
(`Matrix.IsStrictDiagDominant.isMMatrix`). The M-criterion with `w = 1`. -/
theorem isMMatrix_of_forall_sum_pos {A : Matrix n n ℝ} (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hsum : ∀ i, 0 < ∑ j, A i j) : A.IsMMatrix :=
  (isMMatrix_iff_exists_pos_mulVec_pos hoff).2
    ⟨1, fun _ => zero_lt_one, fun i => by simpa [mulVec_apply_eq_sum] using hsum i⟩

/-- For a row with nonpositive off-diagonal entries, the off-diagonal absolute row sum is the
negative of the off-diagonal row sum. -/
private theorem sum_erase_norm_eq_neg_sum {A : Matrix n n ℝ} (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (i : n) : ∑ j ∈ univ.erase i, ‖A i j‖ = -∑ j ∈ univ.erase i, A i j := by
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun j hj => by
    rw [Real.norm_eq_abs, abs_of_nonpos (hoff i j (mem_erase.1 hj).1.symm)]

/-- **[quarteroni2000numerical] Property 1.20**: a strictly row diagonally dominant matrix with
positive diagonal and nonpositive off-diagonal entries is an M-matrix. -/
theorem IsStrictDiagDominant.isMMatrix {A : Matrix n n ℝ} (hA : A.IsStrictDiagDominant)
    (hdiag : ∀ i, 0 < A i i) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) : A.IsMMatrix := by
  refine isMMatrix_of_forall_sum_pos hoff fun i => ?_
  have h := hA i
  rw [sum_erase_norm_eq_neg_sum hoff, Real.norm_eq_abs, abs_of_pos (hdiag i)] at h
  rw [← add_sum_erase _ _ (mem_univ i)]
  linarith

/-- A *weakly* row diagonally dominant matrix with positive diagonal and nonpositive off-diagonal
entries is an M-matrix as soon as it is nonsingular. With `w = A⁻¹ 1`, so that `A w = 1`, the
minimal entry `w_{i₀}` is positive: were it `≤ 0`, the row `i₀` would give `1 = ∑_j a_{i₀ j} w_j ≤
w_{i₀} ∑_j a_{i₀ j} ≤ 0`, the first inequality because the off-diagonal coefficients are nonpositive
and `w_j ≥ w_{i₀}`, the second because the row sum is nonnegative by weak dominance. The M-criterion
then applies. -/
theorem isMMatrix_of_isDiagDominant_of_isUnit {A : Matrix n n ℝ} (hA : A.IsDiagDominant)
    (hu : IsUnit A) (hdiag : ∀ i, 0 < A i i) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) : A.IsMMatrix := by
  cases isEmpty_or_nonempty n
  · exact (isMMatrix_iff_exists_pos_mulVec_pos hoff).2
      ⟨0, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hu
  set w : n → ℝ := A⁻¹ *ᵥ 1 with hw
  have hAw : A *ᵥ w = 1 := by rw [hw, mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]
  obtain ⟨i₀, -, hi₀⟩ := exists_min_image univ w univ_nonempty
  have hmin : ∀ j, w i₀ ≤ w j := fun j => hi₀ j (mem_univ j)
  have hpos : 0 < w i₀ := by
    by_contra hle
    rw [not_lt] at hle
    have h1 : ∑ j, A i₀ j * w j = 1 := by rw [← mulVec_apply_eq_sum, hAw]; rfl
    have h2 : ∑ j, A i₀ j * w j ≤ (∑ j, A i₀ j) * w i₀ := by
      rw [sum_mul]
      refine sum_le_sum fun j _ => ?_
      rcases eq_or_ne j i₀ with rfl | hj
      · exact le_rfl
      · exact mul_le_mul_of_nonpos_left (hmin j) (hoff i₀ j hj.symm)
    have h3 : 0 ≤ ∑ j, A i₀ j := by
      have hd := hA i₀
      rw [sum_erase_norm_eq_neg_sum hoff, Real.norm_eq_abs, abs_of_pos (hdiag i₀)] at hd
      rw [← add_sum_erase _ _ (mem_univ i₀)]
      linarith
    have h4 : (∑ j, A i₀ j) * w i₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h3 hle
    linarith
  exact (isMMatrix_iff_exists_pos_mulVec_pos hoff).2
    ⟨w, fun j => hpos.trans_le (hmin j), fun i => by rw [hAw]; exact zero_lt_one⟩

/-- An irreducibly diagonally dominant matrix with positive diagonal and nonpositive off-diagonal
entries is an M-matrix: the irreducible companion of [quarteroni2000numerical] Property 1.20,
which is what the grid matrices of their §3.14.2 satisfy. Irreducible dominance gives
nonsingularity (`Matrix.IsIrreduciblyDiagDominant.isUnit`) and weak dominance, and
`Matrix.isMMatrix_of_isDiagDominant_of_isUnit` does the rest. -/
theorem isMMatrix_of_isIrreduciblyDiagDominant {A : Matrix n n ℝ}
    (hA : A.IsIrreduciblyDiagDominant) (hdiag : ∀ i, 0 < A i i)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) : A.IsMMatrix :=
  isMMatrix_of_isDiagDominant_of_isUnit hA.isDiagDominant hA.isUnit hdiag hoff

/-- A real matrix that is positive definite in the sense of [quarteroni2000numerical] Definition
1.22 — `xᵀ A x > 0` for every `x ≠ 0`, with no symmetry assumed — and has nonpositive off-diagonal
entries is an M-matrix.

Positive definiteness makes `A` nonsingular; with `w = A⁻¹ 1` and `w = w⁺ - w⁻` split into its
positive and negative parts, pairing `A w = 1` with `w⁻` gives `∑ w⁻_i = w⁻ᵀ A w⁺ - w⁻ᵀ A w⁻ ≤ 0`,
because the first form only involves off-diagonal entries (the parts have disjoint supports) and
the second is nonnegative; so `w ≥ 0`, and then `w > 0` since a vanishing `w_i` would make
`(A w)_i ≤ 0`. The M-criterion concludes. No spectral theory is involved. -/
theorem isMMatrix_of_forall_dotProduct_mulVec_pos {A : Matrix n n ℝ}
    (hpd : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) :
    A.IsMMatrix := by
  have hu : IsUnit A := by
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv, hAv⟩ := exists_mulVec_eq_zero_iff.2 hdet
    have := hpd v hv
    rw [hAv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hu
  set w : n → ℝ := A⁻¹ *ᵥ 1 with hw
  have hAw : A *ᵥ w = 1 := by rw [hw, mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]
  -- the positive and negative parts of `w`
  set u : n → ℝ := fun i => max (w i) 0 with hu'
  set v : n → ℝ := fun i => max (-w i) 0 with hv
  have hu0 : ∀ i, 0 ≤ u i := fun i => le_max_right _ _
  have hv0 : ∀ i, 0 ≤ v i := fun i => le_max_right _ _
  have huv : ∀ i, u i * v i = 0 := fun i => by
    simp only [hu', hv]
    rcases le_total 0 (w i) with h | h
    · rw [max_eq_right (neg_nonpos.2 h), mul_zero]
    · rw [max_eq_right h, zero_mul]
  have hw_eq : w = u - v := funext fun i => by
    simp only [hu', hv, Pi.sub_apply]
    rcases le_total 0 (w i) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h), zero_sub, neg_neg]
  -- pairing `A w = 1` with the negative part
  have hsum : ∑ i, v i = v ⬝ᵥ (A *ᵥ u) - v ⬝ᵥ (A *ᵥ v) := by
    rw [← dotProduct_sub, ← mulVec_sub, ← hw_eq, hAw, dotProduct_one]
  have h1 : v ⬝ᵥ (A *ᵥ u) ≤ 0 := by
    refine sum_nonpos fun i _ => ?_
    rw [mulVec_apply_eq_sum, mul_sum]
    refine sum_nonpos fun j _ => ?_
    rcases eq_or_ne i j with rfl | hij
    · rw [show v i * (A i i * u i) = A i i * (u i * v i) by ring, huv i, mul_zero]
    · exact mul_nonpos_of_nonneg_of_nonpos (hv0 i)
        (mul_nonpos_of_nonpos_of_nonneg (hoff i j hij) (hu0 j))
  have h2 : 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    rcases eq_or_ne v 0 with hv' | hv'
    · rw [hv', zero_dotProduct]
    · exact (hpd v hv').le
  have hvz : ∀ i, v i = 0 := fun i =>
    (sum_eq_zero_iff_of_nonneg fun i _ => hv0 i).1
      (le_antisymm (by linarith) (sum_nonneg fun i _ => hv0 i)) i (mem_univ i)
  have hw0 : ∀ i, 0 ≤ w i := fun i => by
    have h := congrFun hw_eq i
    rw [Pi.sub_apply, hvz i, sub_zero] at h
    rw [h]
    exact hu0 i
  -- and `w` is in fact positive
  refine (isMMatrix_iff_exists_pos_mulVec_pos hoff).2
    ⟨w, fun i => ?_, fun i => by rw [hAw]; exact zero_lt_one⟩
  refine (hw0 i).lt_of_ne fun hwi => ?_
  have h1' : A i i * w i + ∑ j ∈ univ.erase i, A i j * w j = 1 := by
    rw [add_sum_erase univ (fun j => A i j * w j) (mem_univ i), ← mulVec_apply_eq_sum, hAw]; rfl
  have hoffsum : ∑ j ∈ univ.erase i, A i j * w j ≤ 0 :=
    sum_nonpos fun j hj =>
      mul_nonpos_of_nonpos_of_nonneg (hoff i j (mem_erase.1 hj).1.symm) (hw0 j)
  rw [← hwi, mul_zero, zero_add] at h1'
  linarith

/-- **Stieltjes matrices are M-matrices**: a real symmetric positive definite matrix with
nonpositive off-diagonal entries is an M-matrix. The symmetry is not used; see
`Matrix.isMMatrix_of_forall_dotProduct_mulVec_pos`. The model Laplacian `tridiag(-1, 2, -1)`, its
Kronecker sums and the five-point Laplacian are the instances. -/
theorem IsMMatrix.of_posDef_of_offDiag_nonpos {A : Matrix n n ℝ} (hA : A.PosDef)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) : A.IsMMatrix :=
  isMMatrix_of_forall_dotProduct_mulVec_pos
    (fun x hx => by simpa using hA.dotProduct_mulVec_pos hx) hoff

end Criterion

end Matrix
