import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.MonotoneConvergence
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Order
import Numlib.LinearAlgebra.Matrix.PerronFrobenius

/-!
# The nonnegative Neumann criterion, and M-matrices

For an entrywise nonnegative real matrix `B`, the spectral radius is below `1` exactly when
`1 - B` is invertible with an entrywise nonnegative inverse (Saad[^saad-iterative], Theorem 1.29),
and an *M-matrix* is a matrix with nonpositive off-diagonal entries that is invertible with a
nonnegative inverse (his Definition 1.30). Both are statements about the entrywise order of
`Numlib/LinearAlgebra/Matrix/Order` and the spectral radius of
`Numlib/LinearAlgebra/Matrix/Complexify`, and neither mentions an iteration; the splittings that
consume them are in `Numlib/LinearSolve/Stationary/RegularSplitting`.

## Main definitions

* `Matrix.IsMMatrix`: Saad's Definition 1.30, as a three-field structure; the remaining clause of
  the book, positivity of the diagonal, is the derived `Matrix.IsMMatrix.diag_pos`.

## Main results

* `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff`: the nonnegative Neumann criterion.
* `Matrix.isMMatrix_iff_complexSpectralRadius_lt_one`: the spectral characterization, through the
  Jacobi operator `1 - D⁻¹ A`.
* `Matrix.IsMMatrix.of_entrywiseLE`: the comparison theorem, which is what makes the dropping step
  of an incomplete factorization legitimate.

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
needed. If `C` is nonnegative then `Bᵏ C` is too, so the identity exhibits every partial sum
`∑_{j < k} Bʲ` as *bounded above by `C`*, entry by entry; the partial sums are also nondecreasing,
because the terms are nonnegative. A bounded monotone sequence of reals converges, so its
increments `Bᵏ` tend to `0` entrywise, which is `ρ(B) < 1`. The whole argument is monotone
convergence in `ℝ`, one entry at a time, and it needs no eigenvector, no irreducibility and no
compactness.

The irreducible Perron–Frobenius theorem is a separate development, in
`Numlib/LinearAlgebra/Matrix/PerronFrobenius`; neither statement implies the other cheaply.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
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

/-- The partial sums of the Neumann series of `B`, in closed form: if `C` is a right inverse of
`1 - B` then `∑_{j < k} Bʲ = C - Bᵏ C`.

Only a right inverse is needed, and the proof is `Finset.geom_sum_mul_neg` multiplied by `C`. -/
theorem geom_sum_eq_sub_pow_mul {B C : Matrix n n ℝ} (hC : (1 - B) * C = 1) (k : ℕ) :
    ∑ j ∈ range k, B ^ j = C - B ^ k * C :=
  calc ∑ j ∈ range k, B ^ j
      = (∑ j ∈ range k, B ^ j) * ((1 - B) * C) := by rw [hC, mul_one]
    _ = ((∑ j ∈ range k, B ^ j) * (1 - B)) * C := (mul_assoc _ _ _).symm
    _ = (1 - B ^ k) * C := by rw [geom_sum_mul_neg]
    _ = C - B ^ k * C := by rw [sub_mul, one_mul]

/-- **The nonnegative Neumann criterion** (Saad, *Iterative Methods for Sparse Linear Systems*,
Theorem 1.29): an entrywise nonnegative real matrix `B` has spectral radius less than `1` if and
only if `1 - B` is invertible with an entrywise nonnegative inverse.

The forward direction is the Neumann series with nonnegative terms; the backward direction reads
the same series as a monotone sequence bounded above by `(1 - B)⁻¹`. See the module
documentation: no Perron–Frobenius theorem is involved. -/
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

/-- **M-matrix** (Saad, *Iterative Methods for Sparse Linear Systems*, Definition 1.30): the
off-diagonal entries are nonpositive, the matrix is invertible, and the inverse is entrywise
nonnegative. Saad's definition also lists `0 < A i i`, which follows: see
`Matrix.IsMMatrix.diag_pos`. -/
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

/-- The diagonal entries of an M-matrix are positive — the *first* clause of Saad's Definition
1.30, which his Theorem 1.32 shows the other three to imply. Reading `(A A⁻¹) i i = 1` entrywise,
every off-diagonal term
`A i k * A⁻¹ k i` is nonpositive, so `A i i * A⁻¹ i i ≥ 1`, which forces both factors positive. -/
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

/-- The Jacobi operator `1 - D⁻¹ A` of a matrix with positive diagonal and nonpositive
off-diagonal entries is entrywise nonnegative. -/
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

/-- **The spectral characterization of an M-matrix** (Saad, *Iterative Methods for Sparse Linear
Systems*, Theorem 1.31): a real matrix with positive diagonal and nonpositive off-diagonal entries
is an M-matrix exactly when the spectral radius of its Jacobi operator `1 - D⁻¹ A` is less
than one, `D` being the diagonal of `A`.

Both directions are the nonnegative Neumann criterion
`Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff` applied to `B = 1 - D⁻¹ A`, whose
complement is `1 - B = D⁻¹ A`: nonsingularity of `D⁻¹ A` is nonsingularity of `A`, and
`(D⁻¹ A)⁻¹ = A⁻¹ D` is entrywise nonnegative exactly when `A⁻¹` is, the diagonal being
positive. -/
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

/-- **The comparison theorem for M-matrices** (Saad, *Iterative Methods for Sparse Linear
Systems*, Theorem 1.33): a matrix that dominates an M-matrix entrywise and still has nonpositive
off-diagonal entries is itself an M-matrix.

The diagonals satisfy `0 < A i i ≤ B i i`, and entrywise
`0 ≤ₑ 1 - D_B⁻¹ B ≤ₑ 1 - D_A⁻¹ A`, because `A i j / A i i ≤ B i j / B i i` for a nonpositive
numerator that increases and a positive denominator that increases with it. Monotonicity of the
spectral radius (`Matrix.complexSpectralRadius_le_of_entrywiseLE`) and
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

end Matrix
