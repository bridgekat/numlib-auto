import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.MonotoneConvergence
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Order
import Numlib.LinearSolve.Stationary.Splitting

/-!
# Regular splittings, M-matrices, and nonnegative inverses

A splitting `A = M - N` of a real matrix is *regular* when `M⁻¹` and `N` are entrywise
nonnegative, and it converges exactly when `A` is invertible with `A⁻¹` entrywise nonnegative
(Saad[^saad-iterative], Definition 4.3 and Theorem 4.4). The engine is the nonnegative form of
the Neumann criterion, `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff`: for an entrywise
nonnegative `B`, the powers `Bᵏ` tend to `0` exactly when `1 - B` is invertible with a nonnegative
inverse.

## The proof, and the Perron–Frobenius theorem it does not use

Both directions of the Neumann criterion come from one identity — with `C` a right inverse of
`1 - B`,
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

The plan for this module budgeted a weak Perron theorem as a separate item. Nothing here uses it,
so it is not proved; if a surface for Saad's §1.10 ever wants Perron–Frobenius as a theorem in its
own right, that is a new item and not a prerequisite of this one.

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

/-- The diagonal entries of an M-matrix are positive — the fourth clause of Saad's Definition
1.30, which the other three imply. Reading `(A A⁻¹) i i = 1` entrywise, every off-diagonal term
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

end Matrix

namespace Stationary.Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- **Regular splitting** (Saad, *Iterative Methods for Sparse Linear Systems*, Definition 4.3):
the splitting `A = M - N` is regular when `M⁻¹` and `N` are entrywise nonnegative. -/
def IsRegular (s : Splitting A) : Prop :=
  (Ring.inverse s.m).EntrywiseNonneg ∧ s.n.EntrywiseNonneg

namespace IsRegular

variable {s : Splitting A} (hs : s.IsRegular)
include hs

/-- The iteration operator `G = M⁻¹ N` of a regular splitting is entrywise nonnegative. -/
theorem entrywiseNonneg_iterationOperator : s.iterationOperator.EntrywiseNonneg := by
  rw [s.iterationOperator_eq]; exact hs.1.mul hs.2

/-- **Saad's Theorem 4.4** (*Iterative Methods for Sparse Linear Systems*): a regular splitting
`A = M - N` converges exactly when `A` is invertible with an entrywise nonnegative inverse.

Both directions go through the nonnegative Neumann criterion applied to `G = M⁻¹ N`, using
`1 - G = M⁻¹ A`. Forwards, `A = M (1 - G)` is a product of units and `A⁻¹ = (1 - G)⁻¹ M⁻¹` a
product of nonnegative matrices. Backwards, the identity `(1 - G)⁻¹ = A⁻¹ M = 1 + A⁻¹ N` — which
is Saad's `A⁻¹ N = (1 - G)⁻¹ G` in a form that needs no inverse of `N` — exhibits `(1 - G)⁻¹` as
nonnegative. -/
theorem complexSpectralRadius_lt_one_iff :
    s.iterationOperator.complexSpectralRadius < 1 ↔ IsUnit A ∧ A⁻¹.EntrywiseNonneg := by
  have hMinv : Ring.inverse s.m = s.m⁻¹ := (nonsing_inv_eq_ringInverse _).symm
  have hone : 1 - s.iterationOperator = s.m⁻¹ * A := by
    rw [s.one_sub_iterationOperator, hMinv]
  have hfactor : A = s.m * (1 - s.iterationOperator) := by
    rw [hone, ← mul_assoc, mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.1 s.isUnit), one_mul]
  rw [hs.entrywiseNonneg_iterationOperator.complexSpectralRadius_lt_one_iff]
  constructor
  · rintro ⟨hu, hnn⟩
    refine ⟨hfactor ▸ s.isUnit.mul hu, ?_⟩
    rw [hfactor, Matrix.mul_inv_rev, ← hMinv]
    exact hnn.mul hs.1
  · rintro ⟨hu, hnn⟩
    have hdet : IsUnit A.det := isUnit_iff_isUnit_det _ |>.1 hu
    have hunit : IsUnit (1 - s.iterationOperator) := by
      rw [hone]
      exact (isUnit_nonsing_inv_iff.2 s.isUnit).mul hu
    refine ⟨hunit, ?_⟩
    -- `(1 - G)⁻¹ = A⁻¹ M = A⁻¹ (A + N) = 1 + A⁻¹ N`.
    -- `A` occurs in the type `Splitting A` of `s`, so it cannot be rewritten; move the splitting
    -- identity to the form that replaces `s.m` instead.
    have hmA : s.m = A + s.n := sub_eq_iff_eq_add.mp s.m_sub_n
    have hinv : (1 - s.iterationOperator)⁻¹ = 1 + A⁻¹ * s.n := by
      rw [hone, Matrix.mul_inv_rev,
        nonsing_inv_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.1 s.isUnit), hmA, mul_add,
        nonsing_inv_mul _ hdet]
    rw [hinv]
    exact entrywiseNonneg_one.add (hnn.mul hs.2)

/-- Every regular splitting of an M-matrix converges (the remark after Saad's Theorem 4.4 in
*Iterative Methods for Sparse Linear Systems*): an M-matrix is invertible with a nonnegative
inverse, which is exactly the right-hand side of
`Stationary.Splitting.IsRegular.complexSpectralRadius_lt_one_iff`. -/
theorem complexSpectralRadius_lt_one_of_isMMatrix (hA : A.IsMMatrix) :
    s.iterationOperator.complexSpectralRadius < 1 :=
  hs.complexSpectralRadius_lt_one_iff.2 ⟨hA.isUnit, hA.inv_entrywiseNonneg⟩

end IsRegular

end Stationary.Splitting
