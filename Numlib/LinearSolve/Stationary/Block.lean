import Mathlib.LinearAlgebra.Matrix.Block
import Numlib.LinearSolve.Projection.Coordinate
import Numlib.LinearSolve.Stationary.Splitting

/-!
# Block splittings and block relaxation

The block form of the classical iterations ([saad2003iterative] §4.1.1, (4.15)–(4.17), Algorithms
4.1–4.2 in the non-overlapping case). The block structure is a *labelling* `π : n → ι` of the index
set by a linearly ordered type of block labels, and the block-diagonal, strict block-lower and
strict block-upper parts of `A` are the entries with `π i = π j`, `π j < π i` and `π i < π j`
respectively (`Matrix.blockDiagPart`, `Matrix.blockStrictLower`, `Matrix.blockStrictUpper`). They
add up to `A` (`Matrix.blockDiagPart_add_blockStrictLower_add_blockStrictUpper`), which is
[saad2003iterative] `A = D - E - F` of (4.15) with `E = -blockStrictLower π A` and `F =
-blockStrictUpper π A`. When the index set is a sigma type labelled by its first component,
a genuinely block diagonal summand lands entirely in the block diagonal part
(`Matrix.blockDiagPart_sub_blockDiagonal'`, `Matrix.blockStrictLower_sub_blockDiagonal'`).

The point splittings of `Numlib/LinearSolve/Stationary/Splitting.lean` are the case `π = id`
(`Matrix.blockDiagPart_id`, `Matrix.blockStrictLower_id`, `Matrix.blockStrictUpper_id`), and the
block Jacobi, Gauss–Seidel and SOR splittings ([saad2003iterative] (4.16), Algorithms 4.1–4.2) are
built here exactly as the point ones are, under the invertibility of the block diagonal.

The last section reads the two of them as *projection processes* over the blocks
([saad2003iterative] §5.4): each block gives a Petrov–Galerkin pair whose trial and test space is
the coordinate subspace of the block (`EuclideanSpace.blockSubspace`), nondegenerate exactly because
the block diagonal is invertible (`Matrix.isNondegeneratePair_blockSubspace`), and then one block
Jacobi step is one *additive* step over those pairs with unit weights
(`Matrix.blockJacobiSplitting_step_eq_additiveStep`) while one block Gauss–Seidel sweep is the
*multiplicative* sweep over them in increasing order of the block label
(`Matrix.blockGaussSeidelSplitting_step_eq_multiplicativeStep`).

## Implementation notes

Invertibility of the block-lower factor `D - ω E` rests on `Matrix.BlockTriangular.det`, which
factors the determinant of a block triangular matrix as the product of the determinants of its
diagonal blocks over `Finset.univ.image π`: adding the strict block-lower part changes no diagonal
block, hence changes no determinant. So no finiteness of the label type `ι` is needed, only a
`LinearOrder` on it.

Overlapping blocks — [saad2003iterative] general Algorithm 4.1, in which the index sets need not
partition `n` — are not formalized; the book proves no theorem about them.
-/

namespace Matrix

open Stationary

variable {n ι R : Type*}

/-! ### The three block parts of a matrix -/

section Parts

variable [Zero R]

/-- The **block diagonal part** of `A` for the block labelling `π`: the entries whose row and column
carry the same label, [saad2003iterative] `D` of (4.15). -/
def blockDiagPart [DecidableEq ι] (π : n → ι) (A : Matrix n n R) : Matrix n n R :=
  Matrix.of fun i j => if π i = π j then A i j else 0

/-- Entries of the block diagonal part: those whose row and column carry the same label. -/
@[simp]
theorem blockDiagPart_apply [DecidableEq ι] (π : n → ι) (A : Matrix n n R) (i j : n) :
    blockDiagPart π A i j = if π i = π j then A i j else 0 := rfl

/-- The **strict block-lower part** of `A` for the block labelling `π`, [saad2003iterative] `-E` of
(4.15). -/
def blockStrictLower [LinearOrder ι] (π : n → ι) (A : Matrix n n R) : Matrix n n R :=
  Matrix.of fun i j => if π j < π i then A i j else 0

/-- Entries of the strict block-lower part: those whose column label is below the row label. -/
@[simp]
theorem blockStrictLower_apply [LinearOrder ι] (π : n → ι) (A : Matrix n n R) (i j : n) :
    blockStrictLower π A i j = if π j < π i then A i j else 0 := rfl

/-- The **strict block-upper part** of `A` for the block labelling `π`, [saad2003iterative] `-F` of
(4.15). -/
def blockStrictUpper [LinearOrder ι] (π : n → ι) (A : Matrix n n R) : Matrix n n R :=
  Matrix.of fun i j => if π i < π j then A i j else 0

/-- Entries of the strict block-upper part: those whose row label is below the column label. -/
@[simp]
theorem blockStrictUpper_apply [LinearOrder ι] (π : n → ι) (A : Matrix n n R) (i j : n) :
    blockStrictUpper π A i j = if π i < π j then A i j else 0 := rfl

end Parts

section Decomposition

variable [LinearOrder ι] [AddCommMonoid R] (π : n → ι) (A : Matrix n n R)

/-- **[saad2003iterative] (4.15)**: a matrix is the sum of its block-diagonal, strict block-lower
and strict block-upper parts, which in [saad2003iterative] letters is `A = D - E - F`. -/
theorem blockDiagPart_add_blockStrictLower_add_blockStrictUpper :
    blockDiagPart π A + blockStrictLower π A + blockStrictUpper π A = A := by
  ext i j
  simp only [Matrix.add_apply, blockDiagPart_apply, blockStrictLower_apply,
    blockStrictUpper_apply]
  rcases lt_trichotomy (π i) (π j) with h | h | h
  · simp [h, h.ne, asymm h]
  · simp [h]
  · simp [h, h.ne', asymm h]

/-- With the identity labelling the block diagonal part is the diagonal part. -/
@[simp]
theorem blockDiagPart_id [DecidableEq n] (A : Matrix n n R) :
    blockDiagPart id A = diagPart A := by
  ext i j
  rw [blockDiagPart_apply, diagPart, Matrix.diagonal_apply]
  split <;> simp_all [Matrix.diag]

/-- With the identity labelling the strict block-lower part is the strictly lower part. -/
@[simp]
theorem blockStrictLower_id [LinearOrder n] (A : Matrix n n R) :
    blockStrictLower id A = strictLower A := rfl

/-- With the identity labelling the strict block-upper part is the strictly upper part. -/
@[simp]
theorem blockStrictUpper_id [LinearOrder n] (A : Matrix n n R) :
    blockStrictUpper id A = strictUpper A := rfl

end Decomposition

/-! ### Block diagonal matrices -/

section BlockDiagonal

variable {m' : ι → Type*} [AddGroup R]

/-- Subtracting a block diagonal matrix changes the block diagonal part by exactly that matrix: the
labelling by the block index sees a block diagonal matrix as diagonal. -/
theorem blockDiagPart_sub_blockDiagonal' [DecidableEq ι]
    (A : Matrix ((i : ι) × m' i) ((i : ι) × m' i) R) (D : ∀ i, Matrix (m' i) (m' i) R) :
    blockDiagPart Sigma.fst (A - blockDiagonal' D)
      = blockDiagPart Sigma.fst A - blockDiagonal' D := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [blockDiagPart_apply, Matrix.sub_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [blockDiagonal'_apply_ne _ a b h]; simp [h]

/-- Subtracting a block diagonal matrix leaves the strict block-lower part unchanged. -/
theorem blockStrictLower_sub_blockDiagonal' [LinearOrder ι]
    (A : Matrix ((i : ι) × m' i) ((i : ι) × m' i) R) (D : ∀ i, Matrix (m' i) (m' i) R) :
    blockStrictLower Sigma.fst (A - blockDiagonal' D) = blockStrictLower Sigma.fst A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [blockStrictLower_apply, Matrix.sub_apply]
  by_cases h : j < i
  · rw [blockDiagonal'_apply_ne _ a b (ne_of_gt h)]; simp [h]
  · simp [h]

end BlockDiagonal

/-! ### The block splittings -/

section Splittings

variable {𝕜 : Type*} [Field 𝕜] [Fintype n] [DecidableEq n] [LinearOrder ι] {π : n → ι}
variable {A : Matrix n n 𝕜}

omit [Fintype n] [DecidableEq n] in
/-- A scaled block diagonal plus the strict block-lower part is block triangular for the reversed
labelling. -/
private theorem blockTriangular_smul_add_blockStrictLower (c : 𝕜) (A : Matrix n n 𝕜) :
    BlockTriangular (c • blockDiagPart π A + blockStrictLower π A) (OrderDual.toDual ∘ π) := by
  intro i j hij
  have h : π i < π j := hij
  simp [h.ne, asymm h]

/-- Adding the strict block-lower part changes no diagonal block, hence no determinant. -/
private theorem det_smul_add_blockStrictLower (c : 𝕜) (A : Matrix n n 𝕜) :
    (c • blockDiagPart π A + blockStrictLower π A).det = (c • blockDiagPart π A).det := by
  have hD : BlockTriangular (c • blockDiagPart π A) (OrderDual.toDual ∘ π) := by
    intro i j hij
    have h : π i < π j := hij
    simp [h.ne]
  rw [(blockTriangular_smul_add_blockStrictLower (π := π) c A).det, hD.det]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  ext i j
  have hij : π i.1 = π j.1 := i.2.trans j.2.symm
  change (c • blockDiagPart π A + blockStrictLower π A) i.1 j.1
    = (c • blockDiagPart π A) i.1 j.1
  simp [hij]

/-- **The block-lower factor of a block relaxation is invertible** as soon as the block diagonal is:
it is block triangular with the same diagonal blocks. This is what makes the block Gauss–Seidel and
block SOR splittings well defined. -/
theorem isUnit_smul_blockDiagPart_add_blockStrictLower {c : 𝕜} (hc : c ≠ 0)
    (h : IsUnit (blockDiagPart π A)) :
    IsUnit (c • blockDiagPart π A + blockStrictLower π A) := by
  rw [isUnit_iff_isUnit_det] at h ⊢
  rw [det_smul_add_blockStrictLower, det_smul, isUnit_iff_ne_zero] at *
  exact mul_ne_zero (pow_ne_zero _ hc) h

/-- `D - E`, the block-lower part of `A` in [saad2003iterative] letters, is invertible as soon as
the block diagonal of `A` is. -/
theorem isUnit_blockDiagPart_add_blockStrictLower (h : IsUnit (blockDiagPart π A)) :
    IsUnit (blockDiagPart π A + blockStrictLower π A) := by
  simpa using isUnit_smul_blockDiagPart_add_blockStrictLower (c := (1 : 𝕜)) one_ne_zero h

/-- **Block Jacobi** ([saad2003iterative], (4.16)): `M = D`, the block diagonal part. With `π = id`
it is `Matrix.jacobiSplitting`. -/
noncomputable def blockJacobiSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) : Splitting A :=
  ⟨blockDiagPart π A, h⟩

/-- The complementary part of the block Jacobi splitting is `-(E + F)`. -/
theorem blockJacobiSplitting_n (π : n → ι) (A : Matrix n n 𝕜) (h : IsUnit (blockDiagPart π A)) :
    (blockJacobiSplitting π A h).n = -(blockStrictLower π A + blockStrictUpper π A) := by
  change blockDiagPart π A - A = -(blockStrictLower π A + blockStrictUpper π A)
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← add_assoc,
    blockDiagPart_add_blockStrictLower_add_blockStrictUpper, sub_self]

/-- **Block Gauss–Seidel** ([saad2003iterative], Algorithm 4.1): `M = D - E`, the block-lower part.
With `π = id` it is `Matrix.gaussSeidelSplitting`. -/
noncomputable def blockGaussSeidelSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) : Splitting A :=
  ⟨blockDiagPart π A + blockStrictLower π A, isUnit_blockDiagPart_add_blockStrictLower h⟩

/-- The complementary part of the block Gauss–Seidel splitting is `-F`: the forward sweep absorbs
the whole block-lower triangle. -/
theorem blockGaussSeidelSplitting_n (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) :
    (blockGaussSeidelSplitting π A h).n = -blockStrictUpper π A := by
  change blockDiagPart π A + blockStrictLower π A - A = -blockStrictUpper π A
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub,
    blockDiagPart_add_blockStrictLower_add_blockStrictUpper, sub_self]

/-- **Block SOR** ([saad2003iterative], Algorithm 4.2) with parameter `ω`: `M = ω⁻¹ (D - ω E)`. With
`π = id` it is `Matrix.sorSplitting`. -/
noncomputable def blockSORSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) {ω : 𝕜} (hω : ω ≠ 0) : Splitting A :=
  ⟨ω⁻¹ • blockDiagPart π A + blockStrictLower π A,
    isUnit_smul_blockDiagPart_add_blockStrictLower (inv_ne_zero hω) h⟩

/-- Block Gauss–Seidel is block SOR with `ω = 1`. -/
theorem blockSORSplitting_one (π : n → ι) (A : Matrix n n 𝕜) (h : IsUnit (blockDiagPart π A)) :
    blockSORSplitting π A h (one_ne_zero (α := 𝕜)) = blockGaussSeidelSplitting π A h := by
  ext : 1
  change (1 : 𝕜)⁻¹ • blockDiagPart π A + blockStrictLower π A
    = blockDiagPart π A + blockStrictLower π A
  rw [inv_one, one_smul]

end Splittings

/-! ### Block relaxation as a projection process -/

section ProjectionProcess

open EuclideanSpace Projection

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [LinearOrder ι]
variable {π : n → ι} {A : Matrix n n 𝕜}

/-- Entries of `toEuclideanLin M v` are the entries of `M *ᵥ v`. -/
private theorem toEuclideanLin_apply_eq_sum (M : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) (k : n) :
    toEuclideanLin M v k = ∑ j, M k j * v j := rfl

omit [Fintype n] [DecidableEq n] in
/-- Entries of a finite sum in `EuclideanSpace` are the sums of the entries. -/
private theorem euclideanSpace_sum_apply {κ : Type*} (s : Finset κ)
    (f : κ → EuclideanSpace 𝕜 n) (j : n) : (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

/-- The restriction of `v` to the `i`-th block: the entries of `v` on the block, zero elsewhere. -/
private def blockRestrict (π : n → ι) (i : ι) (v : EuclideanSpace 𝕜 n) : EuclideanSpace 𝕜 n :=
  WithLp.toLp 2 fun j => if π j = i then v j else 0

omit [Fintype n] [DecidableEq n] in
@[simp]
private theorem blockRestrict_apply (i : ι) (v : EuclideanSpace 𝕜 n) (j : n) :
    blockRestrict π i v j = if π j = i then v j else 0 := rfl

omit [Fintype n] [DecidableEq n] in
private theorem blockRestrict_mem (i : ι) (v : EuclideanSpace 𝕜 n) :
    blockRestrict π i v ∈ blockSubspace 𝕜 π i := fun _ hj => ite_eq_right hj

omit [Fintype n] [DecidableEq n] in
private theorem sum_blockRestrict [Fintype ι] (v : EuclideanSpace 𝕜 n) :
    ∑ i, blockRestrict π i v = v := by
  refine PiLp.ext fun j => ?_
  rw [euclideanSpace_sum_apply]
  simp

/-- On a vector supported in the `i`-th block, a row of that block sees only the block diagonal. -/
private theorem blockDiag_apply_of_eq {i : ι} {v : EuclideanSpace 𝕜 n}
    (hv : v ∈ blockSubspace 𝕜 π i) {k : n} (hk : π k = i) :
    toEuclideanLin (blockDiagPart π A) v k = toEuclideanLin A v k := by
  rw [toEuclideanLin_apply_eq_sum, toEuclideanLin_apply_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : π j = i
  · rw [blockDiagPart_apply, ite_eq_left (hk.trans hj.symm)]
  · rw [hv j hj, mul_zero, mul_zero]

/-- Outside the `i`-th block the block diagonal annihilates a vector supported in that block. -/
private theorem blockDiag_apply_of_ne {i : ι} {v : EuclideanSpace 𝕜 n}
    (hv : v ∈ blockSubspace 𝕜 π i) {k : n} (hk : π k ≠ i) :
    toEuclideanLin (blockDiagPart π A) v k = 0 := by
  rw [toEuclideanLin_apply_eq_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : π j = i
  · rw [blockDiagPart_apply, ite_eq_right (by rw [hj]; exact hk), zero_mul]
  · rw [hv j hj, mul_zero]

/-- The block diagonal does not see the entries of `v` outside the block of the row. -/
private theorem blockDiag_blockRestrict_apply (i : ι) (v : EuclideanSpace 𝕜 n) {k : n}
    (hk : π k = i) : toEuclideanLin (blockDiagPart π A) (blockRestrict π i v) k
      = toEuclideanLin (blockDiagPart π A) v k := by
  rw [toEuclideanLin_apply_eq_sum, toEuclideanLin_apply_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : π j = i
  · rw [blockRestrict_apply, ite_eq_left hj]
  · rw [blockDiagPart_apply, ite_eq_right (by rw [hk]; exact fun hc => hj hc.symm), zero_mul,
      zero_mul]

/-- On a vector supported in the `i`-th block, a row whose label is at least `i` sees the same in
the block-lower part `D - E` as in `A` itself: the diagonal block contributes for a row of block
`i` and the strict block-lower part for a row below it. -/
private theorem blockLower_apply_of_le {i : ι} {v : EuclideanSpace 𝕜 n}
    (hv : v ∈ blockSubspace 𝕜 π i) {k : n} (hk : i ≤ π k) :
    toEuclideanLin (blockDiagPart π A + blockStrictLower π A) v k = toEuclideanLin A v k := by
  rw [toEuclideanLin_apply_eq_sum, toEuclideanLin_apply_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : π j = i
  · rw [Matrix.add_apply, blockDiagPart_apply, blockStrictLower_apply]
    rcases hk.lt_or_eq with hlt | heq
    · rw [ite_eq_right (by rw [hj]; exact fun hc => absurd hc.symm hlt.ne),
        ite_eq_left (by rw [hj]; exact hlt), zero_add]
    · rw [ite_eq_left (by rw [hj, heq]),
        ite_eq_right (by rw [hj, heq]; exact lt_irrefl _), add_zero]
  · rw [hv j hj, mul_zero, mul_zero]

/-- A vector supported on blocks with labels above `i` is annihilated by the block-lower part
`D - E` in every row whose label is at most `i`. -/
private theorem blockLower_apply_eq_zero {i : ι} {v : EuclideanSpace 𝕜 n}
    (hv : ∀ j, ¬ i < π j → v j = 0) {k : n} (hk : π k ≤ i) :
    toEuclideanLin (blockDiagPart π A + blockStrictLower π A) v k = 0 := by
  rw [toEuclideanLin_apply_eq_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i < π j
  · have h1 : π k < π j := lt_of_le_of_lt hk hj
    rw [Matrix.add_apply, blockDiagPart_apply, blockStrictLower_apply, ite_eq_right h1.ne,
      ite_eq_right (asymm h1), add_zero, zero_mul]
  · rw [hv j hj, mul_zero]

/-- **Each block is a nondegenerate Petrov–Galerkin pair** as soon as the block diagonal is
invertible: on a vector supported in the block, the rows of the block reproduce the diagonal block,
which is therefore what has to be inverted.  This is the hypothesis under which the block
relaxations are projection processes ([saad2003iterative], §5.4). -/
theorem isNondegeneratePair_blockSubspace (h : IsUnit (blockDiagPart π A)) (i : ι) :
    IsNondegeneratePair (toEuclideanLin A) (blockSubspace 𝕜 π i) (blockSubspace 𝕜 π i) where
  finrank_eq := rfl
  eq_zero_of_mem_orthogonal z hz hAz := by
    have hzero : toEuclideanLin (blockDiagPart π A) z = 0 := by
      refine PiLp.ext fun k => ?_
      rw [PiLp.zero_apply]
      by_cases hk : π k = i
      · rw [blockDiag_apply_of_eq hz hk]
        exact mem_orthogonal_blockSubspace.1 hAz k hk
      · exact blockDiag_apply_of_ne hz hk
    have hinv : (blockDiagPart π A)⁻¹ * blockDiagPart π A = 1 :=
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 h)
    calc z = toEuclideanLin ((blockDiagPart π A)⁻¹ * blockDiagPart π A) z := by
          rw [hinv, Matrix.toLpLin_one, LinearMap.id_apply]
      _ = toEuclideanLin (blockDiagPart π A)⁻¹ (toEuclideanLin (blockDiagPart π A) z) := by
          rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]
      _ = 0 := by rw [hzero, map_zero]

/-- Applying the inverse of an invertible matrix undoes the matrix. -/
private theorem toEuclideanLin_inv_apply {M : Matrix n n 𝕜} (hM : IsUnit M)
    (v : EuclideanSpace 𝕜 n) : toEuclideanLin M (toEuclideanLin M⁻¹ v) = v := by
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
    Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM), Matrix.toLpLin_one,
    LinearMap.id_apply]

/-- **[saad2003iterative], §5.4**: one **block Jacobi** step is one step of the *additive*
projection process over the blocks, with all relaxation weights equal to `1`.  Each block
contributes the Petrov–Galerkin correction of the pair `K i = L i = ` the coordinate subspace of
the block, and the corrections are added at once because they are all computed from the same
iterate; their sum is the block Jacobi correction `D⁻¹ (b - A x)`, which is [saad2003iterative]
(4.17) read as (5.7). -/
theorem blockJacobiSplitting_step_eq_additiveStep [Fintype ι] (h : IsUnit (blockDiagPart π A))
    (b x : EuclideanSpace 𝕜 n) :
    additiveStep (toEuclideanLin A) b (blockSubspace 𝕜 π) (blockSubspace 𝕜 π)
        (isNondegeneratePair_blockSubspace h) 1 x
      = x + toEuclideanLin ((blockJacobiSplitting π A h).m)⁻¹ (b - toEuclideanLin A x) := by
  have hm : (blockJacobiSplitting π A h).m = blockDiagPart π A := rfl
  set d : EuclideanSpace 𝕜 n :=
    toEuclideanLin (blockDiagPart π A)⁻¹ (b - toEuclideanLin A x) with hd
  have hMd : toEuclideanLin (blockDiagPart π A) d = b - toEuclideanLin A x :=
    toEuclideanLin_inv_apply h _
  have hstep : ∀ i : ι, pairStep (toEuclideanLin A) b (blockSubspace 𝕜 π i)
      (blockSubspace 𝕜 π i) (isNondegeneratePair_blockSubspace h i) x
        = x + blockRestrict π i d := by
    intro i
    refine (pairStep_isPetrovGalerkin (isNondegeneratePair_blockSubspace h i) x).eq_of_forall
      ⟨?_, ?_⟩ (isNondegeneratePair_blockSubspace h i).eq_zero_of_mem_orthogonal
    · rw [add_sub_cancel_left]
      exact blockRestrict_mem i d
    · refine mem_orthogonal_blockSubspace.2 fun k hk => ?_
      rw [PiLp.sub_apply, map_add, PiLp.add_apply,
        blockDiag_apply_of_eq (blockRestrict_mem i d) hk |>.symm,
        blockDiag_blockRestrict_apply i d hk, hMd, PiLp.sub_apply]
      ring
  rw [additiveStep, hm]
  congr 1
  rw [← hd, ← sum_blockRestrict (π := π) d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hstep i, Pi.one_apply, one_smul, add_sub_cancel_left]

/-- The invariant of a partial multiplicative sweep over an increasing list `l` of block labels:
the correction it has accumulated is supported on the blocks of `l`, and in every row of those
blocks it satisfies the block Gauss–Seidel equation `(D - E) δ = b - A x`.  The second clause is
what makes the sweep a *solve* with the block-lower factor: at the moment block `i` is processed
the blocks below it are already updated and the ones above it are still at their old values, which
is exactly the pattern of the rows of `D - E`. -/
private theorem multiplicativeStep_invariant (h : IsUnit (blockDiagPart π A))
    (b : EuclideanSpace 𝕜 n) (l : List ι) (hl : l.Pairwise (· < ·)) (x : EuclideanSpace 𝕜 n) :
    (∀ j, π j ∉ l → (multiplicativeStep (toEuclideanLin A) b (blockSubspace 𝕜 π)
        (blockSubspace 𝕜 π) (isNondegeneratePair_blockSubspace h) l x - x) j = 0) ∧
      (∀ k, π k ∈ l → toEuclideanLin (blockDiagPart π A + blockStrictLower π A)
        (multiplicativeStep (toEuclideanLin A) b (blockSubspace 𝕜 π) (blockSubspace 𝕜 π)
          (isNondegeneratePair_blockSubspace h) l x - x) k = (b - toEuclideanLin A x) k) := by
  induction l generalizing x with
  | nil => exact ⟨fun j _ => by rw [multiplicativeStep, List.foldl_nil, sub_self, PiLp.zero_apply],
      fun k hk => absurd hk (List.not_mem_nil)⟩
  | cons i l ih =>
    obtain ⟨hi, hl'⟩ := List.pairwise_cons.1 hl
    set y := pairStep (toEuclideanLin A) b (blockSubspace 𝕜 π i) (blockSubspace 𝕜 π i)
      (isNondegeneratePair_blockSubspace h i) x with hy
    have hstep : multiplicativeStep (toEuclideanLin A) b (blockSubspace 𝕜 π) (blockSubspace 𝕜 π)
        (isNondegeneratePair_blockSubspace h) (i :: l) x
          = multiplicativeStep (toEuclideanLin A) b (blockSubspace 𝕜 π) (blockSubspace 𝕜 π)
            (isNondegeneratePair_blockSubspace h) l y := rfl
    obtain ⟨hsupp, hkey⟩ := ih hl' y
    set z := multiplicativeStep (toEuclideanLin A) b (blockSubspace 𝕜 π) (blockSubspace 𝕜 π)
      (isNondegeneratePair_blockSubspace h) l y with hz
    obtain ⟨hw, hyorth⟩ :
        IsPetrovGalerkin (toEuclideanLin A) b x (blockSubspace 𝕜 π i) (blockSubspace 𝕜 π i) y :=
      pairStep_isPetrovGalerkin (isNondegeneratePair_blockSubspace h i) x
    have hdiff : z - x = (y - x) + (z - y) := by abel
    have hsupp' : ∀ j, ¬ i < π j → (z - y) j = 0 := by
      intro j hj
      refine hsupp j fun hmem => hj ?_
      exact hi _ hmem
    refine ⟨fun j hj => ?_, fun k hk => ?_⟩
    · rw [hstep, hdiff, PiLp.add_apply, hsupp j fun hm => hj (List.mem_cons_of_mem _ hm),
        hw j fun hc => hj (hc ▸ List.mem_cons_self), add_zero]
    · rw [hstep, hdiff, map_add, PiLp.add_apply]
      rcases List.mem_cons.1 hk with hki | hki
      · rw [blockLower_apply_eq_zero hsupp' hki.le, add_zero,
          blockLower_apply_of_le hw hki.ge, map_sub, PiLp.sub_apply]
        have := mem_orthogonal_blockSubspace.1 hyorth k hki
        rw [PiLp.sub_apply] at this
        rw [PiLp.sub_apply]
        linear_combination (norm := ring_nf) -this
      · rw [hkey k hki, blockLower_apply_of_le hw (hi _ hki).le, map_sub, PiLp.sub_apply,
          PiLp.sub_apply, PiLp.sub_apply]
        ring

/-- **[saad2003iterative], §5.4, Algorithm 5.6**: one **block Gauss–Seidel** sweep is one sweep of
the *multiplicative* projection process over the blocks, taken in increasing order of the block
label.  Unlike the additive process each correction is computed from the iterate the previous one
produced, and the accumulated correction therefore solves the block-lower system
`(D - E) δ = b - A x`, which is the block Gauss–Seidel step. -/
theorem blockGaussSeidelSplitting_step_eq_multiplicativeStep [Fintype ι]
    (h : IsUnit (blockDiagPart π A)) (b x : EuclideanSpace 𝕜 n) :
    multiplicativeStep (toEuclideanLin A) b (blockSubspace 𝕜 π) (blockSubspace 𝕜 π)
        (isNondegeneratePair_blockSubspace h) (Finset.sort (Finset.univ : Finset ι)) x
      = x + toEuclideanLin ((blockGaussSeidelSplitting π A h).m)⁻¹ (b - toEuclideanLin A x) := by
  have hm : (blockGaussSeidelSplitting π A h).m = blockDiagPart π A + blockStrictLower π A := rfl
  obtain ⟨-, hkey⟩ := multiplicativeStep_invariant h b (Finset.sort (Finset.univ : Finset ι))
    (Finset.sortedLT_sort _).pairwise x
  set z := multiplicativeStep (toEuclideanLin A) b (blockSubspace 𝕜 π) (blockSubspace 𝕜 π)
    (isNondegeneratePair_blockSubspace h) (Finset.sort (Finset.univ : Finset ι)) x with hz
  have hsolve : toEuclideanLin (blockDiagPart π A + blockStrictLower π A) (z - x)
      = b - toEuclideanLin A x :=
    PiLp.ext fun k => hkey k ((Finset.mem_sort _).2 (Finset.mem_univ _))
  have hMinv : z - x = toEuclideanLin (blockDiagPart π A + blockStrictLower π A)⁻¹
      (b - toEuclideanLin A x) := by
    rw [← hsolve, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1
        (isUnit_blockDiagPart_add_blockStrictLower h)), Matrix.toLpLin_one, LinearMap.id_apply]
  rw [hm, ← hMinv, add_sub_cancel]

end ProjectionProcess

end Matrix
