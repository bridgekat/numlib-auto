/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Projection.Coordinate
import Numlib.Stationary.Splitting

/-!
# Block splittings and block relaxation

This module gives the block form of the classical iterations ([saad2003iterative], §4.1.1,
(4.15)–(4.17), and Algorithms 4.1–4.2 in the non-overlapping case). The block structure is a
labelling $\pi \colon n \to \iota$ of the index set by a linearly ordered type $\iota$ of block
labels. For a square matrix $A$, the **block diagonal part** $D$, the **strict block-lower part**
$-E$ and the **strict block-upper part** $-F$ of $A$ keep the entries $a_{ij}$ with
$\pi(i) = \pi(j)$, with $\pi(j) < \pi(i)$ and with $\pi(i) < \pi(j)$, respectively, and set the
other entries to $0$. They give $A = D - E - F$, which is (4.15) of [saad2003iterative]. The point
splittings are the case $\pi = \mathrm{id}$. The block Jacobi, block Gauss–Seidel and block SOR
splittings ([saad2003iterative], (4.16) and Algorithms 4.1–4.2) are built here as the point
splittings are, under the hypothesis that $D$ is invertible.

The last section reads block Jacobi and block Gauss–Seidel as projection processes over the blocks
([saad2003iterative], §5.4). Each block $i$ gives a Petrov–Galerkin pair whose trial and test space
is the coordinate subspace $V_i$ of the vectors supported in block $i$. The pair is nondegenerate
because $D$ is invertible. Then one block Jacobi step is one step of the additive projection process
over these pairs, with unit weights, and one block Gauss–Seidel sweep is one sweep of the
multiplicative projection process over them, in increasing order of the label.

## Main definitions

* `Matrix.blockJacobiSplitting`: the block Jacobi splitting, $M = D$.
* `Matrix.blockGaussSeidelSplitting`: the block Gauss–Seidel splitting, $M = D - E$.
* `Matrix.blockSORSplitting`: the block SOR splitting, $M = \omega^{-1} (D - \omega E)$.

## Main results

* `Matrix.blockDiagPart_sub_blockDiagonal'` and `Matrix.blockStrictLower_sub_blockDiagonal'`: for an
  index set that is a sigma type labelled by its first component, subtracting a block diagonal
  matrix changes only the block diagonal part.
* `Matrix.isUnit_blockDiagPart_add_blockStrictLower`: if $D$ is invertible, then $D - E$ is
  invertible.
* `Matrix.isNondegeneratePair_blockSubspace`: if $D$ is invertible, each pair $(V_i, V_i)$ is a
  nondegenerate Petrov–Galerkin pair for $A$.
* `Matrix.blockJacobiSplitting_step_eq_additiveStep`: one block Jacobi step is one additive
  projection step over the blocks.
* `Matrix.blockGaussSeidelSplitting_step_eq_multiplicativeStep`: one block Gauss–Seidel sweep is one
  multiplicative projection sweep over the blocks.

## Implementation notes

* The three parts of $A$ are `Matrix.blockDiagPart π A`, `Matrix.blockStrictLower π A` and
  `Matrix.blockStrictUpper π A` of `Numlib.LinearAlgebra.Matrix.Triangular`, so $E$ is
  `-blockStrictLower π A` and $F$ is `-blockStrictUpper π A`. Their sum is $A$
  (`Matrix.blockDiagPart_add_blockStrictLower_add_blockStrictUpper`), and for $\pi = \mathrm{id}$
  they are the point parts (`Matrix.blockDiagPart_id`, `Matrix.blockStrictLower_id`,
  `Matrix.blockStrictUpper_id`).
* The invertibility of $D - \omega E$ rests on `Matrix.BlockTriangular.det`, which factors the
  determinant of a block triangular matrix as the product of the determinants of its diagonal
  blocks. Adding the strict block-lower part changes no diagonal block, and so it does not change
  the determinant. Therefore the label type $\iota$ needs only a linear order, and need not be
  finite.
* Overlapping blocks, as in the general Algorithm 4.1 of [saad2003iterative], where the index sets
  need not partition the index set, are not formalized. The source proves no theorem about them.
* The coordinate subspace $V_i$ is `EuclideanSpace.blockSubspace 𝕜 π i`, and a matrix acts on
  vectors through `Matrix.toEuclideanLin`.
-/

namespace Matrix

open Stationary

variable {n ι R : Type*}

/-! ### Block diagonal matrices -/

section BlockDiagonal

variable {m' : ι → Type*} [AddGroup R]

/-- Let the index set be a sigma type $\Sigma_i m_i$, labelled by the first component, let $A$ be a
square matrix on it, and let $\operatorname{diag}(D_i)$ be the block diagonal matrix with the
blocks $D_i$. Then the block diagonal part of $A - \operatorname{diag}(D_i)$ is the block
diagonal part of $A$ minus $\operatorname{diag}(D_i)$.

The block diagonal matrix is `Matrix.blockDiagonal' D`. For this labelling, it is its own block
diagonal part. -/
theorem blockDiagPart_sub_blockDiagonal' [DecidableEq ι]
    (A : Matrix ((i : ι) × m' i) ((i : ι) × m' i) R) (D : ∀ i, Matrix (m' i) (m' i) R) :
    blockDiagPart Sigma.fst (A - blockDiagonal' D)
      = blockDiagPart Sigma.fst A - blockDiagonal' D := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [blockDiagPart_apply, Matrix.sub_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [blockDiagonal'_apply_ne _ a b h]; simp [h]

/-- Let the index set be a sigma type $\Sigma_i m_i$, labelled by the first component, let $A$ be a
square matrix on it, and let $\operatorname{diag}(D_i)$ be the block diagonal matrix with the
blocks $D_i$. Then $A - \operatorname{diag}(D_i)$ and $A$ have the same strict block-lower part. -/
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
/-- For every scalar $c$, the matrix $cD - E$ is block triangular for the reverse order of the
labels. -/
private theorem blockTriangular_smul_add_blockStrictLower (c : 𝕜) (A : Matrix n n 𝕜) :
    BlockTriangular (c • blockDiagPart π A + blockStrictLower π A) (OrderDual.toDual ∘ π) := by
  intro i j hij
  have h : π i < π j := hij
  simp [h.ne, asymm h]

/-- For every scalar $c$, $\det(cD - E) = \det(cD)$, because adding the strict block-lower part
changes no diagonal block. -/
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

/-- Let $c \neq 0$ be a scalar and let the block diagonal part $D$ of $A$ be invertible. Then
$cD - E$ is invertible, where $-E$ is the strict block-lower part of $A$.

The matrix $cD - E$ is block triangular with the same diagonal blocks as $cD$. This makes the
block Gauss–Seidel and block SOR splittings well defined. -/
theorem isUnit_smul_blockDiagPart_add_blockStrictLower {c : 𝕜} (hc : c ≠ 0)
    (h : IsUnit (blockDiagPart π A)) :
    IsUnit (c • blockDiagPart π A + blockStrictLower π A) := by
  rw [isUnit_iff_isUnit_det] at h ⊢
  rw [det_smul_add_blockStrictLower, det_smul, isUnit_iff_ne_zero] at *
  exact mul_ne_zero (pow_ne_zero _ hc) h

/-- Let the block diagonal part $D$ of a square matrix $A$ over a field be invertible. Then the
block-lower part $D - E$ of $A$ is invertible.

In Lean, $D - E$ is `blockDiagPart π A + blockStrictLower π A`. -/
theorem isUnit_blockDiagPart_add_blockStrictLower (h : IsUnit (blockDiagPart π A)) :
    IsUnit (blockDiagPart π A + blockStrictLower π A) := by
  simpa using isUnit_smul_blockDiagPart_add_blockStrictLower (c := (1 : 𝕜)) one_ne_zero h

/-- Let $A$ be a square matrix over a field whose block diagonal part $D$ for the labelling $\pi$ is
invertible. The **block Jacobi splitting** of $A$ is the splitting $A = M - N$ with $M = D$
([saad2003iterative], (4.16)).

For $\pi = \mathrm{id}$ it is `Matrix.jacobiSplitting`. -/
noncomputable def blockJacobiSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) : Splitting A :=
  ⟨blockDiagPart π A, h⟩

/-- The block Jacobi splitting has $N = E + F$, the negative of the sum of the strict block-lower
part and the strict block-upper part of $A$. -/
theorem blockJacobiSplitting_n (π : n → ι) (A : Matrix n n 𝕜) (h : IsUnit (blockDiagPart π A)) :
    (blockJacobiSplitting π A h).n = -(blockStrictLower π A + blockStrictUpper π A) := by
  change blockDiagPart π A - A = -(blockStrictLower π A + blockStrictUpper π A)
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← add_assoc,
    blockDiagPart_add_blockStrictLower_add_blockStrictUpper, sub_self]

/-- Let $A$ be a square matrix over a field whose block diagonal part $D$ for the labelling $\pi$ is
invertible. The **block Gauss–Seidel splitting** of $A$ is the splitting $A = M - N$ with
$M = D - E$, the block-lower part of $A$ ([saad2003iterative], Algorithm 4.1).

For $\pi = \mathrm{id}$ it is `Matrix.gaussSeidelSplitting`. -/
noncomputable def blockGaussSeidelSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) : Splitting A :=
  ⟨blockDiagPart π A + blockStrictLower π A, isUnit_blockDiagPart_add_blockStrictLower h⟩

/-- The block Gauss–Seidel splitting has $N = F$, the negative of the strict block-upper part of
$A$: the forward sweep takes the whole block-lower triangle. -/
theorem blockGaussSeidelSplitting_n (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) :
    (blockGaussSeidelSplitting π A h).n = -blockStrictUpper π A := by
  change blockDiagPart π A + blockStrictLower π A - A = -blockStrictUpper π A
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub,
    blockDiagPart_add_blockStrictLower_add_blockStrictUpper, sub_self]

/-- Let $A$ be a square matrix over a field whose block diagonal part $D$ for the labelling $\pi$ is
invertible, and let $\omega \neq 0$. The **block SOR splitting** of $A$ with relaxation
parameter $\omega$ is the splitting $A = M - N$ with
$$M = \omega^{-1} (D - \omega E) = \omega^{-1} D - E$$
([saad2003iterative], Algorithm 4.2).

For $\pi = \mathrm{id}$ it is `Matrix.sorSplitting`. -/
noncomputable def blockSORSplitting (π : n → ι) (A : Matrix n n 𝕜)
    (h : IsUnit (blockDiagPart π A)) {ω : 𝕜} (hω : ω ≠ 0) : Splitting A :=
  ⟨ω⁻¹ • blockDiagPart π A + blockStrictLower π A,
    isUnit_smul_blockDiagPart_add_blockStrictLower (inv_ne_zero hω) h⟩

/-- The block SOR splitting with $\omega = 1$ is the block Gauss–Seidel splitting. -/
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

/-- The $k$-th entry of `toEuclideanLin M v` is $\sum_j M_{kj} v_j$. -/
private theorem toEuclideanLin_apply_eq_sum_mul (M : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n)
    (k : n) : toEuclideanLin M v k = ∑ j, M k j * v j := rfl

/-- The restriction of $v$ to block $i$: the vector with the entries of $v$ on block $i$ and $0$
elsewhere. -/
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
  simp [WithLp.ofLp_sum]

/-- If $v$ is supported in block $i$ and row $k$ belongs to block $i$, then $(Dv)_k = (Av)_k$. -/
private theorem blockDiag_apply_of_eq {i : ι} {v : EuclideanSpace 𝕜 n}
    (hv : v ∈ blockSubspace 𝕜 π i) {k : n} (hk : π k = i) :
    toEuclideanLin (blockDiagPart π A) v k = toEuclideanLin A v k := by
  rw [toEuclideanLin_apply_eq_sum_mul, toEuclideanLin_apply_eq_sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : π j = i
  · rw [blockDiagPart_apply, ite_eq_left (hk.trans hj.symm)]
  · rw [hv j hj, mul_zero, mul_zero]

/-- If $v$ is supported in block $i$ and row $k$ does not belong to block $i$, then $(Dv)_k = 0$. -/
private theorem blockDiag_apply_of_ne {i : ι} {v : EuclideanSpace 𝕜 n}
    (hv : v ∈ blockSubspace 𝕜 π i) {k : n} (hk : π k ≠ i) :
    toEuclideanLin (blockDiagPart π A) v k = 0 := by
  rw [toEuclideanLin_apply_eq_sum_mul]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : π j = i
  · rw [blockDiagPart_apply, ite_eq_right (by rw [hj]; exact hk), zero_mul]
  · rw [hv j hj, mul_zero]

/-- If row $k$ belongs to block $i$, then $(Dv)_k$ is not changed when $v$ is replaced by its
restriction to block $i$. -/
private theorem blockDiag_blockRestrict_apply (i : ι) (v : EuclideanSpace 𝕜 n) {k : n}
    (hk : π k = i) : toEuclideanLin (blockDiagPart π A) (blockRestrict π i v) k
      = toEuclideanLin (blockDiagPart π A) v k := by
  rw [toEuclideanLin_apply_eq_sum_mul, toEuclideanLin_apply_eq_sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : π j = i
  · rw [blockRestrict_apply, ite_eq_left hj]
  · rw [blockDiagPart_apply, ite_eq_right (by rw [hk]; exact fun hc => hj hc.symm), zero_mul,
      zero_mul]

/-- If $v$ is supported in block $i$ and the label of row $k$ is at least $i$, then
$((D - E) v)_k = (Av)_k$. -/
private theorem blockLower_apply_of_le {i : ι} {v : EuclideanSpace 𝕜 n}
    (hv : v ∈ blockSubspace 𝕜 π i) {k : n} (hk : i ≤ π k) :
    toEuclideanLin (blockDiagPart π A + blockStrictLower π A) v k = toEuclideanLin A v k := by
  rw [toEuclideanLin_apply_eq_sum_mul, toEuclideanLin_apply_eq_sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : π j = i
  · rw [Matrix.add_apply, blockDiagPart_apply, blockStrictLower_apply]
    rcases hk.lt_or_eq with hlt | heq
    · rw [ite_eq_right (by rw [hj]; exact fun hc => absurd hc.symm hlt.ne),
        ite_eq_left (by rw [hj]; exact hlt), zero_add]
    · rw [ite_eq_left (by rw [hj, heq]),
        ite_eq_right (by rw [hj, heq]; exact lt_irrefl _), add_zero]
  · rw [hv j hj, mul_zero, mul_zero]

/-- If $v$ vanishes on every block with label at most $i$, then $((D - E) v)_k = 0$ for every row
$k$ with label at most $i$. -/
private theorem blockLower_apply_eq_zero {i : ι} {v : EuclideanSpace 𝕜 n}
    (hv : ∀ j, ¬ i < π j → v j = 0) {k : n} (hk : π k ≤ i) :
    toEuclideanLin (blockDiagPart π A + blockStrictLower π A) v k = 0 := by
  rw [toEuclideanLin_apply_eq_sum_mul]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i < π j
  · have h1 : π k < π j := lt_of_le_of_lt hk hj
    rw [Matrix.add_apply, blockDiagPart_apply, blockStrictLower_apply, ite_eq_right h1.ne,
      ite_eq_right (asymm h1), add_zero, zero_mul]
  · rw [hv j hj, mul_zero]

/-- Let $A$ be a square matrix over $\mathbb{R}$ or $\mathbb{C}$ whose block diagonal part is
invertible, and let $i$ be a label. Let $V_i$ be the subspace of the vectors supported in block
$i$. Then $(V_i, V_i)$ is a nondegenerate Petrov–Galerkin pair for $A$: the trial space and the
test space have the same dimension, and if $z \in V_i$ and $Az \perp V_i$, then $z = 0$.

On a vector supported in block $i$, the rows of block $i$ reproduce the diagonal block of $A$,
so this diagonal block is the matrix that must be inverted. This is the hypothesis under which
the block relaxations are projection processes ([saad2003iterative], §5.4). The pair condition
is `Projection.IsNondegeneratePair` for `Matrix.toEuclideanLin A`. -/
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

/-- Let the set of labels be finite, let $A$ be a square matrix over $\mathbb{R}$ or $\mathbb{C}$
whose block diagonal part $D$ is invertible, and let $b$ and $x$ be vectors. Then one step of
the additive projection process over the pairs $(V_i, V_i)$, with all relaxation weights equal
to $1$, maps $x$ to
$$x + D^{-1} (b - Ax),$$
which is one block Jacobi step. This is §5.4 of [saad2003iterative]: (4.17) read as (5.7).

Each block contributes the Petrov–Galerkin correction of its pair. The corrections are added
together because they are all computed from the same iterate $x$. The additive step is
`Projection.additiveStep`, and $D$ is the matrix `(Matrix.blockJacobiSplitting π A h).m`. -/
theorem blockJacobiSplitting_step_eq_additiveStep [Fintype ι] (h : IsUnit (blockDiagPart π A))
    (b x : EuclideanSpace 𝕜 n) :
    additiveStep (toEuclideanLin A) b (blockSubspace 𝕜 π) (blockSubspace 𝕜 π)
        (isNondegeneratePair_blockSubspace h) 1 x
      = x + toEuclideanLin ((blockJacobiSplitting π A h).m)⁻¹ (b - toEuclideanLin A x) := by
  have hm : (blockJacobiSplitting π A h).m = blockDiagPart π A := rfl
  set d : EuclideanSpace 𝕜 n :=
    toEuclideanLin (blockDiagPart π A)⁻¹ (b - toEuclideanLin A x) with hd
  have hMd : toEuclideanLin (blockDiagPart π A) d = b - toEuclideanLin A x :=
    toEuclideanLin_mul_nonsing_inv_apply h _
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

/-- After a multiplicative sweep over a strictly increasing list $l$ of labels, the accumulated
correction $\delta$ is supported on the blocks in $l$ and satisfies
$((D - E) \delta)_k = (b - Ax)_k$ in every row $k$ of these blocks. -/
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

/-- Let the set of labels be finite, let $A$ be a square matrix over $\mathbb{R}$ or $\mathbb{C}$
whose block diagonal part $D$ is invertible, and let $b$ and $x$ be vectors. Then one sweep of
the multiplicative projection process over the pairs $(V_i, V_i)$, taken in increasing order of
the label, maps $x$ to
$$x + (D - E)^{-1} (b - Ax),$$
which is one block Gauss–Seidel step. This is §5.4 and Algorithm 5.6 of [saad2003iterative].

Unlike the additive process, each correction is computed from the iterate that the previous
correction produced. When block $i$ is processed, the blocks below it are already updated and
the blocks above it still have their old values, which is the pattern of the rows of $D - E$. So
the accumulated correction solves $(D - E) \delta = b - Ax$. The sweep is
`Projection.multiplicativeStep` over the list `Finset.sort Finset.univ` of all labels, and
$D - E$ is the matrix `(Matrix.blockGaussSeidelSplitting π A h).m`. -/
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
