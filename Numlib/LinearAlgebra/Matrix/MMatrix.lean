/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.MonotoneConvergence
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.Order
import Numlib.LinearAlgebra.Matrix.PerronFrobenius

/-!
# The nonnegative Neumann criterion and M-matrices

Let $B \in \mathbb{R}^{n \times n}$ be entrywise nonnegative. The **nonnegative Neumann criterion**
says that the spectral radius satisfies $\rho(B) < 1$ if and only if $I - B$ is invertible with an
entrywise nonnegative inverse ([saad2003iterative], Theorem 1.29). An **M-matrix** is a real square
matrix with nonpositive off-diagonal entries that is invertible with an entrywise nonnegative
inverse ([saad2003iterative], Definition 1.30). This file proves the criterion and develops the
theory of M-matrices: the spectral characterization through the Jacobi operator $I - D^{-1} A$, the
comparison theorem, the discrete maximum principle, the M-criterion of [quarteroni2000numerical],
Property 1.19, with its sufficient conditions, the theorem of [fan1960note] on one step of Gaussian
elimination, and the Stieltjes matrices, which are the symmetric M-matrices.

The results use the entrywise order of `Numlib.LinearAlgebra.Matrix.Order` and the spectral radius
`Matrix.complexSpectralRadius` of `Numlib.LinearAlgebra.Matrix.Complexify`, and none of them
mentions an iteration. The regular splittings of `Numlib.Stationary.RegularSplitting` and the
incomplete factorizations of `Numlib.Preconditioner.ILU` use them.

## Main definitions

* `Matrix.IsZMatrix`: a square matrix whose off-diagonal entries are nonpositive.
* `Matrix.IsMMatrix`: an M-matrix ([saad2003iterative], Definition 1.30). The clause of the source
  that the diagonal is positive is the derived result `Matrix.IsMMatrix.diag_pos`.
* `Matrix.IsStieltjes`: a Stieltjes matrix, that is, a positive definite matrix with nonpositive
  off-diagonal entries ([golub2013matrix], §11.5.8).

## Main results

* `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff`: the nonnegative Neumann criterion.
* `Matrix.isMMatrix_iff_complexSpectralRadius_lt_one`: a Z-matrix $A$ with positive diagonal $D$ is
  an M-matrix if and only if $\rho(I - D^{-1} A) < 1$.
* `Matrix.IsMMatrix.of_entrywiseLE`: the comparison theorem. A Z-matrix that dominates an M-matrix
  entrywise is an M-matrix. This justifies the dropping step of an incomplete factorization.
* `Matrix.IsMMatrix.nonneg_of_mulVec_nonneg` and `Matrix.IsMMatrix.norm_inv_mulVec_le`: the discrete
  maximum principle ($Ax \ge 0$ implies $x \ge 0$) and the comparison principle ($\|A^{-1}
  \tau\|_\infty \le \|w\|_\infty \|\tau\|_\infty$ for a vector $w$ with $Aw = \mathbf{1}$). A
  convergence proof for a finite-difference scheme takes these two facts from an M-matrix.
* `Matrix.isMMatrix_iff_exists_pos_mulVec_pos`: the M-criterion of [quarteroni2000numerical],
  Property 1.19. A Z-matrix $A$ is an M-matrix if and only if $Aw > 0$ for some $w > 0$. Its
  consequences are the sufficient conditions: strict diagonal dominance ([quarteroni2000numerical],
  Property 1.20, `Matrix.IsStrictDiagDominant.isMMatrix`), weak diagonal dominance with
  nonsingularity (`Matrix.isMMatrix_of_isDiagDominant_of_isUnit`, and hence the irreducibly dominant
  case `Matrix.isMMatrix_of_isIrreduciblyDiagDominant`), and positive definiteness
  (`Matrix.isMMatrix_of_forall_dotProduct_mulVec_pos`, with the Stieltjes case
  `Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos`).
* `Matrix.IsMMatrix.schurComplementSingle`: the theorem of [fan1960note] ([saad2003iterative],
  Theorem 10.1). One step of Gaussian elimination (`Matrix.schurComplementSingle`) takes an M-matrix
  to an M-matrix. The proof uses `Matrix.inv_schurComplementSingle`: the inverse of the Schur
  complement of a $1 \times 1$ pivot is the submatrix of $A^{-1}$ off the pivot.
* `Matrix.isStieltjes_iff_isMMatrix_isSymm`: the Stieltjes matrices are the symmetric M-matrices.
  The hard half is `Matrix.IsMMatrix.posDef_of_isSymm`.
* `Matrix.IsStieltjes.inv_entrywiseNonneg`, `Matrix.IsStieltjes.of_entrywiseLE`,
  `Matrix.IsStieltjes.submatrix`, `Matrix.IsStieltjes.schurComplementSingle`,
  `Matrix.IsStieltjes.sub_drop`: a Stieltjes matrix has a nonnegative inverse ([golub2013matrix],
  Lemma 11.5.1), and the Stieltjes property is preserved when off-diagonal entries increase, under
  principal submatrices, and under an elimination step, with or without dropped entries of the pivot
  column ([golub2013matrix], Theorem 11.5.2). Incomplete Cholesky factorization needs these facts.

## Proof outline

Both directions of the Neumann criterion come from one identity. If $C$ is a right inverse of
$I - B$, then $$\sum_{j < k} B^j = C - B^k C$$ (`Matrix.geom_sum_eq_sub_pow_mul`). For the forward
direction, $\rho(B) < 1$ gives $B^k \to 0$, so the partial sums converge to $C$. Each partial sum is
entrywise nonnegative and the nonnegative matrices form a closed set, so $C$ is nonnegative.

For the backward direction, textbooks use the Perron–Frobenius theorem: $\rho(B)$ is an eigenvalue
of the nonnegative matrix $B$ with a nonnegative eigenvector, and a test of $C$ against this
eigenvector forces $\rho(B) < 1$. This is not necessary. If $C$ is nonnegative, then so is $B^k C$,
so the identity shows that every partial sum $\sum_{j < k} B^j$ is bounded above by $C$, entry by
entry. The partial sums are also nondecreasing, because the terms are nonnegative. A bounded
monotone sequence of reals converges, so its increments $B^k$ tend to $0$ entrywise, which is
$\rho(B) < 1$. The argument is monotone convergence in $\mathbb{R}$, one entry at a time. It needs
no eigenvector, no irreducibility and no compactness.

## Implementation notes

* The spectral radius $\rho(B)$ of a real matrix is `Matrix.complexSpectralRadius B`, the spectral
  radius of its complexification, with values in `ENNReal`.
* The irreducible Perron–Frobenius theorem is a separate development in
  `Numlib.LinearAlgebra.Matrix.PerronFrobenius`. Neither that theorem nor the Neumann criterion
  implies the other easily.
* For vectors, $\|\cdot\|$ is the norm of `n → ℝ`, which is the maximum norm $\|\cdot\|_\infty$.
-/

open Filter Finset
open scoped Topology Matrix

namespace Matrix

variable {m n : Type*}

/-- Let $f$ be a family of entrywise nonnegative real matrices indexed by $\iota$, let $l$ be a
filter on $\iota$ that is not trivial, and let $f \to A$ along $l$. Then $A$ is entrywise
nonnegative. So the cone of nonnegative matrices is closed.

The statement uses a filter instead of a sequence, because the proof is `ge_of_tendsto` in each
entry. This is the only fact about the entrywise order that needs a topology. It is in this
module and not in `Numlib.LinearAlgebra.Matrix.Order`, so that
`Numlib.LinearAlgebra.Matrix.Order` stays free of analysis and can be upstreamed as pure order
theory. -/
theorem EntrywiseNonneg.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → Matrix m n ℝ}
    {A : Matrix m n ℝ} (hf : ∀ i, (f i).EntrywiseNonneg) (h : Tendsto f l (𝓝 A)) :
    A.EntrywiseNonneg :=
  entrywiseNonneg_iff.2 fun i j =>
    ge_of_tendsto (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) j)
      (.of_forall fun k => (hf k).apply i j)

variable [Fintype n] [DecidableEq n]

/-- Let $B, C \in \mathbb{R}^{n \times n}$ with $(I - B) C = I$, and let $k \in \mathbb{N}$. Then
the partial sum of the Neumann series of $B$ is $$\sum_{j < k} B^j = C - B^k C.$$

Only a right inverse $C$ is needed. The proof multiplies `Finset.geom_sum_mul_neg` by $C$. -/
theorem geom_sum_eq_sub_pow_mul {B C : Matrix n n ℝ} (hC : (1 - B) * C = 1) (k : ℕ) :
    ∑ j ∈ range k, B ^ j = C - B ^ k * C :=
  calc ∑ j ∈ range k, B ^ j
      = (∑ j ∈ range k, B ^ j) * ((1 - B) * C) := by rw [hC, mul_one]
    _ = ((∑ j ∈ range k, B ^ j) * (1 - B)) * C := (mul_assoc _ _ _).symm
    _ = (1 - B ^ k) * C := by rw [geom_sum_mul_neg]
    _ = C - B ^ k * C := by rw [sub_mul, one_mul]

/-- The **nonnegative Neumann criterion** ([saad2003iterative], Theorem 1.29). Let
$B \in \mathbb{R}^{n \times n}$ be entrywise nonnegative. Then $\rho(B) < 1$ if and only if
$I - B$ is invertible and $(I - B)^{-1}$ is entrywise nonnegative.

The forward direction is the Neumann series with nonnegative terms. The backward direction reads
the same series as a monotone sequence bounded above by $(I - B)^{-1}$; no Perron–Frobenius
theorem is used (see the proof outline of the module). The spectral radius is
`Matrix.complexSpectralRadius B`. -/
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
      rw [geom_sum_eq_sub_pow_mul hC k, Matrix.sub_apply]
      simpa using ((hB.pow k).mul hCnn).apply i j
    have hmono : ∀ i j, Monotone fun k => (∑ x ∈ range k, B ^ x) i j := fun i j =>
      monotone_nat_of_le_succ fun k => by
        rw [sum_range_succ, Matrix.add_apply]
        simpa using (hB.pow k).apply i j
    refine (tendsto_pow_iff_complexSpectralRadius_lt_one B).1 ?_
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have hlim := tendsto_atTop_ciSup (hmono i j) ⟨(1 - B)⁻¹ i j, by
      rintro _ ⟨k, rfl⟩; exact hle k i j⟩
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa [Function.comp_def, sum_range_succ] using this

omit [Fintype n] [DecidableEq n] in
/-- A square matrix $A$ over an ordered type is a **Z-matrix** if all its off-diagonal entries are
nonpositive: $a_{ij} \le 0$ for $i \neq j$.

The term is the one of the Mathlib module `Mathlib.LinearAlgebra.Matrix.ZMatrix`, which has no
predicate for it. The M-matrices `Matrix.IsMMatrix` are the Z-matrices that are invertible with
an entrywise nonnegative inverse. -/
def IsZMatrix {α : Type*} [Zero α] [LE α] (A : Matrix n n α) : Prop :=
  ∀ i j, i ≠ j → A i j ≤ 0

omit [Fintype n] [DecidableEq n] in
/-- A matrix $A$ is a Z-matrix if and only if $a_{ij} \le 0$ for all $i \neq j$. -/
theorem isZMatrix_iff {α : Type*} [Zero α] [LE α] {A : Matrix n n α} :
    A.IsZMatrix ↔ ∀ i j, i ≠ j → A i j ≤ 0 := Iff.rfl

/-- An **M-matrix** ([saad2003iterative], Definition 1.30) is a matrix
$A \in \mathbb{R}^{n \times n}$ such that $a_{ij} \le 0$ for all $i \neq j$, $A$ is invertible,
and $A^{-1}$ is entrywise nonnegative.

The definition of the source also requires $a_{ii} > 0$. This condition follows from the other
three: see `Matrix.IsMMatrix.diag_pos`. -/
structure IsMMatrix (A : Matrix n n ℝ) : Prop where
  /-- The off-diagonal entries are nonpositive: $a_{ij} \le 0$ for $i \neq j$. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  /-- The matrix is invertible. -/
  isUnit : IsUnit A
  /-- The inverse is entrywise nonnegative. -/
  inv_entrywiseNonneg : A⁻¹.EntrywiseNonneg

/-- An M-matrix is a Z-matrix. -/
theorem IsMMatrix.isZMatrix {A : Matrix n n ℝ} (hA : A.IsMMatrix) : A.IsZMatrix :=
  hA.offDiag_nonpos

namespace IsMMatrix

variable {A : Matrix n n ℝ} (hA : A.IsMMatrix)
include hA

/-- The diagonal entries of an M-matrix $A$ are positive: $a_{ii} > 0$ for every $i$. This is the
first clause of [saad2003iterative], Definition 1.30, which Theorem 1.32 of the source derives
from the other clauses.

The proof reads $(A A^{-1})_{ii} = 1$ entrywise. Every off-diagonal term $a_{ik} (A^{-1})_{ki}$
is nonpositive, so $a_{ii} (A^{-1})_{ii} \ge 1$, and this forces both factors to be positive. -/
theorem diag_pos (i : n) : 0 < A i i := by
  have hdet : IsUnit A.det := isUnit_iff_isUnit_det _ |>.1 hA.isUnit
  have hrow : ∑ k, A i k * A⁻¹ k i = 1 := by
    have := congrArg (fun M : Matrix n n ℝ => M i i) (mul_nonsing_inv A hdet)
    simpa [Matrix.mul_apply] using this
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

/-- The entries of the Jacobi operator $I - D^{-1} A$, where $D$ is the diagonal of $A$, are
$\delta_{ij} - a_{ii}^{-1} a_{ij}$. -/
private theorem one_sub_diagInv_mul_apply (A : Matrix n n ℝ) (i j : n) :
    ((1 : Matrix n n ℝ) - diagonal (fun i => (A i i)⁻¹) * A) i j
      = (1 : Matrix n n ℝ) i j - (A i i)⁻¹ * A i j := by
  rw [Matrix.sub_apply, diagonal_mul]

/-- The Jacobi operator $I - D^{-1} A$ of a Z-matrix $A$ with positive diagonal is entrywise
nonnegative. -/
private theorem entrywiseNonneg_one_sub_diagInv_mul (hoff : A.IsZMatrix)
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

/-- If the diagonal $D$ of $A$ has no zero entry, then $D^{-1} D = I$. -/
private theorem diagInv_mul_diag (hdiag : ∀ i, A i i ≠ 0) :
    (diagonal fun i => (A i i)⁻¹) * (diagonal fun i => A i i) = 1 := by
  rw [diagonal_mul_diagonal,
    show (fun i => (A i i)⁻¹ * A i i) = fun _ : n => (1 : ℝ) from
      funext fun i => inv_mul_cancel₀ (hdiag i),
    diagonal_one]

/-- If the diagonal $D$ of $A$ has no zero entry, then $D D^{-1} = I$. -/
private theorem diag_mul_diagInv (hdiag : ∀ i, A i i ≠ 0) :
    (diagonal fun i => A i i) * (diagonal fun i => (A i i)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal,
    show (fun i => A i i * (A i i)⁻¹) = fun _ : n => (1 : ℝ) from
      funext fun i => mul_inv_cancel₀ (hdiag i),
    diagonal_one]

/-- The **spectral characterization of an M-matrix** ([saad2003iterative], Theorem 1.31). Let
$A \in \mathbb{R}^{n \times n}$ be a Z-matrix with positive diagonal entries, and let $D$ be the
diagonal of $A$. Then $A$ is an M-matrix if and only if $$\rho(I - D^{-1} A) < 1.$$

Both directions apply the nonnegative Neumann criterion
`Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff` to $B = I - D^{-1} A$, for which
$I - B = D^{-1} A$. The matrix $D^{-1} A$ is nonsingular exactly when $A$ is, and
$(D^{-1} A)^{-1} = A^{-1} D$ is entrywise nonnegative exactly when $A^{-1}$ is, because the
diagonal is positive. -/
theorem isMMatrix_iff_complexSpectralRadius_lt_one (hoff : A.IsZMatrix)
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

/-- The **comparison theorem for M-matrices** ([saad2003iterative], Theorem 1.33). Let
$A, B \in \mathbb{R}^{n \times n}$, let $A$ be an M-matrix, let $a_{ij} \le b_{ij}$ for all
$i, j$, and let $B$ be a Z-matrix. Then $B$ is an M-matrix.

The diagonals satisfy $0 < a_{ii} \le b_{ii}$, and entrywise
$0 \le I - D_B^{-1} B \le I - D_A^{-1} A$, because $a_{ij} / a_{ii} \le b_{ij} / b_{ii}$ when
the nonpositive numerator increases and the positive denominator also increases. The
monotonicity of the spectral radius (`Matrix.complexSpectralRadius_le_of_entrywiseLE`) and
`Matrix.isMMatrix_iff_complexSpectralRadius_lt_one` complete the proof. This theorem justifies
the dropping step of an incomplete factorization: to discard a nonpositive off-diagonal entry
moves the matrix up in the entrywise order. -/
theorem IsMMatrix.of_entrywiseLE (hA : A.IsMMatrix) (hAB : A ≤ₑ B)
    (hoff : B.IsZMatrix) : B.IsMMatrix := by
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

/-- For an M-matrix $A$ and every vector $x$, $A^{-1}(Ax) = x$. -/
private theorem IsMMatrix.inv_mulVec_mulVec (x : n → ℝ) : A⁻¹ *ᵥ (A *ᵥ x) = x := by
  rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hA.isUnit), one_mulVec]

/-- The **discrete maximum principle** of an M-matrix. Let $A \in \mathbb{R}^{n \times n}$ be an
M-matrix and let $x \in \mathbb{R}^n$. If $Ax \ge 0$ entrywise, then $x \ge 0$ entrywise.

This is the property that [quarteroni2000numerical], §12.2 and §12.5.2, call the discrete
maximum principle: the discrete solution is nonnegative when the datum is nonnegative. The proof
is $x = A^{-1}(Ax)$ with $A^{-1} \ge 0$. -/
theorem IsMMatrix.nonneg_of_mulVec_nonneg {x : n → ℝ} (hx : 0 ≤ A *ᵥ x) : 0 ≤ x := by
  rw [← hA.inv_mulVec_mulVec x]
  exact hA.inv_entrywiseNonneg.mulVec_nonneg hx

/-- The discrete maximum principle in the form of [quarteroni2000numerical], §1.12. Let
$A \in \mathbb{R}^{n \times n}$ be an M-matrix and let $x \in \mathbb{R}^n$. If $Ax \le 0$
entrywise, then $x \le 0$ entrywise. -/
theorem IsMMatrix.nonpos_of_mulVec_nonpos {x : n → ℝ} (hx : A *ᵥ x ≤ 0) : x ≤ 0 :=
  neg_nonneg.1 (hA.nonneg_of_mulVec_nonneg (x := -x) (by rw [mulVec_neg]; exact neg_nonneg.2 hx))

/-- Let $A \in \mathbb{R}^{n \times n}$ be an M-matrix, and let $\sigma, \tau \in \mathbb{R}^n$ with
$\sigma \le \tau$ entrywise. Then $A^{-1} \sigma \le A^{-1} \tau$ entrywise. -/
theorem IsMMatrix.inv_mulVec_le_inv_mulVec {σ τ : n → ℝ} (h : σ ≤ τ) : A⁻¹ *ᵥ σ ≤ A⁻¹ *ᵥ τ :=
  hA.inv_entrywiseNonneg.mulVec_mono h

/-- Let $A \in \mathbb{R}^{n \times n}$ be an M-matrix and let $\tau \in \mathbb{R}^n$. Then,
entrywise, $$|A^{-1} \tau| \le A^{-1} |\tau|.$$ This is the triangle inequality, because the
entrywise absolute value of $A^{-1}$ is $A^{-1}$. -/
theorem IsMMatrix.abs_inv_mulVec_le (τ : n → ℝ) : |A⁻¹ *ᵥ τ| ≤ A⁻¹ *ᵥ |τ| := by
  have habs : A⁻¹.abs = A⁻¹ :=
    Matrix.ext fun i j => abs_of_nonneg (hA.inv_entrywiseNonneg.apply i j)
  simpa [habs] using abs_mulVec_le A⁻¹ τ

/-- The **comparison principle**. Let $A \in \mathbb{R}^{n \times n}$ be an M-matrix, and let
$w \in \mathbb{R}^n$ be a **comparison vector**, that is, $Aw = \mathbf{1}$, the vector of ones.
Then for every $\tau \in \mathbb{R}^n$, $$\|A^{-1} \tau\|_\infty \le \|w\|_\infty
\|\tau\|_\infty.$$

Entrywise, $|A^{-1} \tau| \le A^{-1} |\tau| \le \|\tau\|_\infty A^{-1} \mathbf{1} =
\|\tau\|_\infty w$, by two uses of $A^{-1} \ge 0$. This is the stability half of the convergence
proof for the finite-difference discretization of a two-point boundary value problem
([quarteroni2000numerical], Theorem 12.1, where (12.28) is the case $w_j = x_j (1 - x_j) / 2$,
$\|w\|_\infty \le 1/8$, for the matrix $\operatorname{tridiag}(-1, 2, -1) / h^2$), and of its
two-dimensional counterpart in §12.6 of the source. The comparison vector replaces the explicit
discrete Green's function of the source. The norm $\|\cdot\|$ of `n → ℝ` is the maximum norm. -/
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

/-!
### The M-criterion, and the sufficient conditions

The criterion of [quarteroni2000numerical], Property 1.19, says that a Z-matrix $A$ is an M-matrix
exactly when $Aw$ is entrywise positive for some entrywise positive $w$. The backward direction is a
bound on the spectral radius of the Jacobi operator $B = I - D^{-1} A$, which is nonnegative with
$Bw < w$. The conjugation by $\operatorname{diag}(w)$ gives a nonnegative matrix whose row sums are
$(Bw)_i / w_i < 1$, so its maximum absolute row sum is less than one. Each of the sufficient
conditions that follow (strict diagonal dominance, irreducible diagonal dominance with
nonsingularity, positive definiteness) is a choice of $w$.
-/

section Criterion

section Operator

open scoped Matrix.Norms.Operator

omit [DecidableEq n] in
/-- The **strict Collatz–Wielandt bound**. Let $B \in \mathbb{R}^{n \times n}$ be entrywise
nonnegative, and let $w \in \mathbb{R}^n$ be entrywise positive with $(Bw)_i < w_i$ for every
$i$. Then $\rho(B) < 1$.

With $W = \operatorname{diag}(w)$, the matrix $W^{-1} B W$ is nonnegative with row sums
$(Bw)_i / w_i < 1$. So its maximum absolute row sum, which bounds the spectral radius, is less
than one. -/
theorem EntrywiseNonneg.complexSpectralRadius_lt_one_of_mulVec_lt {B : Matrix n n ℝ}
    (hB : B.EntrywiseNonneg) {w : n → ℝ} (hw : ∀ i, 0 < w i) (hBw : ∀ i, (B *ᵥ w) i < w i) :
    complexSpectralRadius B < 1 := by
  classical
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

/-- The **M-criterion** ([quarteroni2000numerical], Property 1.19). Let
$A \in \mathbb{R}^{n \times n}$ be a Z-matrix. Then $A$ is an M-matrix if and only if there is a
vector $w \in \mathbb{R}^n$ with $w_i > 0$ and $(Aw)_i > 0$ for every $i$.

For the forward direction, $w = A^{-1} \mathbf{1}$ has $Aw = \mathbf{1}$, and each $w_i$ is a
row sum of the nonnegative matrix $A^{-1}$, which is positive because no row of an invertible
matrix is zero. For the backward direction, $(Aw)_i > 0$ forces $a_{ii} > 0$, because the
off-diagonal terms are nonpositive. The nonnegative Jacobi operator $B = I - D^{-1} A$ has
$Bw = w - D^{-1}(Aw) < w$ entrywise, so $\rho(B) < 1$ by
`Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_of_mulVec_lt`, and
`Matrix.isMMatrix_iff_complexSpectralRadius_lt_one` concludes. -/
theorem isMMatrix_iff_exists_pos_mulVec_pos {A : Matrix n n ℝ} (hoff : A.IsZMatrix) :
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
      rw [Matrix.mul_apply, one_apply_eq] at h1
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

/-- Let $A \in \mathbb{R}^{n \times n}$ be a Z-matrix with positive row sums: $\sum_j a_{ij} > 0$
for every $i$. Then $A$ is an M-matrix. This is [quarteroni2000numerical], Property 1.20, in the
form of row sums.

For a Z-matrix, positive row sums are the same as strict row diagonal dominance with a positive
diagonal, which is the hypothesis of the source (`Matrix.IsStrictDiagDominant.isMMatrix`). The
proof is the M-criterion with $w = \mathbf{1}$. -/
theorem isMMatrix_of_forall_sum_pos {A : Matrix n n ℝ} (hoff : A.IsZMatrix)
    (hsum : ∀ i, 0 < ∑ j, A i j) : A.IsMMatrix :=
  (isMMatrix_iff_exists_pos_mulVec_pos hoff).2
    ⟨1, fun _ => zero_lt_one, fun i => by simpa [mulVec_apply_eq_sum] using hsum i⟩

/-- For a row $i$ of a Z-matrix, the sum of the absolute values of the off-diagonal entries is the
negative of the sum of these entries: $\sum_{j \neq i} |a_{ij}| = -\sum_{j \neq i} a_{ij}$. -/
private theorem sum_erase_norm_eq_neg_sum {A : Matrix n n ℝ} (hoff : A.IsZMatrix)
    (i : n) : ∑ j ∈ univ.erase i, ‖A i j‖ = -∑ j ∈ univ.erase i, A i j := by
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun j hj => by
    rw [Real.norm_eq_abs, abs_of_nonpos (hoff i j (mem_erase.1 hj).1.symm)]

/-- [quarteroni2000numerical], Property 1.20. Let $A \in \mathbb{R}^{n \times n}$ be strictly row
diagonally dominant, $\sum_{j \neq i} |a_{ij}| < |a_{ii}|$ for every $i$, with positive diagonal
entries and nonpositive off-diagonal entries. Then $A$ is an M-matrix. -/
theorem IsStrictDiagDominant.isMMatrix {A : Matrix n n ℝ} (hA : A.IsStrictDiagDominant)
    (hdiag : ∀ i, 0 < A i i) (hoff : A.IsZMatrix) : A.IsMMatrix := by
  refine isMMatrix_of_forall_sum_pos hoff fun i => ?_
  have h := hA i
  rw [sum_erase_norm_eq_neg_sum hoff, Real.norm_eq_abs, abs_of_pos (hdiag i)] at h
  rw [← add_sum_erase _ _ (mem_univ i)]
  linarith

/-- Let $A \in \mathbb{R}^{n \times n}$ be weakly row diagonally dominant,
$\sum_{j \neq i} |a_{ij}| \le |a_{ii}|$ for every $i$, let $A$ be invertible, and let $A$ have
positive diagonal entries and nonpositive off-diagonal entries. Then $A$ is an M-matrix.

Let $w = A^{-1} \mathbf{1}$, so that $Aw = \mathbf{1}$. The least entry $w_{i_0}$ is positive:
if $w_{i_0} \le 0$, row $i_0$ gives $1 = \sum_j a_{i_0 j} w_j \le w_{i_0} \sum_j a_{i_0 j} \le
0$. The first inequality holds because the off-diagonal coefficients are nonpositive and
$w_j \ge w_{i_0}$, and the second because the row sum is nonnegative by weak dominance. Then the
M-criterion applies. -/
theorem isMMatrix_of_isDiagDominant_of_isUnit {A : Matrix n n ℝ} (hA : A.IsDiagDominant)
    (hu : IsUnit A) (hdiag : ∀ i, 0 < A i i) (hoff : A.IsZMatrix) : A.IsMMatrix := by
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

/-- Let $A \in \mathbb{R}^{n \times n}$ be irreducibly diagonally dominant, with positive diagonal
entries and nonpositive off-diagonal entries. Then $A$ is an M-matrix. This is the irreducible
companion of [quarteroni2000numerical], Property 1.20, and the grid matrices of §3.14.2 of the
source satisfy it.

Irreducible dominance gives nonsingularity (`Matrix.IsIrreduciblyDiagDominant.isUnit`) and weak
dominance, and `Matrix.isMMatrix_of_isDiagDominant_of_isUnit` completes the proof. -/
theorem isMMatrix_of_isIrreduciblyDiagDominant {A : Matrix n n ℝ}
    (hA : A.IsIrreduciblyDiagDominant) (hdiag : ∀ i, 0 < A i i)
    (hoff : A.IsZMatrix) : A.IsMMatrix :=
  isMMatrix_of_isDiagDominant_of_isUnit hA.isDiagDominant hA.isUnit hdiag hoff

/-- Let $A \in \mathbb{R}^{n \times n}$ be a Z-matrix that is positive definite in the sense of
[quarteroni2000numerical], Definition 1.22: $x^T A x > 0$ for every $x \neq 0$, with no symmetry
assumed. Then $A$ is an M-matrix.

Positive definiteness makes $A$ nonsingular. Let $w = A^{-1} \mathbf{1}$, and split
$w = w^+ - w^-$ into its positive and negative parts. The pairing of $Aw = \mathbf{1}$ with
$w^-$ gives $\sum_i w^-_i = (w^-)^T A w^+ - (w^-)^T A w^- \le 0$: the first form involves only
off-diagonal entries, because the two parts have disjoint supports, and the second form is
nonnegative. So $w \ge 0$, and then $w > 0$, because $w_i = 0$ would give $(Aw)_i \le 0$. The
M-criterion concludes. No spectral theory is used. -/
theorem isMMatrix_of_forall_dotProduct_mulVec_pos {A : Matrix n n ℝ}
    (hpd : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) (hoff : A.IsZMatrix) :
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

/-- **Stieltjes matrices are M-matrices.** Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive
definite with nonpositive off-diagonal entries. Then $A$ is an M-matrix.

The proof does not use the symmetry; see `Matrix.isMMatrix_of_forall_dotProduct_mulVec_pos`.
Examples are the model Laplacian $\operatorname{tridiag}(-1, 2, -1)$, its Kronecker sums and the
five-point Laplacian. -/
theorem IsMMatrix.of_posDef_of_offDiag_nonpos {A : Matrix n n ℝ} (hA : A.PosDef)
    (hoff : A.IsZMatrix) : A.IsMMatrix :=
  isMMatrix_of_forall_dotProduct_mulVec_pos
    (fun x hx => by simpa using hA.dotProduct_mulVec_pos hx) hoff

end Criterion

/-! ### One step of Gaussian elimination on the smaller index type -/

section KyFan

/-- The **theorem of Ky Fan** ([fan1960note]; [saad2003iterative], Theorem 10.1). Let
$A \in \mathbb{R}^{n \times n}$ be an M-matrix and let $p$ be an index. Then the matrix obtained
from $A$ by one step of Gaussian elimination with pivot $p$, $$a_{ij} - a_{ip} a_{pp}^{-1}
a_{pj} \qquad (i, j \neq p),$$ is again an M-matrix.

The proof makes the three checks of the source. Off the diagonal, $a_{ij} - a_{ip} a_{pj} /
a_{pp} \le a_{ij} \le 0$, because the subtracted term is a product of two nonpositive entries
divided by a positive pivot. Nonsingularity and the nonnegativity of the inverse come from one
identity, `Matrix.inv_schurComplementSingle`: the inverse of the Schur complement is the
submatrix of $A^{-1}$ on the indices other than the pivot. This is the content of the identity
$A_1^{-1} e_j = A^{-1} e_j$ of [saad2003iterative]. The eliminated matrix is
`Matrix.schurComplementSingle A p`, indexed by the subtype of indices $i \neq p$. -/
theorem IsMMatrix.schurComplementSingle {A : Matrix n n ℝ} (hA : A.IsMMatrix) (p : n) :
    (A.schurComplementSingle p).IsMMatrix := by
  have hpp : 0 < A p p := hA.diag_pos p
  refine ⟨fun i j hij => ?_, isUnit_schurComplementSingle hA.isUnit hpp.ne', ?_⟩
  · rw [Matrix.schurComplementSingle_apply]
    have h1 : A i.1 j.1 ≤ 0 := hA.offDiag_nonpos _ _ (Subtype.coe_injective.ne hij)
    have h3 : A p j.1 ≤ 0 := hA.offDiag_nonpos _ _ (Ne.symm j.2)
    have h5 : A i.1 p * (A p p)⁻¹ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (hA.offDiag_nonpos _ _ i.2) (inv_pos.2 hpp).le
    nlinarith [h5, h3]
  · rw [inv_schurComplementSingle hA.isUnit hpp.ne']
    exact entrywiseNonneg_iff.2 fun i j => hA.inv_entrywiseNonneg.apply i.1 j.1

end KyFan

/-! ### Stieltjes matrices -/

section Stieltjes

/-- **A symmetric M-matrix is positive definite.** Let $A \in \mathbb{R}^{n \times n}$ be a
symmetric M-matrix. Then $A$ is positive definite.

Take $w > 0$ with $Aw > 0$ (`Matrix.isMMatrix_iff_exists_pos_mulVec_pos`) and
$W = \operatorname{diag}(w)$. The congruent matrix $WAW$ is symmetric with nonpositive
off-diagonal entries and positive row sums $w_i (Aw)_i$. So it is strictly diagonally dominant
with a positive diagonal, and hence positive definite (`Matrix.IsStrictDiagDominant.posDef`).
Positive definiteness passes back along the congruence. This is the converse of
`Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos` for symmetric matrices. -/
theorem IsMMatrix.posDef_of_isSymm {A : Matrix n n ℝ} (hA : A.IsMMatrix) (hs : A.IsSymm) :
    A.PosDef := by
  obtain ⟨w, hw, hAw⟩ := (isMMatrix_iff_exists_pos_mulVec_pos hA.offDiag_nonpos).1 hA
  have hWu : IsUnit (diagonal w) := (isUnit_iff_isUnit_det _).2 (by
    rw [det_diagonal]
    exact isUnit_iff_ne_zero.2 (prod_ne_zero_iff.2 fun i _ => (hw i).ne'))
  have hB : ∀ i j, (star (diagonal w) * A * diagonal w) i j = w i * A i j * w j := fun i j => by
    rw [star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
    simp
  rw [← Matrix.IsUnit.posDef_star_left_conjugate_iff hWu]
  refine IsStrictDiagDominant.posDef ?_ (fun i => ?_) (fun i => ?_)
  · rw [star_eq_conjTranspose]
    exact isHermitian_conjTranspose_mul_mul _ (isHermitian_iff_isSymm.2 hs)
  · have hrow : (A *ᵥ w) i = A i i * w i + ∑ j ∈ univ.erase i, A i j * w j := by
      rw [mulVec_apply_eq_sum, ← add_sum_erase _ _ (mem_univ i)]
    have hoff : ∀ j ∈ univ.erase i, ‖(star (diagonal w) * A * diagonal w) i j‖
        = -(w i * (A i j * w j)) := fun j hj => by
      rw [hB, Real.norm_eq_abs, abs_of_nonpos, mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (hw i).le
        (hA.offDiag_nonpos i j (mem_erase.1 hj).1.symm)) (hw j).le
    rw [sum_congr rfl hoff, sum_neg_distrib, ← mul_sum, hB, Real.norm_eq_abs,
      abs_of_pos (mul_pos (mul_pos (hw i) (hA.diag_pos i)) (hw i))]
    have key : w i * A i i * w i + w i * ∑ j ∈ univ.erase i, A i j * w j = w i * (A *ᵥ w) i := by
      rw [hrow]; ring
    linarith [mul_pos (hw i) (hAw i)]
  · rw [hB, RCLike.re_to_real]
    exact mul_pos (mul_pos (hw i) (hA.diag_pos i)) (hw i)

/-- A **Stieltjes matrix** ([golub2013matrix], §11.5.8) is a real positive definite matrix
$A \in \mathbb{R}^{n \times n}$ with nonpositive off-diagonal entries. The term is also used in
§3.5 of Varga's *Matrix Iterative Analysis*.

Here positive definite is `Matrix.PosDef`, which includes symmetry. By
`Matrix.isStieltjes_iff_isMMatrix_isSymm`, the Stieltjes matrices are exactly the symmetric
M-matrices. -/
structure IsStieltjes (A : Matrix n n ℝ) : Prop where
  /-- The matrix is positive definite, and in particular symmetric. -/
  posDef : A.PosDef
  /-- The off-diagonal entries are nonpositive: $a_{ij} \le 0$ for $i \neq j$. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0

namespace IsStieltjes

variable {A : Matrix n n ℝ} (hA : A.IsStieltjes)
include hA

/-- A Stieltjes matrix is an M-matrix (`Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos`). -/
theorem isMMatrix : A.IsMMatrix := IsMMatrix.of_posDef_of_offDiag_nonpos hA.posDef hA.offDiag_nonpos

/-- The inverse of a Stieltjes matrix is entrywise nonnegative. This is Lemma 11.5.1 of
[golub2013matrix]. -/
theorem inv_entrywiseNonneg : A⁻¹.EntrywiseNonneg := hA.isMMatrix.inv_entrywiseNonneg

omit [Fintype n] [DecidableEq n] in
/-- A Stieltjes matrix is symmetric. -/
theorem isSymm : A.IsSymm := isHermitian_iff_isSymm.1 hA.posDef.isHermitian

end IsStieltjes

/-- **The Stieltjes matrices are the symmetric M-matrices.** A matrix
$A \in \mathbb{R}^{n \times n}$ is a Stieltjes matrix if and only if it is an M-matrix and
symmetric.

The forward half is `Matrix.IsStieltjes.isMMatrix`, and the backward half is
`Matrix.IsMMatrix.posDef_of_isSymm`. -/
theorem isStieltjes_iff_isMMatrix_isSymm {A : Matrix n n ℝ} :
    A.IsStieltjes ↔ A.IsMMatrix ∧ A.IsSymm :=
  ⟨fun h => ⟨h.isMMatrix, h.isSymm⟩, fun h => ⟨h.1.posDef_of_isSymm h.2, h.1.offDiag_nonpos⟩⟩

omit [Fintype n] [DecidableEq n] in
/-- **An increase of off-diagonal entries keeps a matrix Stieltjes.** Let
$A, B \in \mathbb{R}^{n \times n}$, let $A$ be a Stieltjes matrix, let $a_{ij} \le b_{ij}$ for
all $i, j$, and let $B$ be symmetric with nonpositive off-diagonal entries. Then $B$ is a
Stieltjes matrix.

The proof uses `Matrix.IsMMatrix.of_entrywiseLE`. In particular, to set a symmetric set of
off-diagonal entries to zero, as in the dropping step of incomplete Cholesky factorization,
gives a Stieltjes matrix. -/
theorem IsStieltjes.of_entrywiseLE [Finite n] {A B : Matrix n n ℝ} (hA : A.IsStieltjes)
    (hAB : A ≤ₑ B) (hB : B.IsSymm) (hoff : B.IsZMatrix) : B.IsStieltjes := by
  classical
  have := Fintype.ofFinite n
  exact isStieltjes_iff_isMMatrix_isSymm.2 ⟨hA.isMMatrix.of_entrywiseLE hAB hoff, hB⟩

omit [Fintype n] [DecidableEq n] in
/-- Let $A \in \mathbb{R}^{n \times n}$ be a Stieltjes matrix and let $e$ be an injective map of
indices. Then the principal submatrix $(a_{e(i) e(j)})_{i,j}$ is a Stieltjes matrix. -/
theorem IsStieltjes.submatrix {m : Type*} {A : Matrix n n ℝ}
    (hA : A.IsStieltjes) {e : m → n} (he : Function.Injective e) :
    (A.submatrix e e).IsStieltjes :=
  ⟨hA.posDef.submatrix he, fun _ _ hij => hA.offDiag_nonpos _ _ (he.ne hij)⟩

omit [Fintype n] [DecidableEq n] in
/-- **One step of symmetric Gaussian elimination keeps a matrix Stieltjes.** Let
$A \in \mathbb{R}^{n \times n}$ be a Stieltjes matrix and let $p$ be an index. Then the Schur
complement `Matrix.schurComplementSingle A p` of the pivot $p$ is a Stieltjes matrix.

The Schur complement is an M-matrix by the theorem of Ky Fan
(`Matrix.IsMMatrix.schurComplementSingle`), and it is symmetric. -/
theorem IsStieltjes.schurComplementSingle [Finite n] {A : Matrix n n ℝ} (hA : A.IsStieltjes)
    (p : n) : (A.schurComplementSingle p).IsStieltjes := by
  classical
  have := Fintype.ofFinite n
  exact isStieltjes_iff_isMMatrix_isSymm.2 ⟨hA.isMMatrix.schurComplementSingle p, by
    rw [IsSymm, schurComplementSingle_transpose, hA.isSymm.eq]⟩

omit [Fintype n] [DecidableEq n] in
/-- **Elimination with a dropped pivot column keeps a matrix Stieltjes** ([golub2013matrix], Theorem
11.5.2). Let $A \in \mathbb{R}^{n \times n}$ be a Stieltjes matrix, let $p$ be an index, and let
$S$ be a set of indices other than $p$. Let $\tilde u_i = a_{ip}$ for $i \in S$ and
$\tilde u_i = 0$ otherwise, and let $\tilde v_j = a_{pj}$ for $j \in S$ and $\tilde v_j = 0$
otherwise. Then the matrix $$\left(a_{ij} - \tilde u_i \tilde v_j / a_{pp}\right)_{i, j \neq
p}$$ is a Stieltjes matrix.

This matrix lies entrywise above the Schur complement, because the products $a_{ip} a_{pj}$ that
it omits are nonnegative, so `Matrix.IsStieltjes.of_entrywiseLE` applies. -/
theorem IsStieltjes.sub_drop [Finite n] {A : Matrix n n ℝ} (hA : A.IsStieltjes)
    (p : n) (S : Set {i : n // i ≠ p}) [DecidablePred (· ∈ S)] :
    (Matrix.of fun i j : {i : n // i ≠ p} =>
        A i j - (if i ∈ S then A i p else 0) * (if j ∈ S then A p j else 0) / A p p
      ).IsStieltjes := by
  classical
  have := Fintype.ofFinite n
  have hpp : 0 < A p p := hA.isMMatrix.diag_pos p
  have hsym : ∀ i j, A i j = A j i := fun i j => hA.isSymm.apply j i
  have hprod : ∀ i j : {i : n // i ≠ p}, 0 ≤ A i p * A p j := fun i j =>
    mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos _ _ i.2) (hA.offDiag_nonpos _ _ (Ne.symm j.2))
  have hdrop : ∀ i j : {i : n // i ≠ p},
      0 ≤ (if i ∈ S then A i p else 0) * (if j ∈ S then A p j else 0) / A p p := fun i j => by
    refine div_nonneg ?_ hpp.le
    split_ifs <;> simp [hprod i j]
  refine (hA.schurComplementSingle p).of_entrywiseLE (fun i j => ?_) ?_ (fun i j hij => ?_)
  · rw [schurComplementSingle_apply, of_apply]
    have : A i p * (A p p)⁻¹ * A p j = A i p * A p j / A p p := by ring
    rw [this]
    refine sub_le_sub_left (div_le_div_of_nonneg_right ?_ hpp.le) _
    split_ifs <;> simp [hprod i j]
  · ext i j
    simp only [transpose_apply, of_apply, hsym (i : n) j, hsym (j : n) p, hsym p (i : n)]
    congr 2
    split_ifs <;> ring
  · rw [of_apply]
    linarith [hA.offDiag_nonpos _ _ (Subtype.coe_injective.ne hij), hdrop i j]

end Stieltjes

end Matrix
