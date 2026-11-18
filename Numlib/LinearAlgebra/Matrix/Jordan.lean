/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Jordan`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.AdjoinRoot
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.Similar

/-!
# The Jordan canonical form

A **Jordan block** $J_n(\mu)$ is the $n \times n$ upper bidiagonal matrix with the scalar $\mu$ on
the diagonal and $1$ on the superdiagonal. A **Jordan form** is a block diagonal matrix whose
diagonal blocks are Jordan blocks $J_{e_i}(\mu_i)$, for a finite family of sizes $e_i$ and
eigenvalues $\mu_i$. Over an algebraically closed field, every endomorphism of a finite-dimensional
vector space has a Jordan form as its matrix in a suitable basis, and hence every square matrix is
similar to a Jordan form. This is the Jordan canonical form of [saad2003iterative], §1.8.2, Theorem
1.8. The Jordan form is unique up to the order of the blocks.

The file also computes the multiplicities of an eigenvalue $c$ of a Jordan form $J$ from its
characteristic polynomial and from the dimensions of the null spaces of the powers $(J - cI)^k$. The
**algebraic multiplicity** of $c$, its multiplicity as a root of the characteristic polynomial, is
the total size of the blocks with eigenvalue $c$. The **geometric multiplicity**, the dimension of
the eigenspace, is the number of these blocks, since each block contributes one eigenvector. The
**index** of $c$, the least $k$ at which the null spaces of $(J - cI)^k$ stop growing, is the
largest size of these blocks.

## Main definitions

* `Matrix.jordanBlock`: the Jordan block $J_n(\mu)$.
* `Matrix.jordanForm`: the block diagonal matrix with the blocks $J_{e_i}(\mu_i)$, indexed by the
  pairs $(i, a)$ with $a < e_i$.

## Main results

* `Module.End.exists_basis_toMatrix_eq_jordanForm_of_isNilpotent`: a nilpotent endomorphism has a
  Jordan form with all eigenvalues $0$ as its matrix in some basis, over any field.
* `Module.End.exists_basis_toMatrix_eq_jordanForm_of_isNilpotent_sub`: the same with eigenvalue
  $\mu$ for an endomorphism $f$ such that $f - \mu$ is nilpotent.
* `Module.End.exists_basis_toMatrix_eq_blockDiagonal'_jordanForm`: the Jordan canonical form over an
  algebraically closed field, grouped by eigenvalue: one outer block for each distinct eigenvalue
  $\nu_i$, which is itself a Jordan form whose blocks all have eigenvalue $\nu_i$.
* `Module.End.exists_basis_toMatrix_eq_jordanForm`: the same with the two levels of blocks flattened
  into one Jordan form.
* `Matrix.exists_conj_jordanForm`: every square matrix $A$ over an algebraically closed field has an
  invertible $P$ such that $P^{-1} A P$ is a Jordan form.
* `Matrix.exists_conj_blockDiagonal'_jordanForm`: the same, grouped by eigenvalue, which is the form
  of [saad2003iterative], Theorem 1.8.
* `Matrix.splits_minpoly_jordanBlock`: the minimal polynomial of a Jordan block splits.
* `Matrix.charpoly_jordanForm`: the characteristic polynomial of a Jordan form is
  $\prod_i (X - \mu_i)^{e_i}$.
* `Matrix.rootMultiplicity_charpoly_jordanForm`: the algebraic multiplicity of $c$ is the sum of the
  $e_i$ with $\mu_i = c$.
* `Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow`: $\dim \ker (J - cI)^k = \sum_{\mu_i =
  c} \min(e_i, k)$.
* `Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one`: the geometric multiplicity of $c$ is the
  number of blocks with eigenvalue $c$, if all blocks have positive size.
* `Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff`: the null spaces of
  $(J - cI)^k$ stop growing at $k$ if and only if every block with eigenvalue $c$ has size at most
  $k$.
* `Matrix.card_filter_le_jordanBlocks_eq`: the number of blocks of size at least $k + 1$ with
  eigenvalue $c$ is $\dim \ker (J - cI)^{k+1} - \dim \ker (J - cI)^k$.
* `Matrix.card_jordanBlocks_eq_of_isSimilar`: uniqueness, the number of Jordan blocks of each size
  for each eigenvalue is a similarity invariant ([golub2013matrix], the remark after Theorem 7.1.9,
  and §7.6.5).
* `Matrix.exists_equiv_submatrix_jordanForm_pos`: the blocks of size zero of a Jordan form can be
  removed.
* `Matrix.mulVec_eq_of_conj_jordanForm`: the columns of the transforming matrix are eigenvectors and
  principal vectors, $A x_{i,0} = \mu_i x_{i,0}$ and $A x_{i,j+1} = \mu_i x_{i,j+1} + x_{i,j}$
  ([quarteroni2000numerical], (1.8)).
* `Matrix.finrank_eigenspace_le_rootMultiplicity_charpoly`: the geometric multiplicity of an
  eigenvalue is at most its algebraic multiplicity.

## Proof outline

Two structure theorems of Mathlib are combined. First, over an algebraically closed field, $V$ is
the direct sum of the maximal generalized eigenspaces of $f$, and $f - \mu$ is nilpotent on the
generalized eigenspace of $\mu$. Second, for a nilpotent endomorphism $g$, the space $V$ is a
finitely generated torsion module over the principal ideal domain $K[X]$, with $X$ acting as $g$. By
the structure theorem it is a direct sum of cyclic modules $K[X]/(X^k)$. In the basis of
$K[X]/(X^k)$ given by the images of $X^{k-1}, \dots, X, 1$, multiplication by $X$ is the nilpotent
Jordan block $J_k(0)$.

The multiplicities are computed block by block: the characteristic polynomial and the nullity of a
block diagonal matrix are the product and the sum over the blocks. A Jordan block with a nonzero
eigenvalue is invertible. The $k$-th power of the nilpotent block $J_n(0)$ has ones on the $k$-th
superdiagonal, so its null space consists of the vectors whose coordinates from the $k$-th on
vanish, and it has dimension $\min(n, k)$.

## Implementation notes

* The endomorphism statements give a `Basis` and describe `LinearMap.toMatrix` in it. This shape is
  used instead of a bundled structure or an abstract direct sum decomposition, because the basis is
  the change of coordinates, and an equation between matrices can be transported, multiplied and
  specialized with the ordinary `Matrix` API.
* The basis is indexed by `(i : ι) × Fin (e i)` instead of `Fin n`. With this index type
  `Matrix.blockDiagonal'` applies, and the block sizes can be read off the index type.
* A `Matrix.jordanForm` can have blocks of size zero. These contribute nothing to the matrix, but
  they change the counts of blocks. The existence theorems produce blocks of positive size, and
  `Matrix.exists_equiv_submatrix_jordanForm_pos` removes the blocks of size zero from any Jordan
  form.
* The eigenvalue split uses `Module.End.iSup_maxGenEigenspace_eq_top`,
  `Module.End.independent_maxGenEigenspace` and
  `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`. The cyclic decomposition uses
  `Module.torsion_by_prime_power_decomposition` for the module `Module.AEval' g`, and the basis of
  $K[X]/(X^k)$ comes from `AdjoinRoot.powerBasis'` and `basisOfTopLeSpanOfCardEqFinrank`. Neither
  theorem is proved again here.
* The block diagonal results that the multiplicity statements use are in
  `Numlib.LinearAlgebra.Matrix.BlockDiagonal` and `Numlib.LinearAlgebra.Matrix.Rank`.
* The eigenvalue split is done first, so that the grouped statement comes first; the flat statement
  is a reindexing of it. The opposite order, `Module.equiv_directSum_of_isTorsion` applied to
  `Module.AEval' f` directly, gives the flat statement in one step, but then the grouping must be
  recovered by sorting the blocks by eigenvalue, which is harder.
-/

open Polynomial Module
open scoped DirectSum

namespace Matrix

variable {R : Type*} {n : ℕ}

section Zero

variable [Zero R] [One R] {μ : R}

/-- The **Jordan block** $J_n(\mu)$ of size $n$ for the scalar $\mu$: the $n \times n$ matrix with
$\mu$ on the diagonal, $1$ on the superdiagonal and $0$ elsewhere,
$$(J_n(\mu))_{ij} = \begin{cases} \mu & i = j, \\ 1 & i + 1 = j, \\ 0 & \text{otherwise.}
  \end{cases}$$

The indices run from $0$ to $n - 1$. -/
def jordanBlock (n : ℕ) (μ : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = j then μ else if (i : ℕ) + 1 = (j : ℕ) then 1 else 0

/-- The entries of a Jordan block: $(J_n(\mu))_{ij}$ is $\mu$ if $i = j$, $1$ if $i + 1 = j$, and
$0$ otherwise.

This is the definition of `Matrix.jordanBlock` unfolded. -/
theorem jordanBlock_apply (i j : Fin n) :
    jordanBlock n μ i j = if i = j then μ else if (i : ℕ) + 1 = (j : ℕ) then 1 else 0 := rfl

/-- A diagonal entry of $J_n(\mu)$ is $\mu$. -/
@[simp] theorem jordanBlock_apply_self (i : Fin n) : jordanBlock n μ i i = μ := by
  simp [jordanBlock_apply]

/-- If $i + 1 = j$, then $(J_n(\mu))_{ij} = 1$. -/
theorem jordanBlock_apply_succ {i j : Fin n} (h : (i : ℕ) + 1 = (j : ℕ)) :
    jordanBlock n μ i j = 1 := by
  have hne : i ≠ j := by rintro rfl; omega
  simp [jordanBlock_apply, hne, h]

/-- If $i \ne j$ and $i + 1 \ne j$, then $(J_n(\mu))_{ij} = 0$. -/
theorem jordanBlock_apply_of_ne {i j : Fin n} (h₁ : i ≠ j) (h₂ : (i : ℕ) + 1 ≠ (j : ℕ)) :
    jordanBlock n μ i j = 0 := by
  simp [jordanBlock_apply, h₁, h₂]

/-- The diagonal of $J_n(\mu)$ is the constant vector $\mu$. -/
@[simp] theorem diag_jordanBlock : (jordanBlock n μ).diag = fun _ => μ := by
  funext i
  simp

/-- The entries of the nilpotent Jordan block: $(J_n(0))_{ij}$ is $1$ if $i + 1 = j$, and $0$
otherwise. -/
theorem jordanBlock_zero_apply (i j : Fin n) :
    jordanBlock n (0 : R) i j = if (i : ℕ) + 1 = (j : ℕ) then 1 else 0 := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [jordanBlock_apply, h]

/-- The Jordan block $J_n(\mu)$ is upper triangular. -/
theorem isUpperTriangular_jordanBlock : (jordanBlock n μ).IsUpperTriangular := by
  intro i j hji
  rw [id_eq, id_eq, Fin.lt_def] at hji
  exact jordanBlock_apply_of_ne (fun h => by subst h; omega) (by omega)

end Zero

section CommRing

variable [CommRing R] {μ : R}

/-- Over a commutative ring, the characteristic polynomial of $J_n(\mu)$ is $(X - \mu)^n$. -/
theorem charpoly_jordanBlock : (jordanBlock n μ).charpoly = (X - C μ) ^ n := by
  rw [charpoly_of_isUpperTriangular _ isUpperTriangular_jordanBlock]
  simp

/-- Over a commutative ring, a Jordan block is its nilpotent part plus a multiple of the identity:
$$J_n(\mu) = J_n(0) + \mu I.$$
-/
theorem jordanBlock_eq_add_smul_one : jordanBlock n μ = jordanBlock n 0 + μ • 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [jordanBlock_apply, h, Matrix.one_apply_ne h]

/-- Over a commutative ring, shifting a Jordan block by a scalar shifts its eigenvalue: for every
scalar $c$,
$$J_n(\mu) - cI = J_n(\mu - c).$$
-/
theorem jordanBlock_sub_smul_one (c : R) :
    jordanBlock n μ - c • (1 : Matrix (Fin n) (Fin n) R) = jordanBlock n (μ - c) := by
  rw [jordanBlock_eq_add_smul_one (μ := μ), jordanBlock_eq_add_smul_one (μ := μ - c), sub_smul]
  abel

/-- Over a commutative ring, the $k$-th power of the nilpotent Jordan block has ones on the $k$-th
superdiagonal and zeros elsewhere:
$$(J_n(0)^k)_{ij} = \begin{cases} 1 & i + k = j, \\ 0 & \text{otherwise.} \end{cases}$$
-/
theorem jordanBlock_zero_pow_apply (k : ℕ) (i j : Fin n) :
    ((jordanBlock n (0 : R)) ^ k) i j = if (i : ℕ) + k = (j : ℕ) then 1 else 0 := by
  induction k generalizing j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      by_cases h : (i : ℕ) + k < n
      · rw [Finset.sum_eq_single (⟨(i : ℕ) + k, h⟩ : Fin n) ?_ (by simp)]
        · rw [ih, jordanBlock_zero_apply]
          simp [Nat.add_assoc]
        · intro l _ hl
          have hne : (i : ℕ) + k ≠ (l : ℕ) := fun hc => hl (Fin.ext hc.symm)
          simp [ih, hne]
      · have hj := j.isLt
        have hne : (i : ℕ) + (k + 1) ≠ (j : ℕ) := by omega
        refine (Finset.sum_eq_zero fun l _ => ?_).trans (by simp [hne])
        have hl := l.isLt
        have hil : (i : ℕ) + k ≠ (l : ℕ) := by omega
        simp [ih, hil]

/-- Over a commutative ring, the $k$-th power of the nilpotent Jordan block shifts a vector by $k$
places: if $i + k = j$, then $(J_n(0)^k v)_i = v_j$ for every vector $v$. -/
theorem jordanBlock_zero_pow_mulVec_apply (k : ℕ) (v : Fin n → R) (i j : Fin n)
    (hij : (i : ℕ) + k = (j : ℕ)) : ((jordanBlock n (0 : R) ^ k) *ᵥ v) i = v j := by
  simp only [mulVec, dotProduct, jordanBlock_zero_pow_apply]
  rw [Finset.sum_eq_single j]
  · simp [hij]
  · intro b _ hb
    have hne : (i : ℕ) + k ≠ (b : ℕ) := fun hc => hb (Fin.ext (by omega))
    simp [hne]
  · simp

/-- Over a commutative ring, if $n \le i + k$, then $(J_n(0)^k v)_i = 0$ for every vector $v$. -/
theorem jordanBlock_zero_pow_mulVec_of_le (k : ℕ) (v : Fin n → R) (i : Fin n)
    (hi : n ≤ (i : ℕ) + k) : ((jordanBlock n (0 : R) ^ k) *ᵥ v) i = 0 := by
  simp only [mulVec, dotProduct, jordanBlock_zero_pow_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have := b.isLt
  simp [show (i : ℕ) + k ≠ (b : ℕ) by omega]

end CommRing

section Minpoly

variable {K : Type*} [Field K] {μ : K}

/-- Over a field, the minimal polynomial of a Jordan block splits.

It divides the characteristic polynomial $(X - \mu)^n$ (`Matrix.charpoly_jordanBlock`). -/
theorem splits_minpoly_jordanBlock : (minpoly K (jordanBlock n μ)).Splits :=
  ((Splits.X_sub_C μ).pow n).of_dvd (pow_ne_zero n (X_sub_C_ne_zero μ)) <| by
    rw [← charpoly_jordanBlock]
    exact minpoly_dvd_charpoly _

end Minpoly

section JordanBlockKer

variable {K : Type*} [Field K] {ν : K}

/-- Over a field $K$, a vector $v \in K^n$ lies in the null space of $J_n(0)^k$ if and only if
$v_j = 0$ for every $j \ge k$. -/
theorem mem_ker_mulVecLin_jordanBlock_zero_pow {k : ℕ} {v : Fin n → K} :
    v ∈ LinearMap.ker ((jordanBlock n (0 : K) ^ k).mulVecLin)
      ↔ ∀ j : Fin n, k ≤ (j : ℕ) → v j = 0 := by
  simp only [LinearMap.mem_ker, mulVecLin_apply, funext_iff, Pi.zero_apply]
  constructor
  · intro h j hj
    have hlt : (j : ℕ) - k < n := by omega
    rw [← jordanBlock_zero_pow_mulVec_apply k v ⟨(j : ℕ) - k, hlt⟩ j (Nat.sub_add_cancel hj)]
    exact h _
  · intro h i
    rcases lt_or_ge ((i : ℕ) + k) n with hi | hi
    · rw [jordanBlock_zero_pow_mulVec_apply k v i ⟨(i : ℕ) + k, hi⟩ rfl]
      exact h _ (Nat.le_add_left k i)
    · exact jordanBlock_zero_pow_mulVec_of_le k v i hi

/-- **The nullity of a power of a nilpotent Jordan block.** Over a field $K$, for every
$k \in \mathbb{N}$,
$$\dim \ker J_n(0)^k = \min(n, k).$$

At $k = 1$ this says that the block has exactly one eigenvector, up to scaling, when $n \ge 1$. -/
theorem finrank_ker_mulVecLin_jordanBlock_zero_pow (k : ℕ) :
    Module.finrank K (LinearMap.ker ((jordanBlock n (0 : K) ^ k).mulVecLin)) = min n k := by
  classical
  have hcard : Fintype.card {j : Fin n // (j : ℕ) < k} = min n k := by
    rcases le_total k n with hk | hk
    · rw [Fintype.card_fin_lt_of_le hk, min_eq_right hk]
    · rw [Fintype.card_congr (Equiv.subtypeUnivEquiv fun j : Fin n => lt_of_lt_of_le j.isLt hk),
        Fintype.card_fin, min_eq_left hk]
  have hcompl : Fintype.card {j : Fin n // k ≤ (j : ℕ)} = n - min n k := by
    have h := Fintype.card_subtype_compl (p := fun j : Fin n => (j : ℕ) < k)
    rw [hcard, Fintype.card_fin] at h
    rw [← h]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun j => (not_lt).symm)
  have hker : LinearMap.ker ((jordanBlock n (0 : K) ^ k).mulVecLin)
      = LinearMap.ker
          (LinearMap.funLeft K K (Subtype.val : {j : Fin n // k ≤ (j : ℕ)} → Fin n)) := by
    ext v
    rw [mem_ker_mulVecLin_jordanBlock_zero_pow, LinearMap.mem_ker, funext_iff]
    exact ⟨fun h j => h j.1 j.2, fun h j hj => h ⟨j, hj⟩⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft K K (Subtype.val : {j : Fin n // k ≤ (j : ℕ)} → Fin n))
  rw [LinearMap.range_eq_top.2
      (LinearMap.funLeft_surjective_of_injective K K _ Subtype.val_injective),
    finrank_top, Module.finrank_pi, Module.finrank_pi, hcompl, Fintype.card_fin] at hrn
  rw [hker]
  omega

/-- Over a field, let $\nu \ne 0$. Then the null space of $J_n(\nu)^k$ is $\{0\}$ for every
$k \in \mathbb{N}$.

A Jordan block with a nonzero eigenvalue is invertible. -/
theorem ker_mulVecLin_jordanBlock_pow_eq_bot (hν : ν ≠ 0) (k : ℕ) :
    LinearMap.ker ((jordanBlock n ν ^ k).mulVecLin) = ⊥ := by
  refine Matrix.ker_mulVecLin_eq_bot_iff.2 ?_
  have hdet : (jordanBlock n ν).det = ν ^ n := by
    rw [det_of_isUpperTriangular isUpperTriangular_jordanBlock]
    simp
  have hunit : IsUnit (jordanBlock n ν ^ k) := by
    refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    rw [det_pow, hdet]
    exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ hν)).pow _
  intro v hv
  obtain ⟨B, hB⟩ := hunit.exists_left_inv
  have h : (B * jordanBlock n ν ^ k) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rwa [hB, Matrix.one_mulVec] at h

/-- **The nullity of a power of a Jordan block.** Over a field $K$, for every $\nu \in K$ and
$k \in \mathbb{N}$,
$$\dim \ker J_n(\nu)^k = \begin{cases} \min(n, k) & \nu = 0, \\ 0 & \nu \ne 0. \end{cases}$$
-/
theorem finrank_ker_mulVecLin_jordanBlock_pow [DecidableEq K] (ν : K) (k : ℕ) :
    Module.finrank K (LinearMap.ker ((jordanBlock n ν ^ k).mulVecLin))
      = if ν = 0 then min n k else 0 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp [finrank_ker_mulVecLin_jordanBlock_zero_pow]
  · simp [hν, ker_mulVecLin_jordanBlock_pow_eq_bot hν]

end JordanBlockKer

section BlockDiagonal

variable {α ι ι' : Type*} [Zero α] [DecidableEq ι] [DecidableEq ι']

/-- Reindexing a block diagonal matrix by a bijection $\sigma : \iota' \to \iota$ of the block
indices gives the block diagonal matrix of the reindexed blocks: if $D$ has the diagonal blocks
$M_i$, then $D$ reindexed along $\sigma$ on both sides is the block diagonal matrix with the
blocks $M_{\sigma(i')}$. -/
theorem blockDiagonal'_submatrix_sigmaCongrLeft {m : ι → Type*}
    (M : ∀ i, Matrix (m i) (m i) α) (σ : ι' ≃ ι) :
    (blockDiagonal' M).submatrix (Equiv.sigmaCongrLeft σ) (Equiv.sigmaCongrLeft σ)
      = blockDiagonal' fun i => M (σ i) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  rcases eq_or_ne a b with rfl | hab
  · rw [submatrix_apply, blockDiagonal'_apply_eq]
    exact blockDiagonal'_apply_eq _ _ _ _
  · rw [submatrix_apply, blockDiagonal'_apply_ne _ _ _ hab]
    exact blockDiagonal'_apply_ne _ _ _ (σ.injective.ne hab)

/-- A block diagonal matrix whose diagonal blocks are block diagonal matrices, with blocks $M_{ij}$,
is equal, after the reassociation of the index $(i, (j, a)) \mapsto ((i, j), a)$, to the single
block diagonal matrix with the blocks $M_{ij}$ indexed by the pairs $(i, j)$. -/
theorem blockDiagonal'_blockDiagonal' {κ : ι → Type*} [∀ i, DecidableEq (κ i)]
    {m : (i : ι) → κ i → Type*} (M : ∀ (i : ι) (j : κ i), Matrix (m i j) (m i j) α) :
    (blockDiagonal' fun i => blockDiagonal' fun j => M i j)
      = (blockDiagonal' fun t : (i : ι) × κ i => M t.1 t.2).submatrix
          (Equiv.sigmaAssoc m).symm (Equiv.sigmaAssoc m).symm := by
  set F : ((i : ι) × κ i) → Type _ := fun t => m t.1 t.2
  set N : (t : (i : ι) × κ i) → Matrix (F t) (F t) α := fun t => M t.1 t.2
  ext ⟨i₁, j₁, x⟩ ⟨i₂, j₂, y⟩
  rcases eq_or_ne i₁ i₂ with rfl | hi
  · rcases eq_or_ne j₁ j₂ with rfl | hj
    · rw [blockDiagonal'_apply_eq, blockDiagonal'_apply_eq, submatrix_apply]
      exact (blockDiagonal'_apply_eq N ⟨i₁, j₁⟩ x y).symm
    · have hne : (⟨i₁, j₁⟩ : (i : ι) × κ i) ≠ ⟨i₁, j₂⟩ := fun h => hj (sigma_mk_injective h)
      rw [blockDiagonal'_apply_eq, blockDiagonal'_apply_ne _ _ _ hj, submatrix_apply]
      exact (blockDiagonal'_apply_ne N x y hne).symm
  · have hne : (⟨i₁, j₁⟩ : (i : ι) × κ i) ≠ ⟨i₂, j₂⟩ := fun h => hi (congrArg Sigma.fst h)
    rw [blockDiagonal'_apply_ne _ _ _ hi, submatrix_apply]
    exact (blockDiagonal'_apply_ne N x y hne).symm

end BlockDiagonal

section JordanForm

variable {ι : Type*} [DecidableEq ι]

/-- The **Jordan form** with block sizes $e_i$ and eigenvalues $\mu_i$, for $i$ in a type $\iota$:
the block diagonal matrix whose $i$-th diagonal block is the Jordan block $J_{e_i}(\mu_i)$.

The matrix is indexed by the pairs $(i, a)$ with $i \in \iota$ and $a < e_i$. -/
def jordanForm [Zero R] [One R] (e : ι → ℕ) (μ : ι → R) :
    Matrix ((i : ι) × Fin (e i)) ((i : ι) × Fin (e i)) R :=
  blockDiagonal' fun i => jordanBlock (e i) (μ i)

/-- The Jordan form with sizes $e_i$ and eigenvalues $\mu_i$ is the block diagonal matrix with the
blocks $J_{e_i}(\mu_i)$.

This is the definition of `Matrix.jordanForm` unfolded. -/
theorem jordanForm_def [Zero R] [One R] (e : ι → ℕ) (μ : ι → R) :
    jordanForm e μ = blockDiagonal' fun i => jordanBlock (e i) (μ i) := rfl

/-- Over a commutative ring, shifting a Jordan form by a scalar shifts every eigenvalue: if $J$ has
sizes $e_i$ and eigenvalues $\mu_i$, then $J - cI$ is the Jordan form with sizes $e_i$ and
eigenvalues $\mu_i - c$. -/
theorem jordanForm_sub_smul_one [CommRing R] (e : ι → ℕ) (μ : ι → R) (c : R) :
    jordanForm e μ - c • 1 = jordanForm e fun i => μ i - c := by
  rw [jordanForm_def, blockDiagonal'_sub_smul_one, jordanForm_def]
  exact congrArg blockDiagonal' (funext fun i => jordanBlock_sub_smul_one c)

/-- Over a commutative ring, a Jordan form whose blocks all have the eigenvalue $\mu$ is its
nilpotent part plus $\mu I$: if $J_\mu$ and $J_0$ are the Jordan forms with sizes $e_i$ and all
eigenvalues $\mu$ and $0$, then $J_\mu = J_0 + \mu I$. -/
theorem jordanForm_const_eq_add_smul_one [CommRing R] (e : ι → ℕ) (μ : R) :
    jordanForm e (fun _ => μ) = jordanForm e (fun _ => (0 : R)) + μ • 1 := by
  have h : jordanForm e (fun _ : ι => μ) - μ • 1 = jordanForm e fun _ : ι => (0 : R) := by
    rw [jordanForm_sub_smul_one]
    exact congrArg (jordanForm e) (funext fun _ => sub_self μ)
  rw [← h]
  abel

/-- **The blocks of size zero of a Jordan form can be removed.** Let $\iota$ be finite, and let $J$
be the Jordan form with sizes $e_i$ and eigenvalues $\mu_i$, $i \in \iota$. Then there are
$p \in \mathbb{N}$, a map $\varphi : \{0, \dots, p - 1\} \to \iota$ with $e_{\varphi(j)} > 0$
for all $j$, and a bijection $\rho$ of the index types such that $J$ reindexed along $\rho$ is
the Jordan form with sizes $e_{\varphi(j)}$ and eigenvalues $\mu_{\varphi(j)}$.

A `Matrix.jordanForm` can have blocks of size zero. They contribute nothing to the matrix, but
they change the counts of blocks in the multiplicity statements below, which have the intended
meaning only after these blocks are removed. -/
theorem exists_equiv_submatrix_jordanForm_pos [Finite ι] [Zero R] [One R] (e : ι → ℕ)
    (μ : ι → R) :
    ∃ (p : ℕ) (φ : Fin p → ι) (ρ : ((j : Fin p) × Fin (e (φ j))) ≃ ((i : ι) × Fin (e i))),
      (∀ j, 0 < e (φ j)) ∧
        (jordanForm e μ).submatrix ρ ρ = jordanForm (fun j => e (φ j)) fun j => μ (φ j) := by
  classical
  set S : Type _ := {i : ι // e i ≠ 0}
  have _ : Fintype S := Fintype.ofFinite S
  set τ : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  set ρ₂ : ((s : S) × Fin (e s.1)) ≃ ((i : ι) × Fin (e i)) :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, by have := x.2.isLt; omega⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsub : (jordanForm e μ).submatrix ρ₂ ρ₂
      = blockDiagonal' fun s : S => jordanBlock (e s.1) (μ s.1) := by
    ext ⟨a, x⟩ ⟨b, y⟩
    change blockDiagonal' (fun i => jordanBlock (e i) (μ i)) ⟨a.1, x⟩ ⟨b.1, y⟩
      = blockDiagonal' (fun s : S => jordanBlock (e s.1) (μ s.1)) ⟨a, x⟩ ⟨b, y⟩
    rcases eq_or_ne a b with rfl | hab
    · rw [blockDiagonal'_apply_eq, blockDiagonal'_apply_eq]
    · rw [blockDiagonal'_apply_ne _ _ _ (fun h => hab (Subtype.ext h)),
        blockDiagonal'_apply_ne _ _ _ hab]
  refine ⟨Fintype.card S, fun j => (τ j).1, (Equiv.sigmaCongrLeft τ).trans ρ₂,
    fun j => Nat.pos_of_ne_zero (τ j).2, ?_⟩
  rw [Equiv.coe_trans, ← submatrix_submatrix, hsub]
  exact blockDiagonal'_submatrix_sigmaCongrLeft (fun s : S => jordanBlock (e s.1) (μ s.1)) τ

variable [Fintype ι]

/-- **The characteristic polynomial of a Jordan form.** Over a commutative ring, let $\iota$ be
finite and let $J$ be the Jordan form with sizes $e_i$ and eigenvalues $\mu_i$. Then
$$\chi_J = \prod_{i \in \iota} (X - \mu_i)^{e_i}.$$
-/
theorem charpoly_jordanForm [CommRing R] (e : ι → ℕ) (μ : ι → R) :
    (jordanForm e μ).charpoly = ∏ i, (X - C (μ i)) ^ e i := by
  rw [jordanForm_def, charpoly_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ => charpoly_jordanBlock

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- **The algebraic multiplicity of an eigenvalue of a Jordan form.** Over a field $K$, let $\iota$
be finite and let $J$ be the Jordan form with sizes $e_i$ and eigenvalues $\mu_i$. Then for
every $c \in K$, the multiplicity of $c$ as a root of the characteristic polynomial of $J$ is
$$\sum_{i : \mu_i = c} e_i.$$
-/
theorem rootMultiplicity_charpoly_jordanForm (e : ι → ℕ) (μ : ι → K) (c : K) :
    (jordanForm e μ).charpoly.rootMultiplicity c
      = ∑ i ∈ Finset.univ.filter fun i => μ i = c, e i := by
  have hne : ∀ i : ι, ((X - C (μ i)) ^ e i : K[X]) ≠ 0 := fun i =>
    pow_ne_zero _ (X_sub_C_ne_zero _)
  rw [charpoly_jordanForm, ← count_roots,
    roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun i _ => hne i),
    show (Finset.univ.val.bind fun i => ((X - C (μ i)) ^ e i : K[X]).roots)
      = ∑ i, ((X - C (μ i)) ^ e i : K[X]).roots from rfl,
    Multiset.count_sum', Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [roots_pow, roots_X_sub_C, Multiset.count_nsmul, Multiset.count_singleton]
  rcases eq_or_ne (μ i) c with h | h
  · simp [h]
  · simp [h, Ne.symm h]

/-- **The nullity of a power of a shifted Jordan form.** Over a field $K$, let $\iota$ be finite and
let $J$ be the Jordan form with sizes $e_i$ and eigenvalues $\mu_i$. Then for every $c \in K$
and $k \in \mathbb{N}$,
$$\dim \ker (J - cI)^k = \sum_{i : \mu_i = c} \min(e_i, k).$$

At $k = 1$ this is the geometric multiplicity of $c$, each block with eigenvalue $c$
contributing one eigenvector. The growth in $k$ determines the index of $c$. -/
theorem finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow (e : ι → ℕ) (μ : ι → K) (c : K) (k : ℕ) :
    Module.finrank K (LinearMap.ker (((jordanForm e μ - c • 1) ^ k).mulVecLin))
      = ∑ i ∈ Finset.univ.filter fun i => μ i = c, min (e i) k := by
  rw [jordanForm_sub_smul_one, jordanForm_def, ← blockDiagonal'_pow,
    finrank_ker_mulVecLin_blockDiagonal', Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((fun i => jordanBlock (e i) (μ i - c)) ^ k) i = jordanBlock (e i) (μ i - c) ^ k from
    rfl, finrank_ker_mulVecLin_jordanBlock_pow]
  rcases eq_or_ne (μ i) c with h | h
  · simp [h]
  · simp [h, sub_eq_zero]

omit [DecidableEq K] in
/-- Over a field $K$, let $\iota$ be finite and let $J$ be the Jordan form with sizes $e_i$ and
eigenvalues $\mu_i$. Then for every $c \in K$ and $k \in \mathbb{N}$,
$$\dim \ker (J - cI)^{k+1} = \dim \ker (J - cI)^k \iff e_i \le k \text{ for every } i \text{
  with } \mu_i = c.$$

So the least $k$ at which the null spaces stop growing, the index of $c$, is the largest size of
a block with eigenvalue $c$. -/
theorem finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff (e : ι → ℕ) (μ : ι → K)
    (c : K) (k : ℕ) :
    Module.finrank K (LinearMap.ker (((jordanForm e μ - c • 1) ^ (k + 1)).mulVecLin))
        = Module.finrank K (LinearMap.ker (((jordanForm e μ - c • 1) ^ k).mulVecLin))
      ↔ ∀ i, μ i = c → e i ≤ k := by
  classical
  rw [finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow,
    finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow]
  have hle : ∀ i ∈ Finset.univ.filter fun i => μ i = c, min (e i) k ≤ min (e i) (k + 1) :=
    fun i _ => min_le_min_left _ (Nat.le_succ k)
  constructor
  · intro h i hi
    have h2 := (Finset.sum_eq_sum_iff_of_le hle).1 h.symm i (by simpa using hi)
    omega
  · exact fun h => Finset.sum_congr rfl fun i hi => by
      have := h i (by simpa using hi)
      omega

/-- **The geometric multiplicity of an eigenvalue of a Jordan form.** Over a field $K$, let $\iota$
be finite and let $J$ be the Jordan form with sizes $e_i > 0$ and eigenvalues $\mu_i$. Then for
every $c \in K$, the dimension of the null space of $J - cI$ is the number of blocks with
eigenvalue $c$:
$$\dim \ker (J - cI) = \#\{i \in \iota : \mu_i = c\}.$$
-/
theorem finrank_ker_mulVecLin_jordanForm_sub_smul_one {e : ι → ℕ} (he : ∀ i, 0 < e i) (μ : ι → K)
    (c : K) :
    Module.finrank K (LinearMap.ker ((jordanForm e μ - c • 1).mulVecLin))
      = (Finset.univ.filter fun i => μ i = c).card := by
  have h := finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow e μ c 1
  rw [pow_one] at h
  rw [h, Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun i _ => by have := he i; omega

end Field

end JordanForm

end Matrix

/-- Let $b$ be a basis of a module $M$ indexed by a finite type $\iota$, let
$\sigma : \iota \to \iota'$ be a bijection, and let $f$ be an endomorphism of $M$. The matrix of
$f$ in the basis $b$ reindexed by $\sigma$ is the matrix of $f$ in the basis $b$, reindexed by
$\sigma$: its entry $(i', j')$ is the entry $(\sigma^{-1}(i'), \sigma^{-1}(j'))$ of the matrix
of $f$ in $b$. -/
theorem LinearMap.toMatrix_reindex {R M ι ι' : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι R M) (σ : ι ≃ ι') (f : M →ₗ[R] M) :
    LinearMap.toMatrix (b.reindex σ) (b.reindex σ) f
      = (LinearMap.toMatrix b b f).submatrix σ.symm σ.symm := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
    Basis.reindex_apply, Basis.repr_reindex_apply]

namespace Polynomial

/-- Let $K$ be a field and $k \in \mathbb{N}$. The quotient $K[X]/(X^k)$ has a $K$-basis
$c_0, \dots, c_{k-1}$ in which multiplication by $X$ has the matrix $J_k(0)$:
$$X c_j = \sum_i (J_k(0))_{ij} \, c_i \quad \text{for all } j.$$

The basis consists of the images of $X^{k-1}, \dots, X, 1$. -/
theorem exists_basis_quotient_span_X_pow (K : Type*) [Field K] (k : ℕ) :
    ∃ c : Basis (Fin k) K (K[X] ⧸ (K[X] ∙ (X : K[X]) ^ k)),
      ∀ j, (X : K[X]) • c j = ∑ i, Matrix.jordanBlock k (0 : K) i j • c i := by
  classical
  set Q := K[X] ⧸ (K[X] ∙ (X : K[X]) ^ k)
  set y : Q := Submodule.Quotient.mk 1 with hydef
  have hy : ∀ p : K[X], p • y = (Submodule.Quotient.mk p : Q) := fun p => by
    rw [hydef, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  have hCsmul : ∀ (a : K) (z : Q), (C a : K[X]) • z = a • z := fun a z => by
    rw [← Polynomial.algebraMap_eq, algebraMap_smul]
  have hzero : ((X : K[X]) ^ k) • y = 0 := by
    rw [hy]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)
  set v : Fin k → Q := fun j => ((X : K[X]) ^ (k - 1 - (j : ℕ))) • y with hv
  have hrank : Module.finrank K Q = k := by
    have h := (AdjoinRoot.powerBasis' (R := K) (g := (X : K[X]) ^ k) (monic_X_pow k)).finrank
    rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow] at h
    exact h
  have hmem : ∀ m : ℕ, ((X : K[X]) ^ m) • y ∈ Submodule.span K (Set.range v) := by
    intro m
    rcases lt_or_ge m k with hm | hm
    · refine Submodule.subset_span ⟨⟨k - 1 - m, by omega⟩, ?_⟩
      simp only [hv]
      congr 2
      omega
    · have h : ((X : K[X]) ^ m) • y = ((X : K[X]) ^ (m - k)) • (((X : K[X]) ^ k) • y) := by
        rw [smul_smul, ← pow_add]
        congr 2
        omega
      rw [h, hzero, smul_zero]
      exact Submodule.zero_mem _
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro z _
    obtain ⟨p, rfl⟩ : ∃ p : K[X], p • y = z := by
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact ⟨p, hy p⟩
    have hexp : p • y
        = ∑ m ∈ Finset.range (p.natDegree + 1), p.coeff m • (((X : K[X]) ^ m) • y) := by
      conv_lhs => rw [p.as_sum_range]
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun m _ => by
        rw [← C_mul_X_pow_eq_monomial, mul_smul, hCsmul]
    rw [hexp]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hmem m)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank v hspan (by rw [Fintype.card_fin]; exact hrank.symm),
    fun j => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  have hstep : (X : K[X]) • v j = ((X : K[X]) ^ (k - (j : ℕ))) • y := by
    rw [hv]
    simp only
    rw [smul_smul, ← pow_succ']
    congr 2
    omega
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
  · rw [hstep, show k - (j : ℕ) = k by omega, hzero]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [Matrix.jordanBlock_zero_apply]
    simp [show (i : ℕ) + 1 ≠ (j : ℕ) by omega]
  · have hjk : (j : ℕ) - 1 < k := by omega
    have hval : ((X : K[X]) ^ (k - (j : ℕ))) • y = v ⟨(j : ℕ) - 1, hjk⟩ := by
      rw [hv]
      simp only
      congr 2
      omega
    have hone : Matrix.jordanBlock k (0 : K) (⟨(j : ℕ) - 1, hjk⟩ : Fin k) j = 1 := by
      rw [Matrix.jordanBlock_zero_apply]
      simp [Nat.sub_add_cancel hj]
    have hsum : ∑ i, Matrix.jordanBlock k (0 : K) i j • v i
        = Matrix.jordanBlock k (0 : K) (⟨(j : ℕ) - 1, hjk⟩ : Fin k) j • v ⟨(j : ℕ) - 1, hjk⟩ :=
      Finset.sum_eq_single _
        (fun i _ hi => by
          rw [Matrix.jordanBlock_zero_apply]
          have : (i : ℕ) + 1 ≠ (j : ℕ) := fun h =>
            hi (Fin.ext (show (i : ℕ) = (j : ℕ) - 1 by omega))
          simp [this])
        (fun h => absurd (Finset.mem_univ _) h)
    rw [hstep, hval, hsum, hone, one_smul]

end Polynomial

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If a $K$-linear equivalence carries $f$ to multiplication by $X$ on a finite product of
$K[X]$-modules, and each factor has a $K$-basis in which multiplication by $X$ has the matrix
$J_i$, then $f$ has the block diagonal matrix with the blocks $J_i$ in the transported basis. -/
private theorem exists_basis_toMatrix_eq_blockDiagonal' (f : End K V)
    {d : ℕ} {N : Fin d → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module K[X] (N i)]
    [∀ i, Module K (N i)]
    {e : Fin d → ℕ} (c : ∀ i, Basis (Fin (e i)) K (N i))
    (J : ∀ i, Matrix (Fin (e i)) (Fin (e i)) K)
    (E : V ≃ₗ[K] ∀ i, N i) (hE : ∀ v, E (f v) = (X : K[X]) • E v)
    (hc : ∀ i j, (X : K[X]) • (c i) j = ∑ a, J i a j • (c i) a) :
    ∃ b : Basis ((i : Fin d) × Fin (e i)) K V,
      LinearMap.toMatrix b b f = Matrix.blockDiagonal' J := by
  classical
  refine ⟨(Pi.basis c).map E.symm, ?_⟩
  ext ⟨i, a⟩ ⟨j, β⟩
  have hb : ((Pi.basis c).map E.symm).repr (f (((Pi.basis c).map E.symm) ⟨j, β⟩))
      = (Pi.basis c).repr ((X : K[X]) • Pi.basis c ⟨j, β⟩) := by
    rw [Basis.map_apply, Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, hE,
      LinearEquiv.apply_symm_apply]
  rw [LinearMap.toMatrix_apply, hb, Pi.basis_repr, Pi.basis_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.blockDiagonal'_apply_eq, Pi.smul_apply, Pi.single_eq_same, hc]
    exact congrFun ((c i).repr_sum_self _) a
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij, Pi.smul_apply, Pi.single_eq_of_ne hij,
      smul_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply]

variable [FiniteDimensional K V]

/-- **The Jordan form of a nilpotent endomorphism.** Let $V$ be a finite-dimensional vector space
over a field $K$, and let $g$ be a nilpotent endomorphism of $V$. Then there are
$d \in \mathbb{N}$, positive sizes $e_0, \dots, e_{d-1}$, and a basis of $V$ indexed by the
pairs $(i, a)$ with $a < e_i$, in which the matrix of $g$ is the Jordan form with sizes $e_i$
and all eigenvalues $0$.

No hypothesis on the field is needed. The proof uses the structure theorem for finitely
generated modules over a principal ideal domain: $V$ is a $K[X]$-module with $X$ acting as $g$,
finitely generated and annihilated by a power of $X$, hence a direct sum of cyclic modules
$K[X]/(X^k)$ (`Polynomial.exists_basis_quotient_span_X_pow`). -/
theorem exists_basis_toMatrix_eq_jordanForm_of_isNilpotent {g : End K V} (hg : IsNilpotent g) :
    ∃ (d : ℕ) (e : Fin d → ℕ) (b : Basis ((i : Fin d) × Fin (e i)) K V),
      (∀ i, 0 < e i) ∧ LinearMap.toMatrix b b g = Matrix.jordanForm e (fun _ => (0 : K)) := by
  classical
  have htor : Module.IsTorsion' (AEval' g) (Submonoid.powers (X : K[X])) := by
    rw [Submodule.isTorsion'_powers_iff]
    intro m
    obtain ⟨n, hn⟩ := hg
    refine ⟨n, ?_⟩
    have h := AEval'.X_pow_smul_of g ((AEval'.of g).symm m) n
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, hn]
    simp
  obtain ⟨d, k, ⟨eqv⟩⟩ :=
    Module.torsion_by_prime_power_decomposition (M := AEval' g) irreducible_X htor
  have hc : ∀ i : Fin d, ∃ c : Basis (Fin (k i)) K (K[X] ⧸ (K[X] ∙ (X : K[X]) ^ k i)),
      ∀ j, (X : K[X]) • c j = ∑ a, Matrix.jordanBlock (k i) (0 : K) a j • c a := fun i =>
    Polynomial.exists_basis_quotient_span_X_pow K (k i)
  choose c hcJ using hc
  obtain ⟨E, hEdef⟩ : ∃ E : V ≃ₗ[K] ∀ i, K[X] ⧸ (K[X] ∙ (X : K[X]) ^ k i),
      E = (AEval'.of g).trans ((eqv.restrictScalars K).trans
        ((DirectSum.linearEquivFunOnFintype K[X] (Fin d) _).restrictScalars K)) := ⟨_, rfl⟩
  have hE : ∀ v : V, E (g v) = (X : K[X]) • E v := fun v => by
    simp only [hEdef, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      ← AEval'.X_smul_of g v, map_smul]
  obtain ⟨b, hb⟩ := exists_basis_toMatrix_eq_blockDiagonal' g c
    (fun i => Matrix.jordanBlock (k i) (0 : K)) E hE hcJ
  obtain ⟨p, φ, ρ, hpos, hρ⟩ :=
    Matrix.exists_equiv_submatrix_jordanForm_pos k (fun _ => (0 : K))
  refine ⟨p, fun j => k (φ j), b.reindex ρ.symm, hpos, ?_⟩
  rw [LinearMap.toMatrix_reindex, Equiv.symm_symm, hb]
  exact hρ

/-- **The Jordan form of an endomorphism with a single eigenvalue.** Let $V$ be a finite-dimensional
vector space over a field $K$, let $\mu \in K$, and let $f$ be an endomorphism of $V$ such that
$f - \mu$ is nilpotent. Then there are $d \in \mathbb{N}$, positive sizes $e_0, \dots, e_{d-1}$,
and a basis of $V$ indexed by the pairs $(i, a)$ with $a < e_i$, in which the matrix of $f$ is
the Jordan form with sizes $e_i$ and all eigenvalues $\mu$.

This is `Module.End.exists_basis_toMatrix_eq_jordanForm_of_isNilpotent` shifted by $\mu$. -/
theorem exists_basis_toMatrix_eq_jordanForm_of_isNilpotent_sub {f : End K V} {μ : K}
    (hf : IsNilpotent (f - algebraMap K (End K V) μ)) :
    ∃ (d : ℕ) (e : Fin d → ℕ) (b : Basis ((i : Fin d) × Fin (e i)) K V),
      (∀ i, 0 < e i) ∧ LinearMap.toMatrix b b f = Matrix.jordanForm e (fun _ => μ) := by
  obtain ⟨d, e, b, hpos, hb⟩ := exists_basis_toMatrix_eq_jordanForm_of_isNilpotent hf
  refine ⟨d, e, b, hpos, ?_⟩
  have hid : LinearMap.toMatrix b b (algebraMap K (End K V) μ) = μ • 1 := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.toMatrix_one]
  rw [Matrix.jordanForm_const_eq_add_smul_one, ← hb, ← hid, ← map_add, sub_add_cancel]

variable [IsAlgClosed K]

/-- **The Jordan canonical form of an endomorphism**, grouped by eigenvalue. Let $V$ be a
finite-dimensional vector space over an algebraically closed field $K$, and let $f$ be an
endomorphism of $V$. Then there are $q \in \mathbb{N}$, distinct scalars
$\nu_0, \dots, \nu_{q-1}$, numbers $d_i$, positive sizes $e_{ij}$ for $j < d_i$, and a basis of
$V$ indexed by the triples $(i, j, a)$ with $a < e_{ij}$, such that:

* the eigenvalues of $f$ are exactly $\nu_0, \dots, \nu_{q-1}$;
* the matrix of $f$ in the basis is block diagonal with $q$ outer blocks, and the $i$-th outer
  block is the Jordan form with sizes $e_{ij}$, $j < d_i$, and all eigenvalues $\nu_i$.

The outer decomposition is the decomposition of $V$ into the maximal generalized eigenspaces of
$f$. The inner one is `Module.End.exists_basis_toMatrix_eq_jordanForm_of_isNilpotent_sub`
applied on each of them, where $f - \nu_i$ is nilpotent. -/
theorem exists_basis_toMatrix_eq_blockDiagonal'_jordanForm (f : End K V) :
    ∃ (q : ℕ) (ν : Fin q → K) (d : Fin q → ℕ) (e : ∀ i : Fin q, Fin (d i) → ℕ)
      (b : Basis ((i : Fin q) × (j : Fin (d i)) × Fin (e i j)) K V),
      Function.Injective ν ∧ (∀ μ : K, f.HasEigenvalue μ ↔ μ ∈ Set.range ν) ∧
        (∀ i j, 0 < e i j) ∧
        LinearMap.toMatrix b b f
          = Matrix.blockDiagonal' fun i => Matrix.jordanForm (e i) (fun _ => ν i) := by
  classical
  have hfin : {μ : K | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  set s : Finset K := hfin.toFinset
  set ε : Fin s.card ≃ {x // x ∈ s} := s.equivFin.symm
  set ν : Fin s.card → K := fun i => (ε i : K) with hν
  have hνinj : Function.Injective ν := fun i j h => ε.injective (Subtype.ext h)
  have hνmem : ∀ μ : K, f.maxGenEigenspace μ ≠ ⊥ ↔ μ ∈ Set.range ν := by
    intro μ
    refine ⟨fun h => ⟨ε.symm ⟨μ, hfin.mem_toFinset.2 h⟩, by simp [hν]⟩, ?_⟩
    rintro ⟨i, rfl⟩
    exact hfin.mem_toFinset.1 (ε i).2
  set A : Fin s.card → Submodule K V := fun i => f.maxGenEigenspace (ν i)
  have hindep : iSupIndep A := f.independent_maxGenEigenspace.comp hνinj
  have htop : ⨆ i, A i = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← f.iSup_maxGenEigenspace_eq_top]
    refine iSup_le fun μ => ?_
    by_cases h : f.maxGenEigenspace μ = ⊥
    · rw [h]
      exact bot_le
    · obtain ⟨i, rfl⟩ := (hνmem μ).1 h
      exact le_iSup A i
  have hds : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep htop
  have hmaps : ∀ i, Set.MapsTo f (A i) (A i) := fun i =>
    f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) (ν i)
  have hnil : ∀ i, IsNilpotent (f.restrict (hmaps i) - algebraMap K (End K (A i)) (ν i)) := by
    intro i
    have h1 := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (ν i)
    have heq : (f - algebraMap K (End K V) (ν i)).restrict
        (Module.End.mapsTo_maxGenEigenspace_of_comm
          (Algebra.mul_sub_algebraMap_commutes f (ν i)) (ν i))
        = f.restrict (hmaps i) - algebraMap K (End K (A i)) (ν i) := by
      rfl
    rwa [heq] at h1
  choose d e bb hepos hbb using fun i =>
    exists_basis_toMatrix_eq_jordanForm_of_isNilpotent_sub (hnil i)
  refine ⟨s.card, ν, d, e, hds.collectedBasis bb, hνinj, fun μ => ?_, hepos, ?_⟩
  · rw [show f.HasEigenvalue μ ↔ f.maxGenEigenspace μ ≠ ⊥ from
      (hasUnifEigenvalue_iff_hasUnifEigenvalue_one (f := f) (μ := μ) (k := ⊤) (by simp)).symm,
      hνmem]
  · rw [LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal' hds hds bb bb hmaps]
    exact congrArg Matrix.blockDiagonal' (funext hbb)

/-- **The Jordan canonical form of an endomorphism.** Let $V$ be a finite-dimensional vector space
over an algebraically closed field $K$, and let $f$ be an endomorphism of $V$. Then there are
$p \in \mathbb{N}$, positive sizes $e_0, \dots, e_{p-1}$, scalars $\mu_0, \dots, \mu_{p-1}$, and
a basis of $V$ indexed by the pairs $(i, a)$ with $a < e_i$, in which the matrix of $f$ is the
Jordan form with sizes $e_i$ and eigenvalues $\mu_i$.

This is `Module.End.exists_basis_toMatrix_eq_blockDiagonal'_jordanForm` with the two levels of
the block structure flattened into one. The grouping of the blocks by eigenvalue is lost. -/
theorem exists_basis_toMatrix_eq_jordanForm (f : End K V) :
    ∃ (p : ℕ) (e : Fin p → ℕ) (μ : Fin p → K) (b : Basis ((i : Fin p) × Fin (e i)) K V),
      (∀ i, 0 < e i) ∧ LinearMap.toMatrix b b f = Matrix.jordanForm e μ := by
  classical
  obtain ⟨q, ν, d, e, b, -, -, hepos, hb⟩ := exists_basis_toMatrix_eq_blockDiagonal'_jordanForm f
  set σ : ((i : Fin q) × Fin (d i)) ≃ Fin (∑ i, d i) := finSigmaFinEquiv
  set τ₁ := (Equiv.sigmaAssoc fun (i : Fin q) (j : Fin (d i)) => Fin (e i j)).symm with hτ₁
  set τ₂ := Equiv.sigmaCongrLeft (β := fun t : (i : Fin q) × Fin (d i) => Fin (e t.1 t.2)) σ.symm
    with hτ₂
  refine ⟨∑ i, d i, fun j => e (σ.symm j).1 (σ.symm j).2, fun j => ν (σ.symm j).1,
    b.reindex (τ₁.trans τ₂.symm), fun j => hepos _ _, ?_⟩
  rw [LinearMap.toMatrix_reindex, hb, Matrix.jordanForm_def]
  simp_rw [Matrix.jordanForm_def]
  rw [Matrix.blockDiagonal'_blockDiagonal' fun (i : Fin q) (j : Fin (d i)) =>
    Matrix.jordanBlock (e i j) (ν i), Matrix.submatrix_submatrix]
  rw [show (⇑τ₁ ∘ ⇑(τ₁.trans τ₂.symm).symm) = ⇑τ₂ from
    funext fun x => by simp [hτ₁, hτ₂]]
  exact Matrix.blockDiagonal'_submatrix_sigmaCongrLeft _ σ.symm

end Module.End

namespace Matrix

variable {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}

/-- The endomorphism $x \mapsto Ax$ of $K^n$ given by a square matrix $A$. -/
private noncomputable abbrev endOf (A : Matrix (Fin n) (Fin n) K) :
    Module.End K (Fin n → K) :=
  Matrix.toLin (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) A

omit [IsAlgClosed K] in
/-- Let $A$ be a square matrix of order $n$, $b$ a basis of $K^n$ indexed by $\iota$, and
$\sigma : \iota \to \{0, \dots, n - 1\}$ a bijection. Then there is an invertible $P$ such that
$P^{-1} A P$ is the matrix of $x \mapsto Ax$ in the basis $b$, reindexed by $\sigma$. -/
private theorem exists_isUnit_conj_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin n) (Fin n) K) (b : Basis ι K (Fin n → K)) (σ : ι ≃ Fin n) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧
      P⁻¹ * A * P = reindex σ σ (LinearMap.toMatrix b b (endOf A)) := by
  classical
  refine ⟨(Pi.basisFun K (Fin n)).toMatrix (b.reindex σ),
    (Matrix.isUnit_iff_isUnit_det _).2
      (Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _)), ?_⟩
  rw [Matrix.inv_eq_right_inv
    (Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun K (Fin n)) (b.reindex σ))]
  conv_lhs => rw [← LinearMap.toMatrix_toLin (v₁ := Pi.basisFun K (Fin n))
    (v₂ := Pi.basisFun K (Fin n)) A]
  rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix, LinearMap.toMatrix_reindex]
  rfl

omit [IsAlgClosed K] in
/-- A scalar $\mu$ is an eigenvalue of the endomorphism $x \mapsto Ax$ if and only if $Av = \mu v$
for some $v \ne 0$. -/
private theorem hasEigenvalue_endOf_iff (A : Matrix (Fin n) (Fin n) K) (μ : K) :
    (endOf A).HasEigenvalue μ ↔ ∃ v ≠ 0, A *ᵥ v = μ • v := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  refine exists_congr fun v => ?_
  simp only [Module.End.mem_eigenspace_iff, endOf, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  tauto

/-- **The Jordan canonical form of a matrix.** Let $K$ be an algebraically closed field and
$A \in K^{n \times n}$. Then there are $p \in \mathbb{N}$, positive sizes $e_0, \dots, e_{p-1}$
with $\sum_i e_i = n$, scalars $\mu_0, \dots, \mu_{p-1}$, and an invertible matrix
$P \in K^{n \times n}$ such that $P^{-1} A P$ is the Jordan form with sizes $e_i$ and
eigenvalues $\mu_i$, with its blocks placed consecutively along the diagonal.

The placement of the blocks is the bijection `finSigmaFinEquiv` from the pairs $(i, a)$,
$a < e_i$, to $\{0, \dots, n - 1\}$. -/
theorem exists_conj_jordanForm (A : Matrix (Fin n) (Fin n) K) :
    ∃ (p : ℕ) (e : Fin p → ℕ) (μ : Fin p → K) (he : ∑ i, e i = n)
      (P : Matrix (Fin n) (Fin n) K), (∀ i, 0 < e i) ∧ IsUnit P ∧
        P⁻¹ * A * P = reindex (finSigmaFinEquiv.trans (finCongr he))
          (finSigmaFinEquiv.trans (finCongr he)) (jordanForm e μ) := by
  classical
  obtain ⟨p, e, μ, b, hepos, hb⟩ := Module.End.exists_basis_toMatrix_eq_jordanForm (endOf A)
  have he : ∑ i, e i = n := by
    simpa [Fintype.card_sigma] using
      (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_fin_fun K)
  obtain ⟨P, hP, hPA⟩ :=
    exists_isUnit_conj_toMatrix A b (finSigmaFinEquiv.trans (finCongr he))
  exact ⟨p, e, μ, he, P, hepos, hP, by rw [hPA, hb]⟩

/-- **The Jordan canonical form of a matrix**, grouped by eigenvalue. Let $K$ be an algebraically
closed field and $A \in K^{n \times n}$. Then there are $q \in \mathbb{N}$, distinct scalars
$\nu_0, \dots, \nu_{q-1}$, numbers $d_i$, positive sizes $e_{ij}$ for $j < d_i$, a bijection
$\sigma$ from the triples $(i, j, a)$ with $a < e_{ij}$ to $\{0, \dots, n - 1\}$, and an
invertible matrix $P \in K^{n \times n}$, such that:

* the eigenvalues of $A$ (the $\mu$ with $Av = \mu v$ for some $v \ne 0$) are exactly
  $\nu_0, \dots, \nu_{q-1}$;
* $P^{-1} A P$ is, after reindexing by $\sigma$, the block diagonal matrix with $q$ outer
  blocks, whose $i$-th outer block is the Jordan form with sizes $e_{ij}$, $j < d_i$, and all
  eigenvalues $\nu_i$.

This is Theorem 1.8 of [saad2003iterative], §1.8.2. The book also identifies the data: $q$ is
the number of distinct eigenvalues, $d_i$ is the geometric multiplicity of $\nu_i$, the sizes
$e_{ij}$ are at most the index of $\nu_i$, and the $i$-th outer block has the algebraic
multiplicity of $\nu_i$ as its size. The first of these is the injectivity of $\nu$ together
with the description of the eigenvalues. The other three are not part of this statement. They
follow by transporting `Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one`,
`Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff` and
`Matrix.rootMultiplicity_charpoly_jordanForm` along the similarity, since the other outer blocks
have different eigenvalues and contribute nothing. -/
theorem exists_conj_blockDiagonal'_jordanForm (A : Matrix (Fin n) (Fin n) K) :
    ∃ (q : ℕ) (ν : Fin q → K) (d : Fin q → ℕ) (e : ∀ i : Fin q, Fin (d i) → ℕ)
      (σ : ((i : Fin q) × (j : Fin (d i)) × Fin (e i j)) ≃ Fin n)
      (P : Matrix (Fin n) (Fin n) K),
      Function.Injective ν ∧ (∀ μ : K, (∃ v ≠ 0, A *ᵥ v = μ • v) ↔ μ ∈ Set.range ν) ∧
        (∀ i j, 0 < e i j) ∧ IsUnit P ∧ P⁻¹ * A * P
          = reindex σ σ (blockDiagonal' fun i => jordanForm (e i) (fun _ => ν i)) := by
  classical
  obtain ⟨q, ν, d, e, b, hinj, heig, hepos, hb⟩ :=
    Module.End.exists_basis_toMatrix_eq_blockDiagonal'_jordanForm (endOf A)
  obtain ⟨σ, -⟩ : ∃ σ : ((i : Fin q) × (j : Fin (d i)) × Fin (e i j)) ≃ Fin n, True :=
    ⟨(Fintype.equivFinOfCardEq
      ((Module.finrank_eq_card_basis b).symm.trans (Module.finrank_fin_fun K))), trivial⟩
  obtain ⟨P, hP, hPA⟩ := exists_isUnit_conj_toMatrix A b σ
  exact ⟨q, ν, d, e, σ, P, hinj,
    fun μ => (hasEigenvalue_endOf_iff A μ).symm.trans (heig μ), hepos, hP, by rw [hPA, hb]⟩

end Matrix

namespace Matrix

/-! ### Principal vectors -/

section PrincipalVectors

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] {e : ι → ℕ} {μ : ι → R}

omit [DecidableEq ι] in
/-- Two pairs $(i, a)$ and $(i, b)$ with the same first component are equal only if $a = b$. -/
private theorem snd_eq_of_sigma_mk_eq {i : ι} {a b : Fin (e i)}
    (h : (⟨i, a⟩ : (i : ι) × Fin (e i)) = ⟨i, b⟩) : a = b :=
  eq_of_heq (Sigma.mk.inj_iff.1 h).2

/-- The column $(i, 0)$ of a Jordan form, for $e_i > 0$, is $\mu_i$ times the unit vector
$e_{(i, 0)}$. -/
theorem jordanForm_transpose_zero (i : ι) (h0 : 0 < e i) :
    (jordanForm e μ)ᵀ ⟨i, ⟨0, h0⟩⟩ = μ i • Pi.single (⟨i, ⟨0, h0⟩⟩ : (i : ι) × Fin (e i)) 1 := by
  funext ⟨i', j'⟩
  rw [transpose_apply, jordanForm_def, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne i' i with rfl | hi
  · rw [blockDiagonal'_apply_eq, jordanBlock_apply]
    rcases eq_or_ne j' ⟨0, h0⟩ with rfl | hj
    · simp
    · have hj' : ¬ ((j' : ℕ) + 1 = 0) := by omega
      rw [ite_eq_right hj, ite_eq_right hj',
        Pi.single_eq_of_ne (fun h => hj (snd_eq_of_sigma_mk_eq h)), mul_zero]
  · rw [blockDiagonal'_apply_ne _ _ _ hi, Pi.single_eq_of_ne (fun h => hi (congrArg Sigma.fst h)),
      mul_zero]

/-- The column $(i, j + 1)$ of a Jordan form, for $j + 1 < e_i$, is
$\mu_i e_{(i, j+1)} + e_{(i, j)}$. -/
theorem jordanForm_transpose_succ (i : ι) (j : ℕ) (hj : j + 1 < e i) :
    (jordanForm e μ)ᵀ ⟨i, ⟨j + 1, hj⟩⟩
      = μ i • Pi.single (⟨i, ⟨j + 1, hj⟩⟩ : (i : ι) × Fin (e i)) 1
        + Pi.single (⟨i, ⟨j, by omega⟩⟩ : (i : ι) × Fin (e i)) 1 := by
  funext ⟨i', j'⟩
  rw [transpose_apply, jordanForm_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne i' i with rfl | hi
  · rw [blockDiagonal'_apply_eq, jordanBlock_apply]
    have hne : (⟨j + 1, hj⟩ : Fin (e i')) ≠ ⟨j, by omega⟩ := fun h => by
      have := congrArg Fin.val h
      simp at this
    rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | hj1
    · rw [ite_eq_left rfl, Pi.single_eq_same, mul_one,
        Pi.single_eq_of_ne (fun h => hne (snd_eq_of_sigma_mk_eq h)), add_zero]
    · rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | hj2
      · rw [ite_eq_right hj1, ite_eq_left (by simp), Pi.single_eq_same,
          Pi.single_eq_of_ne (fun h => hne (snd_eq_of_sigma_mk_eq h).symm), mul_zero, zero_add]
      · have h1 : ¬ ((j' : ℕ) + 1 = j + 1) := fun h => hj2 (Fin.ext (Nat.succ_injective h))
        rw [ite_eq_right hj1, ite_eq_right h1,
          Pi.single_eq_of_ne (fun h => hj1 (snd_eq_of_sigma_mk_eq h)),
          Pi.single_eq_of_ne (fun h => hj2 (snd_eq_of_sigma_mk_eq h)), mul_zero, add_zero]
  · rw [blockDiagonal'_apply_ne _ _ _ hi,
      Pi.single_eq_of_ne (fun h => hi (congrArg Sigma.fst h)),
      Pi.single_eq_of_ne (fun h => hi (congrArg Sigma.fst h)), mul_zero, add_zero]

/-- **The principal-vector recursion.** Let $R$ be a commutative ring, let $J$ be the Jordan form
with sizes $e_i$ and eigenvalues $\mu_i$, $i \in \iota$ finite, and let $A$ and $X$ be square
matrices of the same order as $J$, with $X$ invertible and $X^{-1} A X = J$. Write $x_{i,j}$ for
the column $(i, j)$ of $X$. Then for every block $i$:

* if $e_i > 0$, then $A x_{i,0} = \mu_i x_{i,0}$;
* if $j + 1 < e_i$, then $A x_{i,j+1} = \mu_i x_{i,j+1} + x_{i,j}$.

So each block contributes one eigenvector $x_{i,0}$ and a chain of principal vectors
(generalized eigenvectors) above it. This is (1.8) of [quarteroni2000numerical]. The proof reads
$AX = XJ$ column by column. The column $x_{i,j}$ is `Xᵀ ⟨i, j⟩`. -/
theorem mulVec_eq_of_conj_jordanForm [Fintype ι]
    {A X : Matrix ((i : ι) × Fin (e i)) ((i : ι) × Fin (e i)) R} (hX : IsUnit X)
    (h : X⁻¹ * A * X = jordanForm e μ) :
    (∀ (i : ι) (h0 : 0 < e i), A *ᵥ Xᵀ ⟨i, ⟨0, h0⟩⟩ = μ i • Xᵀ ⟨i, ⟨0, h0⟩⟩) ∧
      ∀ (i : ι) (j : ℕ) (hj : j + 1 < e i),
        A *ᵥ Xᵀ ⟨i, ⟨j + 1, hj⟩⟩ = μ i • Xᵀ ⟨i, ⟨j + 1, hj⟩⟩ + Xᵀ ⟨i, ⟨j, by omega⟩⟩ := by
  have hAX : A * X = X * jordanForm e μ := by
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hX), Matrix.one_mul]
  have hcol : ∀ c, A *ᵥ Xᵀ c = X *ᵥ (jordanForm e μ)ᵀ c := fun c =>
    col_mul_eq_mulVec_col.symm.trans ((congrArg (col · c) hAX).trans col_mul_eq_mulVec_col)
  refine ⟨fun i h0 => ?_, fun i j hj => ?_⟩
  · rw [hcol, jordanForm_transpose_zero, mulVec_smul, mulVec_single_one]
    rfl
  · rw [hcol, jordanForm_transpose_succ, mulVec_add, mulVec_smul, mulVec_single_one,
      mulVec_single_one]
    rfl

end PrincipalVectors

/-! ### Geometric versus algebraic multiplicity -/

section Multiplicity

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a square matrix $A$ over a field and a scalar $\mu$, the eigenspace of the map
$x \mapsto Ax$ for $\mu$ is the null space of $A - \mu I$. -/
theorem eigenspace_mulVecLin_eq_ker (A : Matrix n n K) (μ : K) :
    Module.End.eigenspace A.mulVecLin μ = LinearMap.ker (A - μ • 1).mulVecLin := by
  ext v
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply,
    sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]

/-- **The geometric multiplicity of an eigenvalue is at most its algebraic multiplicity.** Let $A$
be a square matrix over a field $K$ and $\mu \in K$. Then the dimension of the eigenspace of
$x \mapsto Ax$ for $\mu$ is at most the multiplicity of $\mu$ as a root of the characteristic
polynomial of $A$.

This is stated in [quarteroni2000numerical], §1.7. The proof is Mathlib's
`LinearMap.finrank_eigenspace_le` for the map $x \mapsto Ax$. The Jordan form shows where the
gap comes from: the eigenspace of $\mu$ has one dimension for each block with eigenvalue $\mu$
(`Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one`), while the root multiplicity is the
total size of these blocks (`Matrix.rootMultiplicity_charpoly_jordanForm`). A matrix is
nondefective if equality holds for every $\mu$. -/
theorem finrank_eigenspace_le_rootMultiplicity_charpoly (A : Matrix n n K) (μ : K) :
    finrank K (Module.End.eigenspace A.mulVecLin μ) ≤ A.charpoly.rootMultiplicity μ := by
  have h := LinearMap.finrank_eigenspace_le A.mulVecLin μ
  rwa [charpoly_mulVecLin] at h

end Multiplicity

/-! ### Uniqueness of the Jordan form -/

section Uniqueness

variable {K : Type*} [Field K] [DecidableEq K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The number of Jordan blocks of size at least $k + 1$.** Over a field $K$, let $\iota$ be
finite and let $J$ be the Jordan form with sizes $e_i$ and eigenvalues $\mu_i$. Then for every
$c \in K$ and $k \in \mathbb{N}$,
$$\dim \ker (J - cI)^{k+1} - \dim \ker (J - cI)^k = \#\{i \in \iota : \mu_i = c,\ k + 1 \le
  e_i\}.$$

This is the statement of [golub2013matrix], §7.6.5, that "$p_i - p_{i-1}$ equals the number of
blocks in $C$'s Jordan form that have dimension $i$ or greater". Each block with eigenvalue $c$
contributes $\min(e_i, k)$ to the $k$-th nullity
(`Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow`), and this grows by one from $k$ to
$k + 1$ exactly when $k + 1 \le e_i$. -/
theorem card_filter_le_jordanBlocks_eq (e : ι → ℕ) (μ : ι → K) (c : K) (k : ℕ) :
    Module.finrank K (LinearMap.ker (((jordanForm e μ - c • 1) ^ (k + 1)).mulVecLin)) -
        Module.finrank K (LinearMap.ker (((jordanForm e μ - c • 1) ^ k).mulVecLin)) =
      (Finset.univ.filter fun i => μ i = c ∧ k + 1 ≤ e i).card := by
  rw [finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow,
    finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow]
  have hsplit : ∑ i ∈ Finset.univ.filter fun i => μ i = c, min (e i) (k + 1) =
      ∑ i ∈ Finset.univ.filter fun i => μ i = c, min (e i) k +
        ∑ i ∈ Finset.univ.filter fun i => μ i = c, if k + 1 ≤ e i then 1 else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h <;> omega
  rw [hsplit, add_tsub_cancel_left, Finset.sum_boole, Finset.filter_filter]
  simp

omit [DecidableEq K] in
/-- If $A$ is similar to $J$ reindexed by a bijection, then
$\dim \ker (A - cI)^k = \dim \ker (J - cI)^k$ for every $c$ and $k$. -/
theorem finrank_ker_pow_eq_of_isSimilar_reindex {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] {A : Matrix n n K} {J : Matrix m m K} (σ : m ≃ n)
    (h : IsSimilar A (J.reindex σ σ)) (c : K) (k : ℕ) :
    Module.finrank K (LinearMap.ker (((A - c • 1) ^ k).mulVecLin)) =
      Module.finrank K (LinearMap.ker (((J - c • 1) ^ k).mulVecLin)) := by
  have hr : (J.reindex σ σ - c • 1) ^ k = ((J - c • 1) ^ k).reindex σ σ := by
    have := map_pow (reindexAlgEquiv K K σ) (J - c • 1) k
    rw [map_sub, map_smul, map_one] at this
    simpa using this.symm
  rw [((h.sub_smul_one c).pow k).finrank_ker_mulVecLin_eq, hr, finrank_ker_mulVecLin_reindex]

omit [Field K] in
/-- For a family of sizes $f_i$ and scalars $\nu_i$, the number of $i$ with $\nu_i = c$ and
$f_i = k + 1$, plus the number with $\nu_i = c$ and $f_i \ge k + 2$, is the number with
$\nu_i = c$ and $f_i \ge k + 1$. -/
private theorem card_filter_eq_add_card_filter_le {κ : Type*} [Fintype κ] (f : κ → ℕ)
    (ν : κ → K) (c : K) (k : ℕ) :
    (Finset.univ.filter fun i => ν i = c ∧ f i = k + 1).card +
        (Finset.univ.filter fun i => ν i = c ∧ k + 2 ≤ f i).card =
      (Finset.univ.filter fun i => ν i = c ∧ k + 1 ≤ f i).card := by
  classical
  have hdisj : Disjoint (Finset.univ.filter fun i => ν i = c ∧ f i = k + 1)
      (Finset.univ.filter fun i => ν i = c ∧ k + 2 ≤ f i) :=
    Finset.disjoint_filter.mpr fun i _ h1 h2 => by omega
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_or]
  congr 1
  refine Finset.filter_congr fun i _ => ⟨?_, ?_⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    exacts [⟨h1, by omega⟩, ⟨h1, by omega⟩]
  · rintro ⟨h1, h2⟩
    rcases (show f i = k + 1 ∨ k + 2 ≤ f i by omega) with h | h
    exacts [Or.inl ⟨h1, h⟩, Or.inr ⟨h1, h⟩]

omit [Field K] in
/-- If all sizes $f_i$ are positive, no index $i$ has $\nu_i = c$ and $f_i = 0$. -/
private theorem card_filter_eq_zero_of_pos {κ : Type*} [Fintype κ] (f : κ → ℕ) (ν : κ → K)
    (c : K) (hf : ∀ i, 0 < f i) : (Finset.univ.filter fun i => ν i = c ∧ f i = 0).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun i _ hi => (hf i).ne' hi.2

/-- **Uniqueness of the Jordan form** up to the order of the blocks. Let $K$ be a field and $A$ a
square matrix over $K$ indexed by a finite type $n$. Let $J$ be the Jordan form with positive
sizes $e_i$ and eigenvalues $\mu_i$, $i \in \iota$, and $J'$ the Jordan form with positive sizes
$e'_{i'}$ and eigenvalues $\mu'_{i'}$, $i' \in \iota'$, with $\iota$ and $\iota'$ finite. Let
$\sigma$ and $\sigma'$ be bijections from the index types of $J$ and $J'$ to $n$, and assume
that $A$ is similar to $J$ reindexed by $\sigma$ and to $J'$ reindexed by $\sigma'$. Then for
every $c \in K$ and $k \in \mathbb{N}$,
$$\#\{i \in \iota : \mu_i = c,\ e_i = k\} = \#\{i' \in \iota' : \mu'_{i'} = c,\ e'_{i'} = k\}.$$

This is the uniqueness statement of [golub2013matrix] after Theorem 7.1.9: "the number and
dimensions of the Jordan blocks associated with each distinct eigenvalue are unique". The number
of blocks of size at least $k$ is a difference of nullities of powers of $A - cI$
(`Matrix.card_filter_le_jordanBlocks_eq`), which is a similarity invariant, and the number of
blocks of size $k$ is the number of size at least $k$ minus the number of size at least $k + 1$. -/
theorem card_jordanBlocks_eq_of_isSimilar {n : Type*} [Fintype n] [DecidableEq n] {ι' : Type*}
    [Fintype ι'] [DecidableEq ι'] {e : ι → ℕ} {μ : ι → K} {e' : ι' → ℕ} {μ' : ι' → K}
    (he : ∀ i, 0 < e i) (he' : ∀ i, 0 < e' i) {A : Matrix n n K}
    (σ : ((i : ι) × Fin (e i)) ≃ n) (σ' : ((i : ι') × Fin (e' i)) ≃ n)
    (h : IsSimilar A ((jordanForm e μ).reindex σ σ))
    (h' : IsSimilar A ((jordanForm e' μ').reindex σ' σ')) (c : K) (k : ℕ) :
    (Finset.univ.filter fun i => μ i = c ∧ e i = k).card =
      (Finset.univ.filter fun i => μ' i = c ∧ e' i = k).card := by
  -- the number of blocks of size at least `k + 1` is an invariant of `A`
  have hge : ∀ k : ℕ, (Finset.univ.filter fun i => μ i = c ∧ k + 1 ≤ e i).card =
      (Finset.univ.filter fun i => μ' i = c ∧ k + 1 ≤ e' i).card := fun k => by
    rw [← card_filter_le_jordanBlocks_eq, ← card_filter_le_jordanBlocks_eq,
      ← finrank_ker_pow_eq_of_isSimilar_reindex σ h, ← finrank_ker_pow_eq_of_isSimilar_reindex σ h,
      finrank_ker_pow_eq_of_isSimilar_reindex σ' h',
      finrank_ker_pow_eq_of_isSimilar_reindex σ' h']
  rcases k with _ | k
  · rw [card_filter_eq_zero_of_pos e μ c he, card_filter_eq_zero_of_pos e' μ' c he']
  · have h1 := card_filter_eq_add_card_filter_le e μ c k
    have h2 := card_filter_eq_add_card_filter_le e' μ' c k
    have h3 := hge k
    have h4 : (Finset.univ.filter fun i => μ i = c ∧ k + 2 ≤ e i).card =
        (Finset.univ.filter fun i => μ' i = c ∧ k + 2 ≤ e' i).card := hge (k + 1)
    omega

end Uniqueness

end Matrix
