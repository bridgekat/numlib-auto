/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Jordan`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.AdjoinRoot
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# The Jordan canonical form

A **Jordan block** `Matrix.jordanBlock n μ` is the `n × n` upper bidiagonal matrix carrying the
scalar `μ` on the diagonal and `1` on the superdiagonal, and a **Jordan form**
`Matrix.jordanForm e μ` is the block diagonal matrix assembled from a finite family of Jordan
blocks, of sizes `e i` and eigenvalues `μ i`. Over an algebraically closed field every endomorphism
of a finite-dimensional vector space is a Jordan form in a suitable basis, and hence every square
matrix is similar to one. This is the Jordan canonical form of Yousef Saad, *Iterative Methods for
Sparse Linear Systems*, 2nd edition, SIAM, 2003 [saad2003iterative], §1.8.2, Theorem 1.8.

The **multiplicity arithmetic** of a Jordan form is here too: its characteristic polynomial, and
the dimensions of the null spaces of the powers of `jordanForm e μ - c`. Between them they identify
the three numbers a textbook attaches to an eigenvalue `c`. The *algebraic* multiplicity, the
multiplicity of `c` as a root of the characteristic polynomial, is the total size of the blocks
carrying `c`; the *geometric* multiplicity, the dimension of the eigenspace, is the number of those
blocks, each contributing one eigenvector; and the *index*, the least `k` at which the null spaces
of the powers of `jordanForm e μ - c` stop growing, is the largest of their sizes.

## Main definitions

* `Matrix.jordanBlock n μ`: the Jordan block of size `n` for the scalar `μ`.
* `Matrix.jordanForm e μ`: the block diagonal matrix of Jordan blocks `jordanBlock (e i) (μ i)`,
  indexed by `(i : ι) × Fin (e i)`.

## Main statements

* `Module.End.exists_basis_toMatrix_eq_jordanForm_of_isNilpotent`: a **nilpotent** endomorphism is
  a Jordan form with all eigenvalues `0` in some basis. No hypothesis on the field.
* `Module.End.exists_basis_toMatrix_eq_jordanForm_of_isNilpotent_sub`: the same shifted by `μ`, for
  an endomorphism with `f - μ` nilpotent, that is, with the single eigenvalue `μ`.
* `Module.End.exists_basis_toMatrix_eq_blockDiagonal'_jordanForm`: the canonical form over an
  algebraically closed field, **grouped by eigenvalue**: one outer block for each of the distinct
  eigenvalues `ν i`, itself a Jordan form all of whose blocks carry `ν i`.
* `Module.End.exists_basis_toMatrix_eq_jordanForm`: the same with the two levels flattened, so that
  the matrix of `f` is a single `Matrix.jordanForm`.
* `Matrix.exists_conj_jordanForm`: the matrix form, `P⁻¹ * A * P` a Jordan form with its blocks
  laid out consecutively along the diagonal.
* `Matrix.exists_conj_blockDiagonal'_jordanForm`: the matrix form grouped by eigenvalue, which is
  the shape in which the textbook states it.
* `Matrix.charpoly_jordanForm`: the characteristic polynomial `∏ i, (X - μ i) ^ e i` of a Jordan
  form, and `Matrix.rootMultiplicity_charpoly_jordanForm` for the **algebraic multiplicity** it
  gives each eigenvalue.
* `Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow`: the dimension of the null space of
  `(jordanForm e μ - c) ^ k`, namely `∑ i, min (e i) k` over the blocks carrying `c`. Its two
  specialisations are `Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one`, the **geometric
  multiplicity** at `k = 1`, and
  `Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff`, which says that the
  dimensions stop growing at `k` exactly when every block carrying `c` has size at most `k`, so
  that the least such `k` — the **index** of `c` — is the largest of those sizes.
* `Matrix.exists_equiv_submatrix_jordanForm_pos`: the size-zero blocks that `Matrix.jordanForm`
  admits, and that would spoil those counts, can always be dropped. The existence theorems above
  produce block sizes that are already positive.

## Implementation notes

The endomorphism statements give a `Basis` and describe `LinearMap.toMatrix` in it. That shape was
chosen over a bundled structure or an abstract direct sum decomposition because it is what a
consumer needs: the basis is the change of coordinates, and an equation between matrices can be
transported, multiplied and specialised with the ordinary `Matrix` API. Indexing the basis by
`(i : ι) × Fin (e i)` rather than by `Fin n` is what makes `Matrix.blockDiagonal'` applicable, and
the block sizes readable off the index type.

Two structure theorems of Mathlib are combined, and neither half is reproved.

* The **eigenvalue split** is `Module.End.iSup_maxGenEigenspace_eq_top` together with
  `Module.End.independent_maxGenEigenspace`: over an algebraically closed field `V` is the internal
  direct sum of the maximal generalized eigenspaces, on each of which `f - μ` is nilpotent by
  `Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`.
* The **cyclic decomposition** of a nilpotent endomorphism `g` is
  `Module.torsion_by_prime_power_decomposition` over the principal ideal domain `K[X]`: the module
  `Module.AEval' g`, which is `V` with `X` acting as `g`, is finitely generated and `X`-power
  torsion, hence a direct sum of cyclic modules `K[X] ⧸ (X ^ k)`. In the `K`-basis of
  `K[X] ⧸ (X ^ k)` given by the images of `X ^ (k - 1), …, X, 1` — obtained from
  `AdjoinRoot.powerBasis'` for the count and from `basisOfTopLeSpanOfCardEqFinrank` — multiplication
  by `X` is the nilpotent Jordan block, which is
  `Polynomial.exists_basis_quotient_span_X_pow`.

The multiplicity statements are read off the block structure with the general block diagonal
results of `Numlib/LinearAlgebra/Matrix/BlockDiagonal.lean` and
`Numlib/LinearAlgebra/Matrix/Rank.lean`: the characteristic polynomial and the nullity of a block
diagonal matrix are the product and the sum over its blocks, so only one Jordan block has to be
understood. A Jordan block with a nonzero eigenvalue is invertible, and the `k`-th power of the
nilpotent one is the `k`-th superdiagonal, whose null space is cut out by the vanishing of the
coordinates from the `k`-th on and hence has dimension `min n k`.

Doing the eigenvalue split first is what produces the grouped statement, which is the one the
textbook states; the flat statement is then a reindexing of it. The opposite order, applying
`Module.equiv_directSum_of_isTorsion` to `Module.AEval' f` directly, gives the flat statement in one
step but leaves the grouping to be recovered by sorting the blocks by eigenvalue, which is harder.
-/

open Polynomial Module
open scoped DirectSum

namespace Matrix

variable {R : Type*} {n : ℕ}

section Zero

variable [Zero R] [One R] {μ : R}

/-- The **Jordan block** of size `n` for the scalar `μ`: the upper bidiagonal matrix with `μ` on the
diagonal and `1` on the superdiagonal. -/
def jordanBlock (n : ℕ) (μ : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = j then μ else if (i : ℕ) + 1 = (j : ℕ) then 1 else 0

/-- The entries of a Jordan block: `μ` on the diagonal, `1` on the superdiagonal, `0` elsewhere. -/
theorem jordanBlock_apply (i j : Fin n) :
    jordanBlock n μ i j = if i = j then μ else if (i : ℕ) + 1 = (j : ℕ) then 1 else 0 := rfl

/-- A diagonal entry of a Jordan block is its eigenvalue. -/
@[simp] theorem jordanBlock_apply_self (i : Fin n) : jordanBlock n μ i i = μ := by
  simp [jordanBlock_apply]

/-- A superdiagonal entry of a Jordan block is `1`. -/
theorem jordanBlock_apply_succ {i j : Fin n} (h : (i : ℕ) + 1 = (j : ℕ)) :
    jordanBlock n μ i j = 1 := by
  have hne : i ≠ j := by rintro rfl; omega
  simp [jordanBlock_apply, hne, h]

/-- Off the diagonal and the superdiagonal a Jordan block vanishes. -/
theorem jordanBlock_apply_of_ne {i j : Fin n} (h₁ : i ≠ j) (h₂ : (i : ℕ) + 1 ≠ (j : ℕ)) :
    jordanBlock n μ i j = 0 := by
  simp [jordanBlock_apply, h₁, h₂]

/-- The diagonal of a Jordan block is constant at its eigenvalue. -/
@[simp] theorem diag_jordanBlock : (jordanBlock n μ).diag = fun _ => μ := by
  funext i
  simp

/-- The entries of a nilpotent Jordan block: `1` on the superdiagonal and `0` elsewhere. -/
theorem jordanBlock_zero_apply (i j : Fin n) :
    jordanBlock n (0 : R) i j = if (i : ℕ) + 1 = (j : ℕ) then 1 else 0 := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [jordanBlock_apply, h]

/-- A Jordan block is upper triangular. -/
theorem isUpperTriangular_jordanBlock : (jordanBlock n μ).IsUpperTriangular := by
  intro i j hji
  rw [id_eq, id_eq, Fin.lt_def] at hji
  exact jordanBlock_apply_of_ne (fun h => by subst h; omega) (by omega)

end Zero

section CommRing

variable [CommRing R] {μ : R}

/-- The characteristic polynomial of a Jordan block. -/
theorem charpoly_jordanBlock : (jordanBlock n μ).charpoly = (X - C μ) ^ n := by
  rw [charpoly_of_isUpperTriangular _ isUpperTriangular_jordanBlock]
  simp

/-- A Jordan block is its nilpotent part plus `μ` times the identity. -/
theorem jordanBlock_eq_add_smul_one : jordanBlock n μ = jordanBlock n 0 + μ • 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [jordanBlock_apply, h, Matrix.one_apply_ne h]

/-- Shifting a Jordan block by a scalar shifts its eigenvalue. -/
theorem jordanBlock_sub_smul_one (c : R) :
    jordanBlock n μ - c • (1 : Matrix (Fin n) (Fin n) R) = jordanBlock n (μ - c) := by
  rw [jordanBlock_eq_add_smul_one (μ := μ), jordanBlock_eq_add_smul_one (μ := μ - c), sub_smul]
  abel

/-- The entries of a power of a nilpotent Jordan block: the `k`-th power carries `1` on the `k`-th
superdiagonal and `0` elsewhere. -/
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

/-- A power of a nilpotent Jordan block shifts a vector down by the exponent. -/
theorem jordanBlock_zero_pow_mulVec_apply (k : ℕ) (v : Fin n → R) (i j : Fin n)
    (hij : (i : ℕ) + k = (j : ℕ)) : ((jordanBlock n (0 : R) ^ k) *ᵥ v) i = v j := by
  simp only [mulVec, dotProduct, jordanBlock_zero_pow_apply]
  rw [Finset.sum_eq_single j]
  · simp [hij]
  · intro b _ hb
    have hne : (i : ℕ) + k ≠ (b : ℕ) := fun hc => hb (Fin.ext (by omega))
    simp [hne]
  · simp

/-- Past the last row that the shift reaches, a power of a nilpotent Jordan block annihilates every
vector. -/
theorem jordanBlock_zero_pow_mulVec_of_le (k : ℕ) (v : Fin n → R) (i : Fin n)
    (hi : n ≤ (i : ℕ) + k) : ((jordanBlock n (0 : R) ^ k) *ᵥ v) i = 0 := by
  simp only [mulVec, dotProduct, jordanBlock_zero_pow_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have := b.isLt
  simp [show (i : ℕ) + k ≠ (b : ℕ) by omega]

end CommRing

section JordanBlockKer

variable {K : Type*} [Field K] {ν : K}

/-- The null space of the `k`-th power of a nilpotent Jordan block consists of the vectors whose
last coordinates, from the `k`-th on, vanish. -/
theorem mem_ker_mulVecLin_jordanBlock_zero_pow {k : ℕ} {v : Fin n → K} :
    v ∈ LinearMap.ker ((jordanBlock n (0 : K) ^ k).mulVecLin)
      ↔ ∀ j : Fin n, k ≤ (j : ℕ) → v j = 0 := by
  simp only [LinearMap.mem_ker, mulVecLin_apply, funext_iff, Pi.zero_apply]
  constructor
  · intro h j hj
    have hlt : (j : ℕ) - k < n := by have := j.isLt; omega
    rw [← jordanBlock_zero_pow_mulVec_apply k v ⟨(j : ℕ) - k, hlt⟩ j (Nat.sub_add_cancel hj)]
    exact h _
  · intro h i
    rcases lt_or_ge ((i : ℕ) + k) n with hi | hi
    · rw [jordanBlock_zero_pow_mulVec_apply k v i ⟨(i : ℕ) + k, hi⟩ rfl]
      exact h _ (Nat.le_add_left k i)
    · exact jordanBlock_zero_pow_mulVec_of_le k v i hi

/-- **The nullity of a power of a nilpotent Jordan block**: the `k`-th power of the nilpotent
Jordan block of size `n` has null space of dimension `min n k`. In particular the block itself,
at `k = 1`, contributes exactly one eigenvector. -/
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

/-- A Jordan block with a nonzero eigenvalue is invertible, so every power of it has trivial null
space. -/
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

/-- **The nullity of a power of a Jordan block**: only a nilpotent block contributes, and then
`min n k`. -/
theorem finrank_ker_mulVecLin_jordanBlock_pow [DecidableEq K] (ν : K) (k : ℕ) :
    Module.finrank K (LinearMap.ker ((jordanBlock n ν ^ k).mulVecLin))
      = if ν = 0 then min n k else 0 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp [finrank_ker_mulVecLin_jordanBlock_zero_pow]
  · simp [hν, ker_mulVecLin_jordanBlock_pow_eq_bot hν]

end JordanBlockKer

section BlockDiagonal

variable {α ι ι' : Type*} [Zero α] [DecidableEq ι] [DecidableEq ι']

/-- Reindexing a block diagonal matrix by a bijection of the block index. -/
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

/-- A block diagonal matrix of block diagonal matrices is, after the reassociation of the index,
a single block diagonal matrix. -/
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

/-- The **Jordan form** built from a family of Jordan blocks: the block diagonal matrix whose `i`-th
block is `jordanBlock (e i) (μ i)`. -/
def jordanForm [Zero R] [One R] (e : ι → ℕ) (μ : ι → R) :
    Matrix ((i : ι) × Fin (e i)) ((i : ι) × Fin (e i)) R :=
  blockDiagonal' fun i => jordanBlock (e i) (μ i)

/-- `Matrix.jordanForm` unfolded to the block diagonal matrix of Jordan blocks that defines it. -/
theorem jordanForm_def [Zero R] [One R] (e : ι → ℕ) (μ : ι → R) :
    jordanForm e μ = blockDiagonal' fun i => jordanBlock (e i) (μ i) := rfl

/-- Shifting a Jordan form by a scalar shifts every eigenvalue. -/
theorem jordanForm_sub_smul_one [CommRing R] (e : ι → ℕ) (μ : ι → R) (c : R) :
    jordanForm e μ - c • 1 = jordanForm e fun i => μ i - c := by
  rw [jordanForm_def, blockDiagonal'_sub_smul_one, jordanForm_def]
  exact congrArg blockDiagonal' (funext fun i => jordanBlock_sub_smul_one c)

/-- A Jordan form with a single repeated eigenvalue is its nilpotent part plus `μ` times the
identity. -/
theorem jordanForm_const_eq_add_smul_one [CommRing R] (e : ι → ℕ) (μ : R) :
    jordanForm e (fun _ => μ) = jordanForm e (fun _ => (0 : R)) + μ • 1 := by
  have h : jordanForm e (fun _ : ι => μ) - μ • 1 = jordanForm e fun _ : ι => (0 : R) := by
    rw [jordanForm_sub_smul_one]
    exact congrArg (jordanForm e) (funext fun _ => sub_self μ)
  rw [← h]
  abel

/-- **The size-zero blocks of a Jordan form can be dropped**: after a permutation of the index, a
Jordan form is a Jordan form whose blocks all have positive size, carrying a subfamily of the same
sizes and eigenvalues.

A `Matrix.jordanForm` is allowed to list blocks of size zero, which contribute nothing to the
matrix; the counts of blocks that the multiplicity statements below produce are the intended ones
only once those have been removed. -/
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

/-- **The characteristic polynomial of a Jordan form**: each block of size `e i` with eigenvalue
`μ i` contributes the factor `(X - μ i) ^ e i`. -/
theorem charpoly_jordanForm [CommRing R] (e : ι → ℕ) (μ : ι → R) :
    (jordanForm e μ).charpoly = ∏ i, (X - C (μ i)) ^ e i := by
  rw [jordanForm_def, charpoly_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ => charpoly_jordanBlock

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- **The algebraic multiplicity of an eigenvalue of a Jordan form**: the multiplicity of `c` as a
root of the characteristic polynomial is the total size of the blocks carrying `c`. -/
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

/-- **The nullity of a power of a shifted Jordan form**: the blocks with eigenvalue `c` each
contribute `min (e i) k`, and the others nothing.

At `k = 1` this is the geometric multiplicity of `c`, each block with eigenvalue `c` contributing
exactly one eigenvector; the growth in `k` is what pins down the index of `c`. -/
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
/-- The null spaces of the powers of a shifted Jordan form stop growing at `k` exactly when every
block carrying `c` has size at most `k`; the least such `k` is the index of `c`. -/
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

/-- **The geometric multiplicity of an eigenvalue of a Jordan form**: the dimension of the null
space of `jordanForm e μ - c` is the number of blocks carrying `c`, each contributing exactly one
eigenvector. -/
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

/-- The matrix of an endomorphism in a reindexed basis is the reindexed matrix. -/
theorem LinearMap.toMatrix_reindex {R M ι ι' : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι R M) (σ : ι ≃ ι') (f : M →ₗ[R] M) :
    LinearMap.toMatrix (b.reindex σ) (b.reindex σ) f
      = (LinearMap.toMatrix b b f).submatrix σ.symm σ.symm := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
    Basis.reindex_apply, Basis.repr_reindex_apply]

namespace Polynomial

/-- The cyclic `K[X]`-module `K[X] ⧸ (X ^ k)` has a `K`-basis, namely the images of
`X ^ (k - 1), …, X, 1`, in which multiplication by `X` is the nilpotent Jordan block of size `k`. -/
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

/-- Transport of a componentwise `X`-action to a block diagonal matrix: if a `K`-linear equivalence
`E` carries `f` to multiplication by `X` on a finite product of `K[X]`-modules, and each factor has
a `K`-basis in which multiplication by `X` has matrix `J i`, then `f` has matrix
`Matrix.blockDiagonal' J` in the transported basis. -/
private theorem exists_basis_toMatrix_eq_blockDiagonal' (f : End K V)
    {d : ℕ} {N : Fin d → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module K[X] (N i)]
    [∀ i, Module K (N i)] [∀ i, IsScalarTower K K[X] (N i)]
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

/-- **The Jordan form of a nilpotent endomorphism**: a nilpotent endomorphism of a
finite-dimensional vector space has a basis in which its matrix is block diagonal, each block a
Jordan block with eigenvalue `0`.  No hypothesis on the field is needed.

The proof runs through the structure theorem for finitely generated modules over a principal ideal
domain: `V` is a `K[X]`-module with `X` acting as `g`, finitely generated and `X`-power torsion
because `g` is nilpotent, hence a direct sum of cyclic modules `K[X] ⧸ (X ^ k)`, each of which is a
nilpotent Jordan block in the basis of the images of `X ^ (k - 1), …, X, 1`. -/
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

/-- **The Jordan form of an endomorphism with a single eigenvalue**: if `f - μ` is nilpotent then
`f` has a basis in which its matrix is block diagonal, each block a Jordan block with eigenvalue
`μ`.  This is the previous theorem shifted by `μ`. -/
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

/-- **The Jordan canonical form of an endomorphism**, grouped by eigenvalue: over an algebraically
closed field a finite-dimensional vector space has a basis in which the matrix of `f` is block
diagonal with one block for each of the `q` distinct eigenvalues `ν i`, and each of those blocks is
itself block diagonal, its blocks the Jordan blocks `Matrix.jordanBlock (e i j) (ν i)`.

The outer decomposition is the decomposition of `V` into the maximal generalized eigenspaces of
`f`; the inner one is `exists_basis_toMatrix_eq_jordanForm_of_isNilpotent_sub` applied on each,
where `f - ν i` is nilpotent. -/
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

/-- **The Jordan canonical form of an endomorphism**: over an algebraically closed field a
finite-dimensional vector space has a basis in which the matrix of `f` is a `Matrix.jordanForm`,
that is, block diagonal with Jordan blocks `Matrix.jordanBlock (e i) (μ i)`.

This is `exists_basis_toMatrix_eq_blockDiagonal'_jordanForm` with the two levels of the block
structure flattened into one; the grouping of the blocks by eigenvalue is lost. -/
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

/-- The endomorphism of `Fin n → K` given by a square matrix, in the form the statements below
use it. -/
private noncomputable abbrev endOf (A : Matrix (Fin n) (Fin n) K) :
    Module.End K (Fin n → K) :=
  Matrix.toLin (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) A

omit [IsAlgClosed K] in
/-- A basis of `Fin n → K`, reindexed by `Fin n`, conjugates `A` into the matrix of `A.endOf` in
that basis. -/
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
/-- The eigenvalues of `A.endOf` are the eigenvalues of `A` in the elementary sense. -/
private theorem hasEigenvalue_endOf_iff (A : Matrix (Fin n) (Fin n) K) (μ : K) :
    (endOf A).HasEigenvalue μ ↔ ∃ v ≠ 0, A *ᵥ v = μ • v := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  refine exists_congr fun v => ?_
  simp only [Module.End.mem_eigenspace_iff, endOf, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  tauto

omit [IsAlgClosed K] in
/-- The number of basis vectors of a basis of `Fin n → K` is `n`. -/
private theorem card_eq_of_basis {ι : Type*} [Fintype ι] (b : Basis ι K (Fin n → K)) :
    Fintype.card ι = n := by
  have h := Module.finrank_eq_card_basis b
  simpa using h.symm

/-- **The Jordan canonical form of a matrix**: over an algebraically closed field every square
matrix is similar to a block diagonal matrix whose diagonal blocks are Jordan blocks, that is, to a
`Matrix.jordanForm` with its blocks laid out consecutively along the diagonal by
`finSigmaFinEquiv`. Every block has positive size. -/
theorem exists_conj_jordanForm (A : Matrix (Fin n) (Fin n) K) :
    ∃ (p : ℕ) (e : Fin p → ℕ) (μ : Fin p → K) (he : ∑ i, e i = n)
      (P : Matrix (Fin n) (Fin n) K), (∀ i, 0 < e i) ∧ IsUnit P ∧
        P⁻¹ * A * P = reindex (finSigmaFinEquiv.trans (finCongr he))
          (finSigmaFinEquiv.trans (finCongr he)) (jordanForm e μ) := by
  classical
  obtain ⟨p, e, μ, b, hepos, hb⟩ := Module.End.exists_basis_toMatrix_eq_jordanForm (endOf A)
  have he : ∑ i, e i = n := by
    simpa [Fintype.card_sigma] using card_eq_of_basis b
  obtain ⟨P, hP, hPA⟩ :=
    exists_isUnit_conj_toMatrix A b (finSigmaFinEquiv.trans (finCongr he))
  exact ⟨p, e, μ, he, P, hepos, hP, by rw [hPA, hb]⟩

/-- **The Jordan canonical form of a matrix, grouped by eigenvalue**: over an algebraically closed
field every square matrix is similar to a block diagonal matrix with one block for each of the `q`
distinct eigenvalues `ν i`, each of those itself block diagonal with Jordan blocks all carrying
`ν i`. The equivalence `σ` names the indices of the resulting matrix by `Fin n`.

Every Jordan block has positive size, so that the counts of blocks are the intended ones.

This is the form of the Jordan canonical form stated by Yousef Saad, *Iterative Methods for Sparse
Linear Systems*, 2nd edition, SIAM, 2003 [saad2003iterative], §1.8.2, Theorem 1.8. The book's
further identifications of the data are not part of this statement: that `q` is the number of
distinct eigenvalues is the injectivity of `ν` together with the description of its range here,
and the remaining three — `d i` is the geometric multiplicity of `ν i`, the sizes `e i j` are
bounded by the index of `ν i`, and the `i`-th outer block has size the algebraic multiplicity of
`ν i` — follow by transporting `Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one`,
`Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff` and
`Matrix.rootMultiplicity_charpoly_jordanForm` for the `i`-th outer block along the conjugation,
the other outer blocks contributing nothing because their eigenvalues differ. -/
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
    ⟨(Fintype.equivFinOfCardEq (card_eq_of_basis b)), trivial⟩
  obtain ⟨P, hP, hPA⟩ := exists_isUnit_conj_toMatrix A b σ
  exact ⟨q, ν, d, e, σ, P, hinj,
    fun μ => (hasEigenvalue_endOf_iff A μ).symm.trans (heig μ), hepos, hP, by rw [hPA, hb]⟩

end Matrix
