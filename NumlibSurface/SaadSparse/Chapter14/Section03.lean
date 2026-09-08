import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearSolve.DomainDecomposition.Schwarz
import Numlib.LinearSolve.Stationary.Block
import NumlibSurface.SaadSparse.Common

/-!
# Saad §14.3: the Schwarz alternating procedures

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §14.3.

The data of the section are index sets `S_i ⊆ {1, …, n}`, not necessarily disjoint, the boolean
restriction matrices `R_i` of §14.3.1 (`restrictSubset`), the local matrices `A_i = R_i A R_iᵀ`
(`localMatrix`), and the operators `T_i = R_iᵀ A_i⁻¹ R_i` of (14.31) (`subdomainInverse`) and
`P_i = T_i A` of (14.24) (`subdomainProjector`).

Everything rests on one identification, `subdomainProjector_eq_energyProjection`: for a symmetric
positive definite `A`, `P_i` **is** the `A`-orthogonal projector onto `Ran(R_iᵀ) = span {e_j :
j ∈ S_i}` (`subdomainSpace`).  The whole convergence theory is then read off
`Numlib/LinearSolve/DomainDecomposition/Schwarz.lean`, whose statements are about the orthogonal
projectors of an inner product space, applied in the energy space of `A`.

* §14.3.1–14.3.3: `multiplicativeSweep` is (14.25), `Q_s` its error operator (14.26), and
  `additiveSweep` the additive procedure.  `error_multiplicativeSweep` is the meaning of `Q_s`,
  `proposition_14_3` the fixed-point form (14.27)–(14.28), and `lemma_14_4` the recurrences
  (14.32)–(14.35) that make Algorithms 14.4 and 14.5 run without `A⁻¹`.
* §14.3.4: `A_J` is the additive Schwarz operator (14.37), `theorem_14_5` and `theorem_14_6` the
  two upper bounds on `λ_max(A_J)`, `IsStableDecomposition` and `IsStrengthenedCauchySchwarz`
  Assumptions 1 and 2, `theorem_14_7` the lower bound `λ_min(A_J) ≥ 1/K₀`, `equation_14_39` the
  telescoping identity of a multiplicative sweep, and `lemma_14_8` and `theorem_14_9` its
  contraction rate.

Indices are `0`-based: the book's `i = 1, …, s` is `i ∈ Finset.range s`, and Saad's `card` of the
family is the cutoff `s`.  `(A u, u)` is written `energyInner A u u`, and `‖u‖_A` is
`energyNorm A u`; over `ℝ` these are Saad's own quantities, and over `ℂ` they are the
Hermitian ones.

## §14.2.3 and Theorem 14.2

Theorem 14.2 is about the *other* partitioning of the chapter, the vertex-based one of §14.2.3,
and its block structure (14.8)–(14.14) is built here as `VertexPartitioning`: `s` subdomains, each
owning interior nodes and interface nodes, local matrices `A_i = [[B_i, E_i], [F_i, C_i]]` of
(14.9), off-diagonal blocks `A_ij` whose only nonzero corner is `E_ij` (14.10), and the assembled
Schur complement system `S` of (14.14).  `schurMatrix_eq` identifies `S` with the Schur complement
of the global matrix, and `equation_14_11`, `equation_14_12` and `isConsistent_iff` read the
blocks, the reduced system and the consistency condition (14.22) off it subdomain by subdomain.

Both iterations are then block Gauss–Seidel sweeps for the labelling of the nodes by their
subdomain: `schwarzSweep` is Algorithm 14.3 on the global matrix and `schurGaussSeidelSweep` is a
sweep on (14.12), and `globalLower_eq_blockGaussSeidelSplitting` and
`schurLower_eq_blockGaussSeidelSplitting` are the identifications with
`Matrix.blockGaussSeidelSplitting`.  `theorem_14_2` is Theorem 14.2, and it rests on
`schurComplement_globalLower`: eliminating the interior variables and taking the block-lower
triangle commute.
-/

open Matrix Finset

open scoped ComplexOrder SaadSparse

namespace SaadSparse.Chapter14

/-! ### §14.2.3 and §14.3.1: the vertex-based partitioning and Theorem 14.2

The rest of the file is the *edge-based* picture of §14.3, in which the subdomains are index sets
`S_i ⊆ {1, …, n}`.  This section is the *vertex-based* picture of §14.2.3, which Theorem 14.2 needs
and nothing else in §14.3 uses: the nodes carry a subdomain label, and inside each subdomain they
split into interior nodes and interface nodes.
-/

section VertexBased

/-- §14.2.3: the subdomain a node belongs to.  A node is an interior node `⟨i, a⟩` or an interface
node `⟨i, a⟩` of subdomain `i`, and its label is `i`; this labelling is the `s`-block structure
(14.8) of the global matrix. -/
def nodeLabel {ι : Type*} (P Q : ι → Type*) : ((i : ι) × P i) ⊕ ((i : ι) × Q i) → ι :=
  Sum.elim Sigma.fst Sigma.fst

@[simp]
theorem nodeLabel_inl {ι : Type*} (P Q : ι → Type*) (p : (i : ι) × P i) :
    nodeLabel P Q (Sum.inl p) = p.1 := rfl

@[simp]
theorem nodeLabel_inr {ι : Type*} (P Q : ι → Type*) (p : (i : ι) × Q i) :
    nodeLabel P Q (Sum.inr p) = p.1 := rfl

/-- **§14.2.3, (14.8)–(14.10)**: a vertex-based partitioning into the subdomains `ι`, subdomain `i`
owning the interior nodes `P i` and the interface nodes `Q i`.

The data are the four blocks of (14.9): `B i`, `E i`, `F i` are the interior–interior,
interior–interface and interface–interior couplings of subdomain `i`, and the single matrix `C`
carries all interface–interface couplings at once, its diagonal block being Saad's `C_i` and its
`(i, j)` block his `E_ij` of (14.10).

Nothing further is assumed, because (14.10) is what the shape of this data says: with the nodes
listed interiors first and interfaces last, as in (14.2), the interior rows and columns of the
global matrix are block diagonal over the subdomains, which is exactly the statement that for
`i ≠ j` the block `A_ij` of (14.8) is zero outside its interface–interface corner. -/
structure VertexPartitioning (𝕜 : Type*) {ι : Type*} (P Q : ι → Type*) where
  /-- `B_i` of (14.9): the coupling between the interior nodes of subdomain `i`. -/
  B : ∀ i, Matrix (P i) (P i) 𝕜
  /-- `E_i` of (14.9): the coupling from the interface nodes of subdomain `i` to its interior
  nodes. -/
  E : ∀ i, Matrix (P i) (Q i) 𝕜
  /-- `F_i` of (14.9): the coupling from the interior nodes of subdomain `i` to its interface
  nodes. -/
  F : ∀ i, Matrix (Q i) (P i) 𝕜
  /-- The interface matrix: its `(i, i)` block is `C_i` of (14.9) and its `(i, j)` block is `E_ij`
  of (14.10). -/
  C : Matrix ((i : ι) × Q i) ((i : ι) × Q i) 𝕜

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {P Q : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
variable [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
variable (V : VertexPartitioning 𝕜 P Q)

namespace VertexPartitioning

section Plumbing

omit [Fintype ι] in
/-- The block diagonal filter does nothing to a block diagonal matrix. -/
private theorem ite_blockDiagonal' {m' n' : ι → Type*} (M : ∀ i, Matrix (m' i) (n' i) 𝕜)
    {i j : ι} (a : m' i) (b : n' j) :
    (if i = j then blockDiagonal' M ⟨i, a⟩ ⟨j, b⟩ else 0) = blockDiagonal' M ⟨i, a⟩ ⟨j, b⟩ := by
  by_cases h : i = j
  · simp [h]
  · rw [blockDiagonal'_apply_ne _ a b h]; simp

omit [Fintype ι] in
/-- The strict block-lower filter adds nothing to the block diagonal filter on a block diagonal
matrix. -/
private theorem ite_add_ite_blockDiagonal' {m' n' : ι → Type*} (M : ∀ i, Matrix (m' i) (n' i) 𝕜)
    {i j : ι} (a : m' i) (b : n' j) :
    (if i = j then blockDiagonal' M ⟨i, a⟩ ⟨j, b⟩ else 0)
        + (if j < i then blockDiagonal' M ⟨i, a⟩ ⟨j, b⟩ else 0)
      = blockDiagonal' M ⟨i, a⟩ ⟨j, b⟩ := by
  rcases lt_trichotomy i j with h | h | h
  · rw [blockDiagonal'_apply_ne _ a b h.ne]; simp [h.ne, asymm h]
  · subst h; simp
  · rw [blockDiagonal'_apply_ne _ a b h.ne']; simp [h.ne', h]

variable {m' n' : ι → Type*}

omit [Fintype ι] [LinearOrder ι] in
/-- The interior rows of a block matrix acting on a vector. -/
private theorem comp_inl_fromBlocks_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (M₁₁ : Matrix m m 𝕜) (M₁₂ : Matrix m n 𝕜) (M₂₁ : Matrix n m 𝕜) (M₂₂ : Matrix n n 𝕜)
    (w : m ⊕ n → 𝕜) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *ᵥ w) ∘ Sum.inl
      = M₁₁ *ᵥ (w ∘ Sum.inl) + M₁₂ *ᵥ (w ∘ Sum.inr) := by
  rw [fromBlocks_mulVec]; rfl

omit [Fintype ι] [LinearOrder ι] in
/-- The interface rows of a block matrix acting on a vector. -/
private theorem comp_inr_fromBlocks_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (M₁₁ : Matrix m m 𝕜) (M₁₂ : Matrix m n 𝕜) (M₂₁ : Matrix n m 𝕜) (M₂₂ : Matrix n n 𝕜)
    (w : m ⊕ n → 𝕜) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *ᵥ w) ∘ Sum.inr
      = M₂₁ *ᵥ (w ∘ Sum.inl) + M₂₂ *ᵥ (w ∘ Sum.inr) := by
  rw [fromBlocks_mulVec]; rfl

omit [Fintype ι] [LinearOrder ι] in
/-- On a vector with vanishing interior part only the `(2,2)` block of the matrix is seen. -/
private theorem comp_inr_mulVec_elim_zero {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix (m ⊕ n) (m ⊕ n) 𝕜) (v : n → 𝕜) :
    (M *ᵥ Sum.elim (0 : m → 𝕜) v) ∘ Sum.inr = M.toBlocks₂₂ *ᵥ v := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [comp_inr_fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, zero_add]

omit [LinearOrder ι] in
/-- A block diagonal matrix acts on each block separately. -/
private theorem blockDiagonal'_comp_mulVec [DecidableEq ι] [∀ i, Fintype (n' i)]
    (M : ∀ i, Matrix (m' i) (n' i) 𝕜) (v : ((i : ι) × n' i) → 𝕜) (i : ι) :
    (blockDiagonal' M *ᵥ v) ∘ Sigma.mk i = M i *ᵥ (v ∘ Sigma.mk i) := by
  funext a
  simp only [Function.comp_apply, mulVec, dotProduct]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine (Fintype.sum_eq_single i fun j hj => Finset.sum_eq_zero fun b _ => ?_).trans ?_
  · rw [blockDiagonal'_apply_ne _ a b hj.symm, zero_mul]
  · exact Finset.sum_congr rfl fun b _ => by rw [blockDiagonal'_apply_eq]

omit [LinearOrder ι] in
/-- One block row of a matrix–vector product over a `Sigma` index type. -/
private theorem comp_mulVec_sigma [∀ i, Fintype (n' i)]
    (M : Matrix ((i : ι) × m' i) ((i : ι) × n' i) 𝕜) (v : ((i : ι) × n' i) → 𝕜) (i : ι) :
    (M *ᵥ v) ∘ Sigma.mk i = ∑ j, M.submatrix (Sigma.mk i) (Sigma.mk j) *ᵥ (v ∘ Sigma.mk j) := by
  funext a
  simp only [Function.comp_apply, mulVec, dotProduct, Finset.sum_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl

omit [Fintype ι] [LinearOrder ι] in
/-- Solving `M x + c = d` for `x`. -/
private theorem mulVec_add_eq_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix m m 𝕜}
    (hM : IsUnit M) (x c d : m → 𝕜) : M *ᵥ x + c = d ↔ x = M⁻¹ *ᵥ (d - c) := by
  constructor
  · rintro rfl
    rw [add_sub_cancel_right, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hM),
      one_mulVec]
  · rintro rfl
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM), one_mulVec]
    abel

end Plumbing

/-! #### The blocks (14.8)–(14.14) -/

/-- **(14.8)**: the global matrix of the partitioning, with the nodes listed interiors first and
interfaces last as in (14.2).  The `s`-block structure of (14.8) is carried by `nodeLabel`, not by
the order of the indices; the two differ by a permutation only. -/
def globalMatrix : Matrix (((i : ι) × P i) ⊕ ((i : ι) × Q i))
    (((i : ι) × P i) ⊕ ((i : ι) × Q i)) 𝕜 :=
  fromBlocks (blockDiagonal' V.B) (blockDiagonal' V.E) (blockDiagonal' V.F) V.C

/-- **(14.9)**: `C_i`, the local part of the interface matrix, the coupling between the interface
nodes of subdomain `i`. -/
def localC (i : ι) : Matrix (Q i) (Q i) 𝕜 := V.C.submatrix (Sigma.mk i) (Sigma.mk i)

/-- **(14.9)**: the local matrix `A_i = [[B_i, E_i], [F_i, C_i]]` of subdomain `i`. -/
def localMatrix (i : ι) : Matrix (P i ⊕ Q i) (P i ⊕ Q i) 𝕜 :=
  fromBlocks (V.B i) (V.E i) (V.F i) (V.localC i)

/-- **(14.10)**: `E_ij`, the only nonzero block of `A_ij` for `i ≠ j`, the coupling from the
interface nodes of subdomain `j` to those of subdomain `i`.  At `i = j` it is `localC`, Saad's
`C_i`. -/
def offDiag (i j : ι) : Matrix (Q i) (Q j) 𝕜 := V.C.submatrix (Sigma.mk i) (Sigma.mk j)

/-- **(14.13)**: the local Schur complement `S_i = C_i - F_i B_i⁻¹ E_i` of subdomain `i`. -/
noncomputable def localSchur (i : ι) : Matrix (Q i) (Q i) 𝕜 := (V.localMatrix i).schurComplement

omit [Fintype ι] [LinearOrder ι] [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **(14.13)** unfolded. -/
theorem localSchur_eq (i : ι) :
    V.localSchur i = V.localC i - V.F i * (V.B i)⁻¹ * V.E i := rfl

/-- **(14.14)**: the Schur complement system, assembled from the local Schur complements on the
diagonal and the interface-to-interface couplings `E_ij` off it. -/
noncomputable def schurMatrix : Matrix ((i : ι) × Q i) ((i : ι) × Q i) 𝕜 :=
  V.C - blockDiagonal' fun i => V.F i * (V.B i)⁻¹ * V.E i

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- The Schur complement of a block matrix whose interior rows and columns are the block diagonals
of the local blocks: the interior variables decouple, so `F B⁻¹ E` is assembled subdomain by
subdomain. -/
theorem schurComplement_fromBlocks_local (hB : ∀ i, IsUnit (V.B i))
    (X : Matrix ((i : ι) × Q i) ((i : ι) × Q i) 𝕜) :
    (fromBlocks (blockDiagonal' V.B) (blockDiagonal' V.E) (blockDiagonal' V.F) X).schurComplement
      = X - blockDiagonal' fun i => V.F i * (V.B i)⁻¹ * V.E i := by
  rw [schurComplement_fromBlocks, inv_blockDiagonal' V.B hB, blockDiagonal'_mul,
    blockDiagonal'_mul]

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **(14.14) is (14.5)**: the assembled matrix `S` is the Schur complement of the global matrix
with respect to the interior variables. -/
theorem schurMatrix_eq (hB : ∀ i, IsUnit (V.B i)) :
    V.schurMatrix = V.globalMatrix.schurComplement :=
  (V.schurComplement_fromBlocks_local hB V.C).symm

omit [Fintype ι] [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **(14.14)**: the diagonal blocks of `S` are the local Schur complements `S_i`. -/
theorem blockDiagPart_schurMatrix :
    blockDiagPart Sigma.fst V.schurMatrix = blockDiagonal' V.localSchur := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [blockDiagPart_apply]
  split_ifs with h
  · subst h
    rw [blockDiagonal'_apply_eq, schurMatrix, Matrix.sub_apply, blockDiagonal'_apply_eq]
    rfl
  · rw [blockDiagonal'_apply_ne _ _ _ h]

/-! #### Faithfulness of the block structure -/

omit [Fintype ι] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] in
/-- **(14.9)**: the local matrix `A_i` is the diagonal block of the global matrix on the nodes of
subdomain `i`. -/
theorem submatrix_globalMatrix (i : ι) :
    V.globalMatrix.submatrix (Sum.map (Sigma.mk i) (Sigma.mk i))
        (Sum.map (Sigma.mk i) (Sigma.mk i)) = V.localMatrix i := by
  ext p q
  rcases p with a | a <;> rcases q with b | b <;>
    simp only [Matrix.submatrix_apply, Sum.map_inl, Sum.map_inr, globalMatrix, localMatrix,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂] <;>
    first
      | rw [blockDiagonal'_apply_eq]
      | rfl

omit [Fintype ι] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] in
/-- **(14.10)**: for `i ≠ j` the block `A_ij` of (14.8) has a single nonzero corner, the
interface–interface one, whose entries are those of `E_ij`. -/
theorem equation_14_10 {i j : ι} (h : i ≠ j) (a : P i) (b : P j) (c : Q i) (d : Q j) :
    V.globalMatrix (Sum.inl ⟨i, a⟩) (Sum.inl ⟨j, b⟩) = 0
      ∧ V.globalMatrix (Sum.inl ⟨i, a⟩) (Sum.inr ⟨j, d⟩) = 0
      ∧ V.globalMatrix (Sum.inr ⟨i, c⟩) (Sum.inl ⟨j, b⟩) = 0
      ∧ V.globalMatrix (Sum.inr ⟨i, c⟩) (Sum.inr ⟨j, d⟩) = V.offDiag i j c d :=
  ⟨blockDiagonal'_apply_ne _ a b h, blockDiagonal'_apply_ne _ a d h,
    blockDiagonal'_apply_ne _ c b h, rfl⟩

omit [∀ i, DecidableEq (P i)] [∀ i, DecidableEq (Q i)] in
/-- **(14.11)**: the two rows of the global system that are local to subdomain `i`, the interior
one `B_i x_i + E_i y_i` and the interface one `F_i x_i + C_i y_i + ∑_{j ≠ i} E_ij y_j`. -/
theorem equation_14_11 (z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) (i : ι) :
    ((V.globalMatrix *ᵥ z) ∘ Sum.inl) ∘ Sigma.mk i
        = V.B i *ᵥ ((z ∘ Sum.inl) ∘ Sigma.mk i) + V.E i *ᵥ ((z ∘ Sum.inr) ∘ Sigma.mk i)
      ∧ ((V.globalMatrix *ᵥ z) ∘ Sum.inr) ∘ Sigma.mk i
        = V.F i *ᵥ ((z ∘ Sum.inl) ∘ Sigma.mk i) + V.localC i *ᵥ ((z ∘ Sum.inr) ∘ Sigma.mk i)
          + ∑ j ∈ Finset.univ.erase i, V.offDiag i j *ᵥ ((z ∘ Sum.inr) ∘ Sigma.mk j) := by
  constructor
  · rw [globalMatrix, comp_inl_fromBlocks_mulVec]
    change (blockDiagonal' V.B *ᵥ (z ∘ Sum.inl)) ∘ Sigma.mk i
        + (blockDiagonal' V.E *ᵥ (z ∘ Sum.inr)) ∘ Sigma.mk i = _
    rw [blockDiagonal'_comp_mulVec, blockDiagonal'_comp_mulVec]
  · rw [globalMatrix, comp_inr_fromBlocks_mulVec]
    change (blockDiagonal' V.F *ᵥ (z ∘ Sum.inl)) ∘ Sigma.mk i
        + (V.C *ᵥ (z ∘ Sum.inr)) ∘ Sigma.mk i = _
    rw [blockDiagonal'_comp_mulVec, comp_mulVec_sigma,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_assoc]
    rfl

omit [∀ i, DecidableEq (Q i)] in
/-- **(14.12)**: the block row of the Schur complement system at subdomain `i`,
`S_i y_i + ∑_{j ≠ i} E_ij y_j`. -/
theorem equation_14_12 (y : ((i : ι) × Q i) → 𝕜) (i : ι) :
    (V.schurMatrix *ᵥ y) ∘ Sigma.mk i
      = V.localSchur i *ᵥ (y ∘ Sigma.mk i)
        + ∑ j ∈ Finset.univ.erase i, V.offDiag i j *ᵥ (y ∘ Sigma.mk j) := by
  rw [comp_mulVec_sigma, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  refine congrArg₂ _ ?_ (Finset.sum_congr rfl fun j hj => ?_) <;> refine congrArg₂ _ ?_ rfl <;>
    ext a b
  · rw [Matrix.submatrix_apply, schurMatrix, Matrix.sub_apply, blockDiagonal'_apply_eq]
    rfl
  · rw [Matrix.submatrix_apply, schurMatrix, Matrix.sub_apply,
      blockDiagonal'_apply_ne _ a b (Ne.symm (Finset.ne_of_mem_erase hj)), sub_zero]
    rfl

/-! #### The two block Gauss–Seidel sweeps -/

omit [Fintype ι] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] in
/-- `D`, the block diagonal part of the global matrix for the subdomain blocks: the block diagonal
of the local matrices `A_i`. -/
theorem blockDiagPart_globalMatrix :
    blockDiagPart (nodeLabel P Q) V.globalMatrix
      = fromBlocks (blockDiagonal' V.B) (blockDiagonal' V.E) (blockDiagonal' V.F)
          (blockDiagPart Sigma.fst V.C) := by
  ext p q
  rcases p with ⟨i, a⟩ | ⟨i, a⟩ <;> rcases q with ⟨j, b⟩ | ⟨j, b⟩ <;>
    simp only [globalMatrix, blockDiagPart_apply, nodeLabel_inl, nodeLabel_inr,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  · exact ite_blockDiagonal' V.B a b
  · exact ite_blockDiagonal' V.E a b
  · exact ite_blockDiagonal' V.F a b
  · rfl

/-- `D - E`, the block-lower factor of the global matrix for the subdomain blocks; one block
Gauss–Seidel sweep over the subdomains solves with it. -/
def globalLower : Matrix (((i : ι) × P i) ⊕ ((i : ι) × Q i))
    (((i : ι) × P i) ⊕ ((i : ι) × Q i)) 𝕜 :=
  blockDiagPart (nodeLabel P Q) V.globalMatrix + blockStrictLower (nodeLabel P Q) V.globalMatrix

/-- `D - E`, the block-lower factor of the Schur complement system (14.14) for the subdomain
blocks. -/
noncomputable def schurLower : Matrix ((i : ι) × Q i) ((i : ι) × Q i) 𝕜 :=
  blockDiagPart Sigma.fst V.schurMatrix + blockStrictLower Sigma.fst V.schurMatrix

omit [Fintype ι] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] in
/-- The block-lower factor of the global matrix differs from the global matrix in the
interface–interface corner alone: the interior rows and columns of (14.8) already are block
diagonal, so the sweep does not touch them. -/
theorem globalLower_eq :
    V.globalLower = fromBlocks (blockDiagonal' V.B) (blockDiagonal' V.E) (blockDiagonal' V.F)
      (blockDiagPart Sigma.fst V.C + blockStrictLower Sigma.fst V.C) := by
  ext p q
  rcases p with ⟨i, a⟩ | ⟨i, a⟩ <;> rcases q with ⟨j, b⟩ | ⟨j, b⟩ <;>
    simp only [globalLower, globalMatrix, Matrix.add_apply, blockDiagPart_apply,
      blockStrictLower_apply, nodeLabel_inl, nodeLabel_inr, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  · exact ite_add_ite_blockDiagonal' V.B a b
  · exact ite_add_ite_blockDiagonal' V.E a b
  · exact ite_add_ite_blockDiagonal' V.F a b
  · rfl

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **The key identity**: the Schur complement of the block-lower factor of the global matrix is
the block-lower factor of the Schur complement system.  Eliminating the interior variables and
taking the block-lower triangle commute, which is why a Schwarz sweep on (14.8) and a Gauss–Seidel
sweep on (14.14) are the same iteration. -/
theorem schurComplement_globalLower (hB : ∀ i, IsUnit (V.B i)) :
    V.globalLower.schurComplement = V.schurLower := by
  rw [globalLower_eq, V.schurComplement_fromBlocks_local hB, schurLower, schurMatrix,
    blockDiagPart_sub_blockDiagonal', blockStrictLower_sub_blockDiagonal']
  abel

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- The same identity for the block diagonal alone. -/
theorem schurComplement_blockDiagPart_globalMatrix (hB : ∀ i, IsUnit (V.B i)) :
    (blockDiagPart (nodeLabel P Q) V.globalMatrix).schurComplement
      = blockDiagPart Sigma.fst V.schurMatrix := by
  rw [blockDiagPart_globalMatrix, V.schurComplement_fromBlocks_local hB, schurMatrix,
    blockDiagPart_sub_blockDiagonal']

/-- **(14.12)**, right-hand side: `g_i - F_i B_i⁻¹ f_i`, assembled over the subdomains. -/
noncomputable def reducedRhs (b : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) :
    ((i : ι) × Q i) → 𝕜 :=
  b ∘ Sum.inr - (blockDiagonal' V.F * (blockDiagonal' V.B)⁻¹) *ᵥ (b ∘ Sum.inl)

/-- **(14.22)**: an initial guess is *consistent* when its interior part solves the interior
equations of (14.11) exactly, `B_i x_i + E_i y_i = f_i`; equivalently the interior components of
the global residual vanish. -/
def IsConsistent (b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) : Prop :=
  (V.globalMatrix *ᵥ z) ∘ Sum.inl = b ∘ Sum.inl

/-- **Algorithm 14.3**, the multiplicative Schwarz sweep of §14.3.1 in matrix form: one block
Gauss–Seidel sweep on the global matrix, the blocks being the subdomains.  Solving `A_i δ_i = r_i`
in turn, each from the residual the previous solve left behind, accumulates a correction that
solves the block-lower system `(D - E) δ = b - A z`; this is
`Matrix.blockGaussSeidelSplitting_step_eq_multiplicativeStep`. -/
noncomputable def schwarzSweep (b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) :
    (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜 :=
  z + V.globalLower⁻¹ *ᵥ (b - V.globalMatrix *ᵥ z)

/-- One block Gauss–Seidel sweep on the Schur complement system (14.12), the blocks being the
interface unknowns `y_i` of the subdomains. -/
noncomputable def schurGaussSeidelSweep (g y : ((i : ι) × Q i) → 𝕜) : ((i : ι) × Q i) → 𝕜 :=
  y + V.schurLower⁻¹ *ᵥ (g - V.schurMatrix *ᵥ y)

/-- The sweep of Algorithm 14.3 is the step of the block Gauss–Seidel splitting of the global
matrix for the subdomain labelling. -/
theorem globalLower_eq_blockGaussSeidelSplitting
    (h : IsUnit (blockDiagPart (nodeLabel P Q) V.globalMatrix)) :
    V.globalLower = (blockGaussSeidelSplitting (nodeLabel P Q) V.globalMatrix h).m := rfl

/-- The sweep on (14.12) is the step of the block Gauss–Seidel splitting of the Schur complement
system for the subdomain labelling. -/
theorem schurLower_eq_blockGaussSeidelSplitting
    (h : IsUnit (blockDiagPart Sigma.fst V.schurMatrix)) :
    V.schurLower = (blockGaussSeidelSplitting Sigma.fst V.schurMatrix h).m := rfl

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **(14.12)**, right-hand side, read on subdomain `i`. -/
theorem reducedRhs_comp (hB : ∀ i, IsUnit (V.B i))
    (b : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) (i : ι) :
    V.reducedRhs b ∘ Sigma.mk i
      = (b ∘ Sum.inr) ∘ Sigma.mk i - (V.F i * (V.B i)⁻¹) *ᵥ ((b ∘ Sum.inl) ∘ Sigma.mk i) := by
  have h : blockDiagonal' V.F * (blockDiagonal' V.B)⁻¹
      = blockDiagonal' fun i => V.F i * (V.B i)⁻¹ := by
    rw [inv_blockDiagonal' V.B hB, blockDiagonal'_mul]
  rw [reducedRhs, h]
  change (b ∘ Sum.inr) ∘ Sigma.mk i
      - (blockDiagonal' (fun i => V.F i * (V.B i)⁻¹) *ᵥ (b ∘ Sum.inl)) ∘ Sigma.mk i = _
  rw [blockDiagonal'_comp_mulVec]

omit [∀ i, DecidableEq (P i)] [∀ i, DecidableEq (Q i)] in
/-- Consistency is the first line of (14.11) holding on every subdomain. -/
theorem isConsistent_iff_local (b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) :
    V.IsConsistent b z ↔ ∀ i, V.B i *ᵥ ((z ∘ Sum.inl) ∘ Sigma.mk i)
        + V.E i *ᵥ ((z ∘ Sum.inr) ∘ Sigma.mk i) = (b ∘ Sum.inl) ∘ Sigma.mk i := by
  constructor
  · intro h i
    rw [← (V.equation_14_11 z i).1, h]
  · intro h
    funext p
    obtain ⟨i, a⟩ := p
    exact congrFun (((V.equation_14_11 z i).1).trans (h i)) a

omit [∀ i, DecidableEq (Q i)] in
/-- **(14.22)**: consistency says exactly that `x_i^(0) = B_i⁻¹ (f_i - E_i y_i^(0))` on every
subdomain, which is the hypothesis of Theorem 14.2. -/
theorem isConsistent_iff (hB : ∀ i, IsUnit (V.B i))
    (b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) :
    V.IsConsistent b z ↔ ∀ i, (z ∘ Sum.inl) ∘ Sigma.mk i
      = (V.B i)⁻¹ *ᵥ ((b ∘ Sum.inl) ∘ Sigma.mk i - V.E i *ᵥ ((z ∘ Sum.inr) ∘ Sigma.mk i)) := by
  rw [isConsistent_iff_local V b z]
  exact forall_congr' fun i => mulVec_add_eq_iff (hB i) _ _ _

/-! #### Theorem 14.2 -/

/-- The Schur complement system is nonsingular in the block-lower triangle as soon as every local
Schur complement `S_i` is. -/
theorem isUnit_schurLower (hS : ∀ i, IsUnit (V.localSchur i)) : IsUnit V.schurLower :=
  isUnit_blockDiagPart_add_blockStrictLower
    (by rw [blockDiagPart_schurMatrix]; exact isUnit_blockDiagonal' _ hS)

/-- The block-lower factor of the global matrix is nonsingular as soon as every `B_i` and every
local Schur complement `S_i` is: this is Proposition 14.1 (1) applied to it. -/
theorem isUnit_globalLower (hB : ∀ i, IsUnit (V.B i)) (hS : ∀ i, IsUnit (V.localSchur i)) :
    IsUnit V.globalLower := by
  refine isUnit_of_isUnit_schurComplement ?_ ?_
  · rw [globalLower_eq, toBlocks_fromBlocks₁₁]
    exact isUnit_blockDiagonal' _ hB
  · rw [schurComplement_globalLower V hB]
    exact isUnit_schurLower V hS

/-- Every local matrix `A_i` is nonsingular as soon as every `B_i` and every `S_i` is, which is
what makes the subdomain solves of Algorithm 14.3 well posed. -/
theorem isUnit_blockDiagPart_globalMatrix (hB : ∀ i, IsUnit (V.B i))
    (hS : ∀ i, IsUnit (V.localSchur i)) :
    IsUnit (blockDiagPart (nodeLabel P Q) V.globalMatrix) := by
  refine isUnit_of_isUnit_schurComplement ?_ ?_
  · rw [blockDiagPart_globalMatrix, toBlocks_fromBlocks₁₁]
    exact isUnit_blockDiagonal' _ hB
  · rw [schurComplement_blockDiagPart_globalMatrix V hB, blockDiagPart_schurMatrix]
    exact isUnit_blockDiagonal' _ hS

omit [∀ i, DecidableEq (Q i)] in
/-- **The first half of the proof of Theorem 14.2**: for a consistent iterate the interface
components of the global residual are the residual of the Schur complement system (14.12) at the
same `y`.  Substituting `x_i = B_i⁻¹ (f_i - E_i y_i)` into `g_i - F_i x_i - C_i y_i - ∑ E_ij y_j`
turns `C_i` into `S_i` and `g_i` into `g_i - F_i B_i⁻¹ f_i`. -/
theorem residual_comp_inr (hB : ∀ i, IsUnit (V.B i))
    {b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜} (hc : V.IsConsistent b z) :
    (b - V.globalMatrix *ᵥ z) ∘ Sum.inr
      = V.reducedRhs b - V.schurMatrix *ᵥ (z ∘ Sum.inr) := by
  have hBu : IsUnit (blockDiagonal' V.B) := isUnit_blockDiagonal' _ hB
  have hcons : blockDiagonal' V.B *ᵥ (z ∘ Sum.inl) + blockDiagonal' V.E *ᵥ (z ∘ Sum.inr)
      = b ∘ Sum.inl := by
    rw [← comp_inl_fromBlocks_mulVec]; exact hc
  have hFB : blockDiagonal' V.F * (blockDiagonal' V.B)⁻¹ * blockDiagonal' V.B
      = blockDiagonal' V.F := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hBu), Matrix.mul_one]
  have hFx : (blockDiagonal' V.F * (blockDiagonal' V.B)⁻¹) *ᵥ (b ∘ Sum.inl)
      = blockDiagonal' V.F *ᵥ (z ∘ Sum.inl)
        + (blockDiagonal' V.F * (blockDiagonal' V.B)⁻¹ * blockDiagonal' V.E) *ᵥ (z ∘ Sum.inr) := by
    rw [← hcons, mulVec_add, mulVec_mulVec, mulVec_mulVec, hFB]
  have hbd : blockDiagonal' (fun i => V.F i * (V.B i)⁻¹ * V.E i)
      = blockDiagonal' V.F * (blockDiagonal' V.B)⁻¹ * blockDiagonal' V.E := by
    rw [inv_blockDiagonal' V.B hB, blockDiagonal'_mul, blockDiagonal'_mul]
  have hsub : (b - V.globalMatrix *ᵥ z) ∘ Sum.inr
      = b ∘ Sum.inr - (V.globalMatrix *ᵥ z) ∘ Sum.inr := rfl
  rw [hsub, globalMatrix, comp_inr_fromBlocks_mulVec, reducedRhs, hFx, schurMatrix, hbd,
    Matrix.sub_mulVec]
  abel

/-- **The second half of the proof of Theorem 14.2**: one sweep of Algorithm 14.3 started from a
consistent iterate moves the interface unknowns exactly as one block Gauss–Seidel sweep on the
Schur complement system does.  With `r_{x,i} = 0` the subdomain solve `A_i δ_i = (0, r_{y,i})`
returns `δ_{y,i} = S_i⁻¹ r_{y,i}` by (14.7); assembled over the subdomains that is the statement
that the `(2,2)` block of `(D - E)⁻¹` is the inverse of the Schur complement of `D - E`. -/
theorem comp_inr_schwarzSweep (hB : ∀ i, IsUnit (V.B i)) (hS : ∀ i, IsUnit (V.localSchur i))
    {b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜} (hc : V.IsConsistent b z) :
    (V.schwarzSweep b z) ∘ Sum.inr
      = V.schurGaussSeidelSweep (V.reducedRhs b) (z ∘ Sum.inr) := by
  have hr : b - V.globalMatrix *ᵥ z
      = Sum.elim (0 : ((i : ι) × P i) → 𝕜) ((b - V.globalMatrix *ᵥ z) ∘ Sum.inr) := by
    funext p
    rcases p with p | p
    · exact sub_eq_zero.2 (congrFun hc p).symm
    · rfl
  have h11 : (V.globalLower).toBlocks₁₁ = blockDiagonal' V.B := by
    rw [globalLower_eq, toBlocks_fromBlocks₁₁]
  have hstep : (V.globalLower⁻¹ *ᵥ (b - V.globalMatrix *ᵥ z)) ∘ Sum.inr
      = V.schurLower⁻¹ *ᵥ ((b - V.globalMatrix *ᵥ z) ∘ Sum.inr) := by
    conv_lhs => rw [hr]
    rw [comp_inr_mulVec_elim_zero, toBlocks₂₂_inv_eq_inv_schurComplement
      (by rw [h11]; exact isUnit_blockDiagonal' _ hB) (isUnit_globalLower V hB hS),
      schurComplement_globalLower V hB]
  change z ∘ Sum.inr + (V.globalLower⁻¹ *ᵥ (b - V.globalMatrix *ᵥ z)) ∘ Sum.inr = _
  rw [hstep, residual_comp_inr V hB hc, schurGaussSeidelSweep]

/-- **Consistency is an invariant of Algorithm 14.3**: the sweep changes the residual only in its
interface components, since the interior rows of the global matrix and of its block-lower factor
agree.  This is Saad's "because only the `y` components of the residual vector are modified, this
property remains valid throughout the iterative process". -/
theorem isConsistent_schwarzSweep (hB : ∀ i, IsUnit (V.B i)) (hS : ∀ i, IsUnit (V.localSchur i))
    {b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜} (hc : V.IsConsistent b z) :
    V.IsConsistent b (V.schwarzSweep b z) := by
  set d := V.globalLower⁻¹ *ᵥ (b - V.globalMatrix *ᵥ z) with hd
  have hLd : V.globalLower *ᵥ d = b - V.globalMatrix *ᵥ z := by
    rw [hd, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1
      (isUnit_globalLower V hB hS)), one_mulVec]
  have hAd : (V.globalMatrix *ᵥ d) ∘ Sum.inl = (V.globalLower *ᵥ d) ∘ Sum.inl := by
    rw [globalMatrix, comp_inl_fromBlocks_mulVec, globalLower_eq, comp_inl_fromBlocks_mulVec]
  have hr0 : (b - V.globalMatrix *ᵥ z) ∘ Sum.inl = 0 := by
    funext p
    exact sub_eq_zero.2 (congrFun hc p).symm
  change (V.globalMatrix *ᵥ (z + d)) ∘ Sum.inl = b ∘ Sum.inl
  rw [mulVec_add]
  change (V.globalMatrix *ᵥ z) ∘ Sum.inl + (V.globalMatrix *ᵥ d) ∘ Sum.inl = b ∘ Sum.inl
  rw [hAd, hLd, hr0, hc, add_zero]

end VertexPartitioning

/-- **Theorem 14.2** (Chan and Goovaerts): if the initial guess of the multiplicative Schwarz
procedure is consistent, that is `x_i^(0) = B_i⁻¹ (f_i - E_i y_i^(0))` of (14.22), then the `y`
iterates produced by Algorithm 14.3 are identical to those of a Gauss–Seidel sweep applied to the
Schur complement system (14.12).

Both hypotheses are the nonsingularity that makes the two iterations defined: every `B_i` so that
the interior variables can be eliminated, and every local Schur complement `S_i` so that the
diagonal blocks of (14.14) can be solved with. -/
theorem theorem_14_2 (hB : ∀ i, IsUnit (V.B i)) (hS : ∀ i, IsUnit (V.localSchur i))
    {b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜} (hc : V.IsConsistent b z) (k : ℕ) :
    ((V.schwarzSweep b)^[k] z) ∘ Sum.inr
      = (V.schurGaussSeidelSweep (V.reducedRhs b))^[k] (z ∘ Sum.inr) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ← V.comp_inr_schwarzSweep hB hS hc]
    exact ih (V.isConsistent_schwarzSweep hB hS hc)

end VertexBased

variable {n : ℕ}

/-! ### §14.3.1: the restriction matrices and the subdomain spaces -/

/-- §14.3.1: the boolean restriction matrix `R_S` of an index set `S ⊆ {1, …, n}`, whose rows are
the `e_jᵀ` for `j ∈ S`.  `R_S x` is the sub-vector of `x` indexed by `S`, and `R_Sᵀ y` extends a
vector on `S` by zero. -/
def restrictSubset (𝕜 : Type*) [RCLike 𝕜] (S : Finset (Fin n)) : Matrix ↥S (Fin n) 𝕜 :=
  Matrix.of fun i j => if (i : Fin n) = j then 1 else 0

/-- §14.3.1: the subspace `Ran(R_Sᵀ) = span {e_j : j ∈ S}` of the vectors supported on `S`, on
which the subdomain problem of the Schwarz procedure is solved. -/
def subdomainSpace (𝕜 : Type*) [RCLike 𝕜] (S : Finset (Fin n)) :
    Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  Submodule.span 𝕜 (Set.range fun j : ↥S => EuclideanSpace.single (j : Fin n) (1 : 𝕜))

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The entries of `R_S`, read off its definition. -/
theorem restrictSubset_apply (S : Finset (Fin n)) (i : ↥S) (j : Fin n) :
    restrictSubset 𝕜 S i j = if (i : Fin n) = j then 1 else 0 := rfl

/-- The rows of `R_S` are orthonormal: `R_S R_Sᵀ = I`.  In particular `R_Sᵀ` has full column
rank, which is what makes the local matrix `A_S` nonsingular. -/
theorem restrictSubset_mul_transpose (S : Finset (Fin n)) :
    restrictSubset 𝕜 S * (restrictSubset 𝕜 S)ᵀ = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [restrictSubset_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (i : Fin n)]
  · have h : ((k : Fin n) = (i : Fin n)) ↔ i = k := by
      rw [Subtype.ext_iff]; exact eq_comm
    simp [h]
  · exact fun j _ hj => by rw [ite_eq_right (Ne.symm hj), zero_mul]
  · exact fun h => absurd (Finset.mem_univ (i : Fin n)) h

/-- The entries of `R_S` are `0` and `1`, so its conjugate transpose is its transpose: the
adjoint of the extension `R_Sᵀ` is the restriction `R_S`. -/
theorem conjTranspose_transpose_restrictSubset (S : Finset (Fin n)) :
    ((restrictSubset 𝕜 S)ᵀ)ᴴ = restrictSubset 𝕜 S := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  simp only [restrictSubset_apply]
  split_ifs <;> simp

/-- **Saad §14.3.1**: the range of the extension `R_Sᵀ` is the span of the coordinate vectors of
`S`.  This is the subspace on which the local problem is posed. -/
theorem range_restrictSubset_transpose (S : Finset (Fin n)) :
    LinearMap.range (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) = subdomainSpace 𝕜 S := by
  have hbasis : (⊤ : Submodule 𝕜 (EuclideanSpace 𝕜 ↥S))
      = Submodule.span 𝕜 (Set.range fun j : ↥S => EuclideanSpace.single j (1 : 𝕜)) := by
    have h := (EuclideanSpace.basisFun (ι := ↥S) (𝕜 := 𝕜)).toBasis.span_eq
    rw [← h]
    congr 1
    exact congrArg Set.range (funext fun j => by
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply])
  have happ : ∀ j : ↥S, Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ
      (EuclideanSpace.single j (1 : 𝕜)) = EuclideanSpace.single (j : Fin n) (1 : 𝕜) := by
    intro j
    have hcol : (restrictSubset 𝕜 S)ᵀ *ᵥ Pi.single j (1 : 𝕜)
        = Pi.single (j : Fin n) (1 : 𝕜) := by
      rw [Matrix.mulVec_single_one]
      funext k
      rw [Matrix.col_apply, Matrix.transpose_apply, restrictSubset_apply, Pi.single_apply]
      by_cases h : (j : Fin n) = k
      · simp [h]
      · simp [h, Ne.symm h]
    rw [Matrix.toLpLin_apply, PiLp.ofLp_single, hcol, PiLp.toLp_single]
  rw [LinearMap.range_eq_map, hbasis, Submodule.map_span, ← Set.range_comp, subdomainSpace]
  exact congrArg _ (congrArg Set.range (funext happ))

/-! ### §14.3.1: the local matrices and the subdomain projectors -/

variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- §14.3.1: the local matrix `A_S = R_S A R_Sᵀ` of the subdomain `S`, the submatrix of `A` on
the rows and columns of `S`. -/
def localMatrix (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) : Matrix ↥S ↥S 𝕜 :=
  restrictSubset 𝕜 S * A * (restrictSubset 𝕜 S)ᵀ

/-- (14.31): the subdomain solve `T_S = R_Sᵀ A_S⁻¹ R_S`, which restricts a residual to `S`,
solves the local system there, and extends the correction by zero. -/
noncomputable def subdomainInverse (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  (restrictSubset 𝕜 S)ᵀ * (localMatrix A S)⁻¹ * restrictSubset 𝕜 S

/-- (14.24): the subdomain projector `P_S = R_Sᵀ A_S⁻¹ R_S A = T_S A`. -/
noncomputable def subdomainProjector (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  subdomainInverse A S * A

/-- (14.24) and (14.31): `P_S = T_S A`. -/
theorem subdomainProjector_eq_mul (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    subdomainProjector A S = subdomainInverse A S * A := rfl

/-- `(I - M) z = z - M z`: unfolding a projector complement one application at a time, which is
what every error recurrence of the section needs. -/
theorem toEuclideanLin_one_sub_apply (M : Matrix (Fin n) (Fin n) 𝕜)
    (z : EuclideanSpace 𝕜 (Fin n)) : ((1 - M) ⬝ z) = z - (M ⬝ z) := by
  have hmat : Matrix.toEuclideanLin (1 - M)
      = (LinearMap.id : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
        - Matrix.toEuclideanLin M := by
    rw [map_sub, Matrix.toLpLin_one]
  rw [hmat, LinearMap.sub_apply, LinearMap.id_apply]

/-- A symmetric positive definite matrix is a symmetric coercive operator; this is the hypothesis
under which the energy inner product `(x, y)_A` of §14.3.4 exists. -/
theorem isSymmetricCoercive_toEuclideanLin (hA : A.PosDef) :
    (Matrix.toEuclideanLin A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 hA

/-- The adjoint of the extension `R_Sᵀ` is the restriction `R_S`. -/
theorem adjoint_toEuclideanLin_transpose (S : Finset (Fin n)) :
    LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      = Matrix.toEuclideanLin (restrictSubset 𝕜 S) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_transpose_restrictSubset]

/-- The extension `R_Sᵀ` is injective, since `R_S R_Sᵀ = I`. -/
theorem injective_toEuclideanLin_transpose (S : Finset (Fin n)) :
    Function.Injective (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) := by
  have h : Matrix.toEuclideanLin (restrictSubset 𝕜 S) ∘ₗ
      Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ = LinearMap.id := by
    rw [← Matrix.toLpLin_mul_same, restrictSubset_mul_transpose, Matrix.toLpLin_one]
  exact Function.LeftInverse.injective (g := Matrix.toEuclideanLin (restrictSubset 𝕜 S))
    fun x => DFunLike.congr_fun h x

/-- The local matrix `A_S = R_S A R_Sᵀ` is the Galerkin coarse operator of the extension `R_Sᵀ`:
this is the sentence that makes the whole section a specialization of the abstract theory. -/
theorem galerkinCoarse_eq (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
        (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      = Matrix.toEuclideanLin (localMatrix A S) := by
  have hdef : Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
      (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
        = LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) ∘ₗ
            Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ := rfl
  rw [hdef, adjoint_toEuclideanLin_transpose, localMatrix, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_mul_same, LinearMap.comp_assoc]

/-- **The local problem is well posed**: for symmetric positive definite `A` the local matrix
`A_S` is symmetric positive definite, so `A_S⁻¹` in (14.24) makes sense. -/
theorem posDef_localMatrix (hA : A.PosDef) (S : Finset (Fin n)) : (localMatrix A S).PosDef := by
  rw [Matrix.posDef_iff_isSymmetricCoercive, ← galerkinCoarse_eq]
  exact Multigrid.galerkinCoarse_isSymmetricCoercive (isSymmetricCoercive_toEuclideanLin hA)
    (injective_toEuclideanLin_transpose S)

/-- The subspace argument of `Schwarz.energyProjection` may be rewritten. -/
private theorem energyProjection_congr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetricCoercive)
    {K L : Submodule 𝕜 E} [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L] (h : K = L) :
    Schwarz.energyProjection T hT K = Schwarz.energyProjection T hT L := by
  subst h; rfl

/-- **Saad (14.24)**: the subdomain projector `P_S = R_Sᵀ A_S⁻¹ R_S A` is the `A`-orthogonal
projector onto the subdomain space `span {e_j : j ∈ S}`.  Every statement of §14.3 follows from
this identification and the abstract Schwarz theory. -/
theorem subdomainProjector_eq_energyProjection (hA : A.PosDef) (S : Finset (Fin n)) :
    Matrix.toEuclideanLin (subdomainProjector A S)
      = Schwarz.energyProjection (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S) := by
  have hinv : localMatrix A S * (localMatrix A S)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (posDef_localMatrix hA S).isUnit)
  refine LinearMap.ext fun x => ?_
  have hy : Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
      (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      (Matrix.toEuclideanLin ((localMatrix A S)⁻¹ * restrictSubset 𝕜 S * A) x)
        = LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
            (Matrix.toEuclideanLin A x) := by
    rw [galerkinCoarse_eq, adjoint_toEuclideanLin_transpose, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul,
      Matrix.toLpLin_mul_same]
    rfl
  have hproj := Schwarz.energyProjection_eq_of_galerkinCoarse (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA) (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) hy
  rw [energyProjection_congr (isSymmetricCoercive_toEuclideanLin hA)
    (range_restrictSubset_transpose (𝕜 := 𝕜) S).symm, hproj, ← LinearMap.comp_apply,
    ← Matrix.toLpLin_mul_same]
  rw [subdomainProjector, subdomainInverse, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/-- Saad's computation that `P_S² = P_S`: the subdomain projector is idempotent. -/
theorem subdomainProjector_mul_self (hA : A.PosDef) (S : Finset (Fin n)) :
    subdomainProjector A S * subdomainProjector A S = subdomainProjector A S := by
  refine (Matrix.toEuclideanLin (𝕜 := 𝕜)).injective ?_
  rw [Matrix.toLpLin_mul_same, subdomainProjector_eq_energyProjection hA S]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact Schwarz.energyProjection_apply_of_mem (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S)
    (Schwarz.energyProjection_apply_mem (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S) x)

/-! ### §14.3.2–14.3.3: the multiplicative and additive procedures -/

section Procedures

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **(14.25)**, the multiplicative Schwarz procedure: sweeping over the subdomains
`S 0, …, S (i-1)` in order, each correction `x ← x + R_jᵀ A_j⁻¹ R_j (b - A x)` being computed
from the iterate the previous one produced. -/
noncomputable def multiplicativeSweep (b : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → EuclideanSpace 𝕜 (Fin n) → EuclideanSpace 𝕜 (Fin n)
  | 0, x => x
  | i + 1, x => multiplicativeSweep b i x +
      (subdomainInverse A (S i) ⬝ (b - (A ⬝ multiplicativeSweep b i x)))

/-- A sweep over no subdomains changes nothing. -/
@[simp]
theorem multiplicativeSweep_zero (b x : EuclideanSpace 𝕜 (Fin n)) :
    multiplicativeSweep A S b 0 x = x := rfl

/-- One more subdomain adds one more correction, computed from the current iterate. -/
theorem multiplicativeSweep_succ (b : EuclideanSpace 𝕜 (Fin n)) (i : ℕ)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    multiplicativeSweep A S b (i + 1) x = multiplicativeSweep A S b i x +
      (subdomainInverse A (S i) ⬝ (b - (A ⬝ multiplicativeSweep A S b i x))) := rfl

/-- **§14.3.3**, the additive Schwarz procedure: all `s` corrections are computed from the same
iterate and added at once, `x ← x + ∑_{i<s} T_i (b - A x)`. -/
noncomputable def additiveSweep (s : ℕ) (b x : EuclideanSpace 𝕜 (Fin n)) :
    EuclideanSpace 𝕜 (Fin n) :=
  x + ∑ i ∈ Finset.range s, (subdomainInverse A (S i) ⬝ (b - (A ⬝ x)))

/-- **(14.26)**: the error propagation operator `Q_s = (I - P_{s-1}) ⋯ (I - P_0)` of one
multiplicative Schwarz sweep. -/
noncomputable def Q_s : ℕ → Matrix (Fin n) (Fin n) 𝕜
  | 0 => 1
  | i + 1 => (1 - subdomainProjector A (S i)) * Q_s i

/-- A sweep over no subdomains propagates the error unchanged. -/
@[simp]
theorem Q_s_zero : Q_s A S 0 = 1 := rfl

/-- One more subdomain composes one more factor `1 - P_i` on the left. -/
theorem Q_s_succ (i : ℕ) :
    Q_s A S (i + 1) = (1 - subdomainProjector A (S i)) * Q_s A S i := rfl

/-- **(14.37)**: the additive Schwarz operator `A_J = ∑_{i<s} P_i`. -/
noncomputable def A_J (s : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  ∑ i ∈ Finset.range s, subdomainProjector A (S i)

/-- The additive Schwarz preconditioner `M⁻¹ = ∑ T_i` satisfies `M⁻¹ A = A_J`. -/
theorem sum_subdomainInverse_mul (s : ℕ) :
    (∑ i ∈ Finset.range s, subdomainInverse A (S i)) * A = A_J A S s := by
  rw [A_J, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (subdomainProjector_eq_mul A (S i)).symm

/-- **(14.26)**: `Q_s` is the error propagation operator of the multiplicative sweep — sweeping
over `S 0, …, S (s-1)` multiplies the error by `Q_s`.  No hypothesis on `A` is needed: this is
the algebra of the corrections, not their optimality. -/
theorem error_multiplicativeSweep {b xstar : EuclideanSpace 𝕜 (Fin n)}
    (hstar : (A ⬝ xstar) = b) (s : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    xstar - multiplicativeSweep A S b s x = (Q_s A S s ⬝ (xstar - x)) := by
  induction s with
  | zero => rw [multiplicativeSweep_zero, Q_s_zero, Matrix.toLpLin_one, LinearMap.id_apply]
  | succ i ih =>
      have hz : b - (A ⬝ multiplicativeSweep A S b i x)
          = (A ⬝ (xstar - multiplicativeSweep A S b i x)) := by rw [map_sub, hstar]
      have hstep : xstar - multiplicativeSweep A S b (i + 1) x
          = ((1 - subdomainProjector A (S i)) ⬝
              (xstar - multiplicativeSweep A S b i x)) := by
        rw [multiplicativeSweep_succ, hz, toEuclideanLin_one_sub_apply,
          subdomainProjector_eq_mul, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
        abel
      rw [hstep, ih, Q_s_succ, Matrix.toLpLin_mul_same, LinearMap.comp_apply]

/-- **Proposition 14.3**: one multiplicative Schwarz sweep is one step of the fixed-point
iteration `x ← x + M⁻¹(b - A x)` for the preconditioned system, with `M⁻¹ = (I - Q_s) A⁻¹`
(14.28) and hence `M⁻¹ A = I - Q_s` (14.27); and one additive Schwarz step is the same iteration
with `M⁻¹ = ∑ T_i`, whose preconditioned operator `M⁻¹ A` is the additive Schwarz operator
`A_J` of (14.37). -/
theorem proposition_14_3 (hA : A.PosDef) {b xstar : EuclideanSpace 𝕜 (Fin n)}
    (hstar : (A ⬝ xstar) = b) (s : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    multiplicativeSweep A S b s x = x + (((1 - Q_s A S s) * A⁻¹) ⬝ (b - (A ⬝ x)))
      ∧ additiveSweep A S s b x
          = x + ((∑ i ∈ Finset.range s, subdomainInverse A (S i)) ⬝ (b - (A ⬝ x)))
      ∧ (∑ i ∈ Finset.range s, subdomainInverse A (S i)) * A = A_J A S s := by
  have hinv : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit)
  refine ⟨?_, ?_, sum_subdomainInverse_mul A S s⟩
  · have herr := error_multiplicativeSweep A S hstar s x
    have hres : b - (A ⬝ x) = (A ⬝ (xstar - x)) := by rw [map_sub, hstar]
    rw [hres, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, mul_assoc, hinv, mul_one,
      toEuclideanLin_one_sub_apply, ← herr]
    abel
  · rw [additiveSweep, map_sum, LinearMap.sum_apply]

end Procedures

/-! ### §14.3.2: Lemma 14.4, the recurrences of Algorithms 14.4 and 14.5 -/

section Lemma144

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **(14.35)**: what a multiplicative sweep adds to the iterate is `∑_{i<s} P_i Q_i`. -/
theorem one_sub_Q_s_eq_sum (s : ℕ) :
    1 - Q_s A S s = ∑ j ∈ Finset.range s, subdomainProjector A (S j) * Q_s A S j := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Q_s_succ, Finset.sum_range_succ, ← ih]
      noncomm_ring

/-- **Lemma 14.4**: with `Z_i = I - Q_i`, `M_i = Z_i A⁻¹` and `T_i = R_iᵀ A_i⁻¹ R_i`, the
recurrences `Z_{i+1} = Z_i + P_i (I - Z_i)` of (14.32) and `M_{i+1} = M_i + T_i (I - A M_i)` of
(14.33), together with the expansion (14.35) `I - Q_s = ∑_{j<s} P_j Q_{j}`.  The second
recurrence is Algorithm 14.5: it applies `M⁻¹` without ever forming `A⁻¹`. -/
theorem lemma_14_4 (hA : A.PosDef) (i s : ℕ) :
    1 - Q_s A S (i + 1)
        = (1 - Q_s A S i) + subdomainProjector A (S i) * (1 - (1 - Q_s A S i))
      ∧ (1 - Q_s A S (i + 1)) * A⁻¹
          = (1 - Q_s A S i) * A⁻¹
            + subdomainInverse A (S i) * (1 - A * ((1 - Q_s A S i) * A⁻¹))
      ∧ 1 - Q_s A S s = ∑ j ∈ Finset.range s, subdomainProjector A (S j) * Q_s A S j := by
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit)
  have hPA : subdomainProjector A (S i) * A⁻¹ = subdomainInverse A (S i) := by
    rw [subdomainProjector_eq_mul, mul_assoc, hAA, mul_one]
  have h1 : 1 - Q_s A S (i + 1)
      = (1 - Q_s A S i) + subdomainProjector A (S i) * (1 - (1 - Q_s A S i)) := by
    rw [Q_s_succ]; noncomm_ring
  refine ⟨h1, ?_, one_sub_Q_s_eq_sum A S s⟩
  calc (1 - Q_s A S (i + 1)) * A⁻¹
      = ((1 - Q_s A S i) + subdomainProjector A (S i) * (1 - (1 - Q_s A S i))) * A⁻¹ := by
        rw [h1]
    _ = (1 - Q_s A S i) * A⁻¹ + subdomainProjector A (S i) * A⁻¹
          - subdomainProjector A (S i) * ((1 - Q_s A S i) * A⁻¹) := by noncomm_ring
    _ = (1 - Q_s A S i) * A⁻¹ + subdomainInverse A (S i)
          - subdomainInverse A (S i) * (A * ((1 - Q_s A S i) * A⁻¹)) := by
        rw [hPA, subdomainProjector_eq_mul, mul_assoc]
    _ = (1 - Q_s A S i) * A⁻¹
          + subdomainInverse A (S i) * (1 - A * ((1 - Q_s A S i) * A⁻¹)) := by noncomm_ring

end Lemma144

/-! ### §14.3.4: the convergence theory -/

section Convergence

variable {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) (S : ℕ → Finset (Fin n))

include hA

/-- The energy space of `A`: the same vectors, carrying the inner product `(x, y)_A`. -/
private noncomputable abbrev energySpaceType : Type _ :=
  WithEnergy (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)

/-- The subdomain spaces read in the energy inner product, the family the abstract Schwarz
theory is stated over. -/
private noncomputable abbrev energySpace (i : ℕ) : Submodule 𝕜 (energySpaceType hA) :=
  WithEnergy.submoduleMap (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
    (subdomainSpace 𝕜 (S i))

private theorem energyNorm_eq_norm_equiv (x : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) x
      = ‖WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x‖ :=
  (WithEnergy.norm_equiv _ _ x).symm

/-- The bridge: `P_i` read in the energy space is the orthogonal projector onto `V_i`. -/
private theorem equiv_subdomainProjector (i : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    WithEnergy.equiv (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
        (subdomainProjector A (S i) ⬝ x)
      = (energySpace hA S i).starProjection (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x) := by
  rw [subdomainProjector_eq_energyProjection hA]
  exact Schwarz.equiv_energyProjection _ _ _ x

/-- The bridge: `Q_s` read in the energy space is `Schwarz.errorOp`. -/
private theorem equiv_Q_s (s : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    WithEnergy.equiv (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
        (Q_s A S s ⬝ x)
      = Schwarz.errorOp (energySpace hA S) s (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x) := by
  induction s with
  | zero =>
      rw [Q_s_zero, Matrix.toLpLin_one, LinearMap.id_apply, Schwarz.errorOp_zero]
      rfl
  | succ i ih =>
      rw [Q_s_succ, Matrix.toLpLin_mul_same, LinearMap.comp_apply, toEuclideanLin_one_sub_apply,
        map_sub, equiv_subdomainProjector hA S, ih, Schwarz.errorOp_succ_apply]

/-- The bridge: `A_J` read in the energy space is `Schwarz.additiveOperator`. -/
private theorem equiv_A_J (s : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    WithEnergy.equiv (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
        (A_J A S s ⬝ x)
      = Schwarz.additiveOperator (energySpace hA S) s (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x) := by
  have h : (A_J A S s ⬝ x) = ∑ i ∈ Finset.range s, (subdomainProjector A (S i) ⬝ x) := by
    rw [A_J, map_sum, LinearMap.sum_apply]
  rw [h, map_sum, Schwarz.additiveOperator_apply]
  exact Finset.sum_congr rfl fun i _ => equiv_subdomainProjector hA S i x

omit hA in
/-- Eigenvalues of a symmetric operator whose quadratic form lies in `[a, b]`. -/
private theorem re_mem_Icc_of_hasEigenvalue {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {T : H →ₗ[𝕜] H} {a b : ℝ} (hsym : T.IsSymmetric)
    (hlo : ∀ u, a * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T u) u))
    (hhi : ∀ u, RCLike.re (inner 𝕜 (T u) u) ≤ b * ‖u‖ ^ 2) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue T μ) : RCLike.re μ ∈ Set.Icc a b :=
  LinearMap.IsSymmetricBoundedBy.re_mem_Icc_of_hasEigenvalue ⟨hsym, hlo, hhi⟩ hμ

/-- An eigenvalue of `A_J` is an eigenvalue of the additive Schwarz operator of the energy
space: the two are conjugate by `WithEnergy.equiv`. -/
private theorem hasEigenvalue_additiveOperator (s : ℕ) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    Module.End.HasEigenvalue
      (Schwarz.additiveOperator (energySpace hA S) s : energySpaceType hA →ₗ[𝕜] _) μ := by
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := WithEnergy.equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA) x) ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
  · rw [ContinuousLinearMap.coe_coe, ← equiv_A_J hA S s x, hx, map_smul]
  · exact fun h => hx0 ((WithEnergy.equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA)).map_eq_zero_iff.1 h)

/-! #### Theorem 14.5 and Theorem 14.6: the largest eigenvalue of `A_J` -/

/-- **Theorem 14.5** in quadratic-form language: `(A_J u, u)_A ≤ s ‖u‖_A²`, since each `P_i` has
`A`-norm one. -/
theorem re_energyInner_A_J_le (s : ℕ) (u : EuclideanSpace 𝕜 (Fin n)) :
    RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u)
      ≤ s * energyNorm (Matrix.toEuclideanLin A) u ^ 2 := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, energyNorm_eq_norm_equiv hA]
  exact Schwarz.re_inner_additiveOperator_le (energySpace hA S) s _

/-- The additive Schwarz operator is positive semidefinite in the energy inner product. -/
theorem re_energyInner_A_J_nonneg (s : ℕ) (u : EuclideanSpace 𝕜 (Fin n)) :
    0 ≤ RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S]
  exact Schwarz.re_inner_additiveOperator_nonneg (energySpace hA S) s _

/-- **(14.37)**: the additive Schwarz operator is self-adjoint for the energy inner product, so
its eigenvalues are real. -/
theorem isSymmetric_energyInner_A_J (s : ℕ) (u v : EuclideanSpace 𝕜 (Fin n)) :
    energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) v
      = energyInner (Matrix.toEuclideanLin A) u (A_J A S s ⬝ v) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), ← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, equiv_A_J hA S]
  exact Schwarz.additiveOperator_isSymmetric (energySpace hA S) s _ _

/-- **Theorem 14.5**: `λ_max(A_J) ≤ s`, the number of subdomains. -/
theorem theorem_14_5 (s : ℕ) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    RCLike.re μ ≤ s :=
  (re_mem_Icc_of_hasEigenvalue (a := 0)
    (Schwarz.additiveOperator_isSymmetric (energySpace hA S) s)
    (fun u => by simpa using Schwarz.re_inner_additiveOperator_nonneg (energySpace hA S) s u)
    (fun u => Schwarz.re_inner_additiveOperator_le (energySpace hA S) s u)
    (hasEigenvalue_additiveOperator hA S s hμ)).2

/-- Two subdomains with no coupling in `A` span `A`-orthogonal subspaces. -/
private theorem isOrtho_energySpace {i j : ℕ}
    (h : ∀ k ∈ S i, ∀ l ∈ S j, A l k = 0) : energySpace hA S i ⟂ energySpace hA S j := by
  have hgen : ∀ m : ℕ, energySpace hA S m
      = Submodule.span 𝕜 (Set.range fun k : ↥(S m) => WithEnergy.equiv (Matrix.toEuclideanLin A)
            (isSymmetricCoercive_toEuclideanLin hA)
            (EuclideanSpace.single (k : Fin n) (1 : 𝕜))) := by
    intro m
    have h0 : energySpace hA S m = Submodule.map
        (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA)).toLinearMap
        (Submodule.span 𝕜 (Set.range fun k : ↥(S m) =>
          EuclideanSpace.single (k : Fin n) (1 : 𝕜))) := rfl
    rw [h0, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hgen i, hgen j, Submodule.isOrtho_span]
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  rw [WithEnergy.inner_equiv, energyInner]
  have hval : (Matrix.toEuclideanLin A (EuclideanSpace.single (k : Fin n) (1 : 𝕜)))
      = WithLp.toLp 2 (fun p => A p (k : Fin n)) := by
    rw [Matrix.toLpLin_apply, PiLp.ofLp_single, Matrix.mulVec_single_one]
    rfl
  rw [hval, EuclideanSpace.inner_single_right]
  simp [h (k : Fin n) k.2 (l : Fin n) l.2]

/-- **Theorem 14.6**: if the subdomains are coloured so that two subdomains of the same colour
have no coupling in `A` — no entry `A_{lk}` with `k` in one and `l` in the other, which for a
positive definite `A` forces them to be disjoint — then `λ_max(A_J) ≤ c`, the number of
colours.  Colouring the interaction graph of the subdomains therefore replaces the crude bound
of Theorem 14.5 by one that does not grow with the number of subdomains.

The book asks only that two subdomains of the same colour "have no common nodes", justifying
it by "`P_{Θ_i} = ∑_{j ∈ Θ_i} P_j` is again an orthogonal projector".  That step needs the
ranges to be `A`-orthogonal, which disjointness does not give.  A counterexample: `n = 2`,
`A = [[2, 1], [1, 2]]`, `S_0 = {0}` and `S_1 = {1}`, disjoint and therefore of one colour.
Then `P_0 = [[1, ½], [0, 0]]`, `P_1 = [[0, 0], [½, 1]]` and `A_J = [[1, ½], [½, 1]]`, whose
largest eigenvalue is `3/2 > 1 = c`.  The no-coupling hypothesis used here is what the proof
needs, and it is what a genuinely decoupled colouring provides. -/
theorem theorem_14_6 {κ : Type*} [Fintype κ] (s : ℕ) (col : ℕ → κ)
    (hcol : ∀ i ∈ Finset.range s, ∀ j ∈ Finset.range s, i ≠ j → col i = col j →
      ∀ k ∈ S i, ∀ l ∈ S j, A l k = 0)
    {μ : 𝕜} (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    RCLike.re μ ≤ Fintype.card κ :=
  (re_mem_Icc_of_hasEigenvalue (a := 0)
    (Schwarz.additiveOperator_isSymmetric (energySpace hA S) s)
    (fun u => by simpa using Schwarz.re_inner_additiveOperator_nonneg (energySpace hA S) s u)
    (fun u => Schwarz.re_inner_additiveOperator_le_of_coloring (energySpace hA S) s col
      (fun i hi j hj hij hc => isOrtho_energySpace hA S (hcol i hi j hj hij hc)) u)
    (hasEigenvalue_additiveOperator hA S s hμ)).2

/-! #### Assumptions 1 and 2 -/

end Convergence

section Assumptions

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **Assumption 1** of §14.3.4: every vector splits over the subdomain spaces with
`∑ (A u_i, u_i) ≤ K₀ (A u, u)`.  This is the hypothesis that the subdomains cover the domain
stably; for a finite-element family it is what an overlapping partition of unity provides. -/
def IsStableDecomposition (s : ℕ) (K₀ : ℝ) : Prop :=
  ∀ u : EuclideanSpace 𝕜 (Fin n), ∃ w : ℕ → EuclideanSpace 𝕜 (Fin n),
    (∀ i ∈ Finset.range s, w i ∈ subdomainSpace 𝕜 (S i)) ∧
      ∑ i ∈ Finset.range s, w i = u ∧
        ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A) (w i) ^ 2
          ≤ K₀ * energyNorm (Matrix.toEuclideanLin A) u ^ 2

/-- **Assumption 2** of §14.3.4, (14.40): a strengthened Cauchy–Schwarz inequality with constant
`K₁`, measuring how far the subdomain spaces are from being `A`-orthogonal.  Mutually
`A`-orthogonal subdomains admit `K₁ = 0`, and the plain Cauchy–Schwarz inequality always gives
`K₁ = s`. -/
def IsStrengthenedCauchySchwarz (s : ℕ) (K₁ : ℝ) : Prop :=
  ∀ ps : Finset (ℕ × ℕ), ps ⊆ Finset.range s ×ˢ Finset.range s →
    ∀ u v : ℕ → EuclideanSpace 𝕜 (Fin n),
      (∀ i, u i ∈ subdomainSpace 𝕜 (S i)) → (∀ j, v j ∈ subdomainSpace 𝕜 (S j)) →
      ∑ ij ∈ ps, RCLike.re (energyInner (Matrix.toEuclideanLin A) (u ij.1) (v ij.2))
        ≤ K₁ * Real.sqrt (∑ i ∈ Finset.range s,
              energyNorm (Matrix.toEuclideanLin A) (u i) ^ 2)
            * Real.sqrt (∑ j ∈ Finset.range s,
              energyNorm (Matrix.toEuclideanLin A) (v j) ^ 2)

end Assumptions

section Rates

variable {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) (S : ℕ → Finset (Fin n))

include hA

private theorem isStableDecompositionWith_of {s : ℕ} {K₀ : ℝ}
    (h : IsStableDecomposition A S s K₀) :
    Schwarz.IsStableDecompositionWith (energySpace hA S) s K₀ := by
  intro u
  obtain ⟨z, rfl⟩ := (WithEnergy.equiv (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA)).surjective u
  obtain ⟨w, hmem, hsum, hbd⟩ := h z
  refine ⟨fun i => WithEnergy.equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA) (w i),
    fun i hi => (WithEnergy.equiv_mem_submoduleMap_iff _ _).2 (hmem i hi), ?_, ?_⟩
  · rw [← map_sum, hsum]
  · simpa only [WithEnergy.norm_equiv] using hbd

private theorem isStrengthenedCauchySchwarzWith_of {s : ℕ} {K₁ : ℝ}
    (h : IsStrengthenedCauchySchwarz A S s K₁) :
    Schwarz.IsStrengthenedCauchySchwarzWith (energySpace hA S) s K₁ := by
  intro ps hps x y
  have hmem : ∀ (z : ℕ → energySpaceType hA) (i : ℕ),
      (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA)).symm
        ((energySpace hA S i).starProjection (z i)) ∈ subdomainSpace 𝕜 (S i) := by
    intro z i
    rw [← WithEnergy.equiv_mem_submoduleMap_iff (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), LinearEquiv.apply_symm_apply]
    exact Submodule.starProjection_apply_mem _ _
  have key := h ps hps _ _ (hmem x) (hmem y)
  simpa only [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA),
    ← WithEnergy.norm_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA),
    LinearEquiv.apply_symm_apply] using key

/-- **Theorem 14.7** in quadratic-form language: under Assumption 1, `‖u‖_A²/K₀ ≤ (A_J u, u)_A`.
With `re_energyInner_A_J_le` this encloses the spectrum of `A_J` in `[1/K₀, s]`, so the
condition number of the additive Schwarz preconditioned system is at most `s K₀`. -/
theorem le_re_energyInner_A_J {s : ℕ} {K₀ : ℝ} (hst : IsStableDecomposition A S s K₀)
    (u : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) u ^ 2 / K₀
      ≤ RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, energyNorm_eq_norm_equiv hA]
  exact Schwarz.le_re_inner_additiveOperator (energySpace hA S)
    (isStableDecompositionWith_of hA S hst) _

/-- **Theorem 14.7**: under Assumption 1, `λ_min(A_J) ≥ 1/K₀`.  With Theorem 14.5 the spectrum
of the additive Schwarz preconditioned operator lies in `[1/K₀, s]`, so its condition number is
at most `s K₀` and preconditioned conjugate gradients converge at the corresponding rate. -/
theorem theorem_14_7 {s : ℕ} {K₀ : ℝ} (hst : IsStableDecomposition A S s K₀) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    1 / K₀ ≤ RCLike.re μ :=
  (re_mem_Icc_of_hasEigenvalue (Schwarz.additiveOperator_isSymmetric (energySpace hA S) s)
    (fun u => by
      rw [one_div, inv_mul_eq_div]
      exact Schwarz.le_re_inner_additiveOperator (energySpace hA S)
        (isStableDecompositionWith_of hA S hst) u)
    (fun u => Schwarz.re_inner_additiveOperator_le (energySpace hA S) s u)
    (hasEigenvalue_additiveOperator hA S s hμ)).1

/-- **(14.39)**: `‖Q_s v‖_A² = ‖v‖_A² - ∑_{i<s} ‖P_i Q_i v‖_A²`.  In particular the `A`-norm of
the error does not increase at any substep of a multiplicative sweep. -/
theorem equation_14_39 (s : ℕ) (v : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) (Q_s A S s ⬝ v) ^ 2
      = energyNorm (Matrix.toEuclideanLin A) v ^ 2
        - ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
            (subdomainProjector A (S i) ⬝ (Q_s A S i ⬝ v)) ^ 2 := by
  simp only [energyNorm_eq_norm_equiv hA, equiv_Q_s hA S, equiv_subdomainProjector hA S]
  exact Schwarz.norm_errorOp_sq_eq (energySpace hA S) s _

/-- **Lemma 14.8**, (14.41): under Assumption 2 the projections of a vector are controlled by
the projections of the partially swept vectors,
`∑_i ‖P_i v‖_A² ≤ (1 + K₁)² ∑_i ‖P_i Q_i v‖_A²`. -/
theorem lemma_14_8 {s : ℕ} {K₁ : ℝ} (hcs : IsStrengthenedCauchySchwarz A S s K₁)
    (v : EuclideanSpace 𝕜 (Fin n)) :
    ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
        (subdomainProjector A (S i) ⬝ v) ^ 2
      ≤ (1 + K₁) ^ 2 * ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
          (subdomainProjector A (S i) ⬝ (Q_s A S i ⬝ v)) ^ 2 := by
  simp only [energyNorm_eq_norm_equiv hA, equiv_Q_s hA S, equiv_subdomainProjector hA S]
  exact Schwarz.sum_norm_starProjection_sq_le (energySpace hA S)
    (isStrengthenedCauchySchwarzWith_of hA S hcs) _

/-- **Theorem 14.9**: under Assumptions 1 and 2 one multiplicative Schwarz sweep contracts the
`A`-norm of the error by `√(1 - 1/(K₀ (1 + K₁)²))`, a rate depending only on the two constants —
in particular not on the number of subdomains. -/
theorem theorem_14_9 {s : ℕ} {K₀ K₁ : ℝ} (hK₀ : 0 < K₀) (hK₁ : 0 ≤ K₁)
    (hst : IsStableDecomposition A S s K₀) (hcs : IsStrengthenedCauchySchwarz A S s K₁)
    (v : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) (Q_s A S s ⬝ v)
      ≤ Real.sqrt (1 - 1 / (K₀ * (1 + K₁) ^ 2)) * energyNorm (Matrix.toEuclideanLin A) v := by
  simp only [energyNorm_eq_norm_equiv hA, equiv_Q_s hA S]
  exact Schwarz.norm_errorOp_le (energySpace hA S) hK₀ hK₁
    (isStableDecompositionWith_of hA S hst) (isStrengthenedCauchySchwarzWith_of hA S hcs) _

end Rates
end SaadSparse.Chapter14
