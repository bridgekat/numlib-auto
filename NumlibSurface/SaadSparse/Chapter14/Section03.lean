/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.DomainDecomposition.Schwarz
import Numlib.Stationary.Block
import NumlibSurface.SaadSparse.Chapter12.Section02

/-!
# Saad, Section 14.3: The Schwarz alternating procedures

This module formalizes Section 14.3 of [saad2003iterative], together with the vertex-based
partitioning of Section 14.2.3 that Theorem 14.2 needs. The data of Section 14.3 are index sets
$S_i \subseteq \{1, \dots, n\}$, not necessarily disjoint, the boolean restriction matrices $R_i$ of
Section 14.3.1, the local matrices $A_i = R_i A R_i^T$, the operators $T_i = R_i^T A_i^{-1} R_i$ of
(14.31) and $P_i = T_i A$ of (14.24), and the subdomain spaces $\operatorname{Ran}(R_i^T) =
\operatorname{span}\{e_j : j \in S_i\}$. For a symmetric positive definite $A$, $P_i$ is the
$A$-orthogonal projector onto $\operatorname{Ran}(R_i^T)$. The module states the multiplicative
Schwarz procedure (14.25) with its error operator $Q_s$ (14.26), the additive procedure, Proposition
14.3 and Lemma 14.4, and the convergence theory of Section 14.3.4: the bounds of Theorems 14.5 and
14.6 on the largest eigenvalue of the additive Schwarz operator $A_J = \sum_i P_i$ (14.37),
Assumptions 1 and 2, the lower bound $\lambda_{\min}(A_J) \ge 1/K_0$ of Theorem 14.7, and the
contraction rate of a multiplicative sweep in Lemma 14.8 and Theorem 14.9. The convergence theory
specializes `Numlib.DomainDecomposition.Schwarz`, whose statements are about orthogonal projectors
in an inner product space, in the energy inner product of $A$.

Theorem 14.2 concerns the other partitioning of the chapter, the vertex-based one of Section 14.2.3.
There each of $s$ subdomains owns interior nodes and interface nodes, the local matrices are $A_i =
\begin{pmatrix} B_i & E_i \\ F_i & C_i \end{pmatrix}$ (14.9), and the interface nodes of different
subdomains are coupled by blocks $E_{ij}$ (14.10). Elimination of the interior variables gives the
Schur complement system (14.12)–(14.14). Theorem 14.2 (Chan and Goovaerts) states that the
multiplicative Schwarz procedure, started from a consistent initial guess, produces on the interface
the iterates of block Gauss–Seidel on the Schur complement system. The proof rests on the fact that
the elimination of the interior variables commutes with taking the block-lower triangle.

## Main definitions

* Section 14.2.3, `SaadSparse.Chapter14.VertexPartitioning`: the data (14.8)–(14.10) of a
  vertex-based partitioning.
* Equation (14.8), `SaadSparse.Chapter14.VertexPartitioning.globalMatrix`: the global matrix of the
  partitioning.
* Equation (14.9), `SaadSparse.Chapter14.VertexPartitioning.localMatrix`: the local matrix $A_i$.
* Equation (14.10), `SaadSparse.Chapter14.VertexPartitioning.offDiag`: the interface coupling
  $E_{ij}$.
* Equation (14.13), `SaadSparse.Chapter14.VertexPartitioning.localSchur`: the local Schur complement
  $S_i = C_i - F_i B_i^{-1} E_i$.
* Equation (14.14), `SaadSparse.Chapter14.VertexPartitioning.schurMatrix`: the Schur complement
  system $S$.
* Equation (14.22), `SaadSparse.Chapter14.VertexPartitioning.IsConsistent`: a consistent initial
  guess.
* Algorithm 14.3, `SaadSparse.Chapter14.VertexPartitioning.schwarzSweep`: one multiplicative Schwarz
  sweep on the global matrix.
* Equation (14.25), `SaadSparse.Chapter14.multiplicativeSweep`: the multiplicative Schwarz
  procedure.
* Equation (14.26), `SaadSparse.Chapter14.Q_s`: its error propagation operator
  $Q_s = (I - P_{s-1}) \cdots (I - P_0)$.
* Section 14.3.3, `SaadSparse.Chapter14.additiveSweep`: the additive Schwarz procedure.
* Equation (14.37), `SaadSparse.Chapter14.A_J`: the additive Schwarz operator $A_J = \sum_i P_i$.
* Assumption 1, `SaadSparse.Chapter14.IsStableDecomposition`: a stable decomposition with constant
  $K_0$.
* Assumption 2, `SaadSparse.Chapter14.IsStrengthenedCauchySchwarz`: a strengthened Cauchy–Schwarz
  inequality with constant $K_1$ (14.40).

## Main results

* Equation (14.14), `SaadSparse.Chapter14.VertexPartitioning.schurMatrix_eq`: $S$ is the Schur
  complement of the global matrix.
* Equations (14.11) and (14.12), `SaadSparse.Chapter14.VertexPartitioning.equation_14_11` and
  `SaadSparse.Chapter14.VertexPartitioning.equation_14_12`: the rows of the global system and of the
  Schur complement system at subdomain $i$.
* Equation (14.22), `SaadSparse.Chapter14.VertexPartitioning.isConsistent_iff`: an initial guess is
  consistent if and only if $x_i = B_i^{-1}(f_i - E_i y_i)$ for every $i$.
* Theorem 14.2, `SaadSparse.Chapter14.theorem_14_2`: from a consistent initial guess, the interface
  iterates of Algorithm 14.3 are the iterates of block Gauss–Seidel on the Schur complement system.
* Proposition 14.3, `SaadSparse.Chapter14.proposition_14_3`: the multiplicative and the additive
  procedures are fixed-point iterations $x \leftarrow x + M^{-1}(b - Ax)$, with $M^{-1} A = I - Q_s$
  and $M^{-1} A = A_J$.
* Lemma 14.4, `SaadSparse.Chapter14.lemma_14_4`: the recurrences (14.32) and (14.33) and the
  expansion (14.35) of $I - Q_s$.
* Theorem 14.5, `SaadSparse.Chapter14.theorem_14_5`: $\lambda_{\max}(A_J) \le s$.
* Theorem 14.6, `SaadSparse.Chapter14.theorem_14_6`: $\lambda_{\max}(A_J)$ is at most the number of
  colours of a colouring of the subdomains with no coupling inside a colour.
* Theorem 14.7, `SaadSparse.Chapter14.theorem_14_7`: under Assumption 1,
  $\lambda_{\min}(A_J) \ge 1/K_0$.
* Equation (14.39), `SaadSparse.Chapter14.equation_14_39`: $\|Q_s v\|_A^2 = \|v\|_A^2 - \sum_i \|P_i
  Q_i v\|_A^2$.
* Lemma 14.8, `SaadSparse.Chapter14.lemma_14_8`: under Assumption 2, $\sum_i \|P_i v\|_A^2 \le (1 +
  K_1)^2 \sum_i \|P_i Q_i v\|_A^2$.
* Theorem 14.9, `SaadSparse.Chapter14.theorem_14_9`: under Assumptions 1 and 2, $\|Q_s v\|_A \le
  \sqrt{1 - 1/(K_0 (1 + K_1)^2)} \, \|v\|_A$.

## Conventions

* Indices are $0$-based: the subdomains $i = 1, \dots, s$ of the book are
  $i \in \{0, \dots, s - 1\}$ (`Finset.range s`), and the number of subdomains is the cutoff $s$.
* The scalar field is $\mathbb{R}$ or $\mathbb{C}$ (`[RCLike 𝕜]`). The energy inner product
  $(Au, v)$ is `energyInner (Matrix.toEuclideanLin A) u v` and the energy norm $\|u\|_A$ is
  `energyNorm (Matrix.toEuclideanLin A) u`. Over $\mathbb{R}$ these are the quantities of the book,
  and over $\mathbb{C}$ they are the Hermitian ones.

## Implementation notes

* The restriction matrices, the local matrices and the subdomain operators are those of Section
  12.2, where the book first writes them as $V_i = R_i^T$ and $A_i = V_i^T A V_i$. They are
  `SaadSparse.Chapter12.restrictSubset`, `SaadSparse.Chapter12.localMatrix`,
  `SaadSparse.Chapter12.subdomainInverse` ($T_i$), `SaadSparse.Chapter12.subdomainProjector` ($P_i$)
  and `SaadSparse.Chapter12.subdomainSpace` of `NumlibSurface.SaadSparse.Chapter12.Section02`, and
  this module opens that namespace.
* The convergence theory rests on `SaadSparse.Chapter12.subdomainProjector_eq_energyProjection`: for
  a symmetric positive definite $A$, $P_i$ is the $A$-orthogonal projector onto the subdomain space.
* In the vertex-based partitioning, the nodes are listed with all interior nodes first and all
  interface nodes last, as in (14.2). The block structure (14.8) by subdomains is carried by the
  label function `SaadSparse.Chapter14.nodeLabel`, not by the order of the indices; the two orders
  differ by a permutation. Both iterations of Theorem 14.2 are block Gauss–Seidel sweeps for this
  labelling, and they are identified with `Matrix.blockGaussSeidelSplitting`.

## Deviations from the source

* **Theorem 14.6** (correction). The book asks only that subdomains of the same colour have no
  common nodes. This is not enough; the theorem assumes that subdomains of the same colour have no
  coupling in $A$. See `SaadSparse.Chapter14.theorem_14_6`.
-/

open Matrix Finset

open scoped ComplexOrder SaadSparse

namespace SaadSparse.Chapter14

/-!
### Section 14.2.3 and Section 14.3.1: The vertex-based partitioning and Theorem 14.2

The rest of the module treats the *edge-based* picture of Section 14.3, in which the subdomains are
index sets $S_i \subseteq \{1, \dots, n\}$. This part treats the *vertex-based* picture of Section
14.2.3, which Theorem 14.2 needs and which nothing else in Section 14.3 uses. The nodes carry a
subdomain label, and inside each subdomain they split into interior nodes and interface nodes.
-/

section VertexBased

/-- **Equation (14.8)** of [saad2003iterative], the subdomain of a node. A node is an interior node
$\langle i, a \rangle$ or an interface node $\langle i, a \rangle$ of subdomain $i$, and its
label is $i$. This labelling is the block structure (14.8) of the global matrix by subdomains. -/
def nodeLabel {ι : Type*} (P Q : ι → Type*) : ((i : ι) × P i) ⊕ ((i : ι) × Q i) → ι :=
  Sum.elim Sigma.fst Sigma.fst

/-- The label of an interior node $\langle i, a \rangle$ is its subdomain $i$. -/
@[simp]
theorem nodeLabel_inl {ι : Type*} (P Q : ι → Type*) (p : (i : ι) × P i) :
    nodeLabel P Q (Sum.inl p) = p.1 := rfl

/-- The label of an interface node $\langle i, a \rangle$ is its subdomain $i$. -/
@[simp]
theorem nodeLabel_inr {ι : Type*} (P Q : ι → Type*) (p : (i : ι) × Q i) :
    nodeLabel P Q (Sum.inr p) = p.1 := rfl

/-- **Section 14.2.3** of [saad2003iterative], equations (14.8)–(14.10). A **vertex-based
partitioning** into the subdomains $i \in \iota$, where subdomain $i$ owns the interior nodes
$P_i$ and the interface nodes $Q_i$, consists of the four blocks of (14.9): for each $i$, the
couplings $B_i$ (interior–interior), $E_i$ (interface to interior) and $F_i$ (interior to
interface) of subdomain $i$, and one matrix $C$ that holds all interface–interface couplings.
The diagonal block $(i, i)$ of $C$ is $C_i$, and its block $(i, j)$ is $E_{ij}$ of (14.10).

No further condition is assumed, because (14.10) is what the shape of these data says. With the
nodes listed interiors first and interfaces last, as in (14.2), the interior rows and columns of
the global matrix are block diagonal over the subdomains. This is exactly the statement that for
$i \ne j$ the block $A_{ij}$ of (14.8) is zero outside its interface–interface corner. -/
structure VertexPartitioning (𝕜 : Type*) {ι : Type*} (P Q : ι → Type*) where
  /-- The block $B_i$ of (14.9): the coupling between the interior nodes of subdomain $i$. -/
  B : ∀ i, Matrix (P i) (P i) 𝕜
  /-- The block $E_i$ of (14.9): the coupling from the interface nodes of subdomain $i$ to its
  interior nodes. -/
  E : ∀ i, Matrix (P i) (Q i) 𝕜
  /-- The block $F_i$ of (14.9): the coupling from the interior nodes of subdomain $i$ to its
  interface nodes. -/
  F : ∀ i, Matrix (Q i) (P i) 𝕜
  /-- The interface matrix: its block $(i, i)$ is $C_i$ of (14.9), and its block $(i, j)$ is
  $E_{ij}$ of (14.10). -/
  C : Matrix ((i : ι) × Q i) ((i : ι) × Q i) 𝕜

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {P Q : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
variable [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
variable (V : VertexPartitioning 𝕜 P Q)

namespace VertexPartitioning

section Plumbing

omit [Fintype ι] in
/-- On a block diagonal matrix, the filter that keeps the blocks with $i = j$ changes nothing. -/
private theorem ite_blockDiagonal' {m' n' : ι → Type*} (M : ∀ i, Matrix (m' i) (n' i) 𝕜)
    {i j : ι} (a : m' i) (b : n' j) :
    (if i = j then blockDiagonal' M ⟨i, a⟩ ⟨j, b⟩ else 0) = blockDiagonal' M ⟨i, a⟩ ⟨j, b⟩ := by
  by_cases h : i = j
  · simp [h]
  · rw [blockDiagonal'_apply_ne _ a b h]; simp

omit [Fintype ι] in
/-- On a block diagonal matrix, the filter for the strict block-lower part adds nothing to the
filter for the block diagonal. -/
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
/-- The interior rows of $\begin{pmatrix} M_{11} & M_{12} \\ M_{21} & M_{22} \end{pmatrix} w$ are
$M_{11} w_1 + M_{12} w_2$. -/
private theorem comp_inl_fromBlocks_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (M₁₁ : Matrix m m 𝕜) (M₁₂ : Matrix m n 𝕜) (M₂₁ : Matrix n m 𝕜) (M₂₂ : Matrix n n 𝕜)
    (w : m ⊕ n → 𝕜) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *ᵥ w) ∘ Sum.inl
      = M₁₁ *ᵥ (w ∘ Sum.inl) + M₁₂ *ᵥ (w ∘ Sum.inr) := by
  rw [fromBlocks_mulVec]; rfl

omit [Fintype ι] [LinearOrder ι] in
/-- The interface rows of $\begin{pmatrix} M_{11} & M_{12} \\ M_{21} & M_{22} \end{pmatrix} w$ are
$M_{21} w_1 + M_{22} w_2$. -/
private theorem comp_inr_fromBlocks_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (M₁₁ : Matrix m m 𝕜) (M₁₂ : Matrix m n 𝕜) (M₂₁ : Matrix n m 𝕜) (M₂₂ : Matrix n n 𝕜)
    (w : m ⊕ n → 𝕜) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *ᵥ w) ∘ Sum.inr
      = M₂₁ *ᵥ (w ∘ Sum.inl) + M₂₂ *ᵥ (w ∘ Sum.inr) := by
  rw [fromBlocks_mulVec]; rfl

omit [Fintype ι] [LinearOrder ι] in
/-- On a vector $(0, v)$ with zero interior part, the interface rows of $Mv$ are $M_{22} v$. -/
private theorem comp_inr_mulVec_elim_zero {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix (m ⊕ n) (m ⊕ n) 𝕜) (v : n → 𝕜) :
    (M *ᵥ Sum.elim (0 : m → 𝕜) v) ∘ Sum.inr = M.toBlocks₂₂ *ᵥ v := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [comp_inr_fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, zero_add]

omit [LinearOrder ι] in
/-- A block diagonal matrix acts on each block separately: block $i$ of $\operatorname{diag}(M_j) v$
is $M_i v_i$. -/
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
/-- Block row $i$ of a matrix–vector product over a sigma index type is $\sum_j M_{ij} v_j$. -/
private theorem comp_mulVec_sigma [∀ i, Fintype (n' i)]
    (M : Matrix ((i : ι) × m' i) ((i : ι) × n' i) 𝕜) (v : ((i : ι) × n' i) → 𝕜) (i : ι) :
    (M *ᵥ v) ∘ Sigma.mk i = ∑ j, M.submatrix (Sigma.mk i) (Sigma.mk j) *ᵥ (v ∘ Sigma.mk j) := by
  funext a
  simp only [Function.comp_apply, mulVec, dotProduct, Finset.sum_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl

omit [Fintype ι] [LinearOrder ι] in
/-- If $M$ is nonsingular, then $Mx + c = d$ if and only if $x = M^{-1}(d - c)$. -/
private theorem mulVec_add_eq_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix m m 𝕜}
    (hM : IsUnit M) (x c d : m → 𝕜) : M *ᵥ x + c = d ↔ x = M⁻¹ *ᵥ (d - c) := by
  constructor
  · rintro rfl
    rw [add_sub_cancel_right, nonsing_inv_mulVec_mulVec hM]
  · rintro rfl
    rw [mulVec_nonsing_inv_mulVec hM]
    abel

end Plumbing

/-! ### The blocks (14.8)–(14.14) -/

/-- **Equation (14.8)** of [saad2003iterative]. The **global matrix** of a vertex-based
partitioning, with the nodes listed interiors first and interfaces last as in (14.2):
$$A = \begin{pmatrix} \operatorname{diag}(B_i) & \operatorname{diag}(E_i) \\
  \operatorname{diag}(F_i) & C \end{pmatrix}.$$

The block structure of (14.8) by subdomains is carried by `SaadSparse.Chapter14.nodeLabel`, not
by the order of the indices. The two orders differ by a permutation only. -/
def globalMatrix : Matrix (((i : ι) × P i) ⊕ ((i : ι) × Q i))
    (((i : ι) × P i) ⊕ ((i : ι) × Q i)) 𝕜 :=
  fromBlocks (blockDiagonal' V.B) (blockDiagonal' V.E) (blockDiagonal' V.F) V.C

/-- **Equation (14.9)** of [saad2003iterative]. The block $C_i$, the local part of the interface
matrix: the coupling between the interface nodes of subdomain $i$. -/
def localC (i : ι) : Matrix (Q i) (Q i) 𝕜 := V.C.submatrix (Sigma.mk i) (Sigma.mk i)

/-- **Equation (14.9)** of [saad2003iterative]. The **local matrix** of subdomain $i$,
$$A_i = \begin{pmatrix} B_i & E_i \\ F_i & C_i \end{pmatrix}.$$
-/
def localMatrix (i : ι) : Matrix (P i ⊕ Q i) (P i ⊕ Q i) 𝕜 :=
  fromBlocks (V.B i) (V.E i) (V.F i) (V.localC i)

/-- **Equation (14.10)** of [saad2003iterative]. The block $E_{ij}$ of the interface matrix: the
coupling from the interface nodes of subdomain $j$ to those of subdomain $i$. For $i \ne j$ it
is the only nonzero block of $A_{ij}$. For $i = j$ it is $C_i$. -/
def offDiag (i j : ι) : Matrix (Q i) (Q j) 𝕜 := V.C.submatrix (Sigma.mk i) (Sigma.mk j)

/-- **Equation (14.13)** of [saad2003iterative]. The **local Schur complement** of subdomain $i$,
$$S_i = C_i - F_i B_i^{-1} E_i,$$
the Schur complement `Matrix.schurComplement` of the local matrix $A_i$. -/
noncomputable def localSchur (i : ι) : Matrix (Q i) (Q i) 𝕜 := (V.localMatrix i).schurComplement

omit [Fintype ι] [LinearOrder ι] [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **Equation (14.13)** of [saad2003iterative]: the local Schur complement is
$S_i = C_i - F_i B_i^{-1} E_i$. -/
theorem localSchur_eq (i : ι) :
    V.localSchur i = V.localC i - V.F i * (V.B i)⁻¹ * V.E i := rfl

/-- **Equation (14.14)** of [saad2003iterative]. The **Schur complement system** of the
partitioning,
$$S = C - \operatorname{diag}(F_i B_i^{-1} E_i).$$
Its diagonal blocks are the local Schur complements $S_i$, and its off-diagonal blocks are the
interface couplings $E_{ij}$. -/
noncomputable def schurMatrix : Matrix ((i : ι) × Q i) ((i : ι) × Q i) 𝕜 :=
  V.C - blockDiagonal' fun i => V.F i * (V.B i)⁻¹ * V.E i

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- Let every $B_i$ be nonsingular, and let $X$ be any interface matrix. Then the Schur complement
of $\begin{pmatrix} \operatorname{diag}(B_i) & \operatorname{diag}(E_i) \\
\operatorname{diag}(F_i) & X \end{pmatrix}$ is $X - \operatorname{diag}(F_i B_i^{-1} E_i)$: the
interior variables decouple, so $F B^{-1} E$ is assembled subdomain by subdomain. -/
theorem schurComplement_fromBlocks_local (hB : ∀ i, IsUnit (V.B i))
    (X : Matrix ((i : ι) × Q i) ((i : ι) × Q i) 𝕜) :
    (fromBlocks (blockDiagonal' V.B) (blockDiagonal' V.E) (blockDiagonal' V.F) X).schurComplement
      = X - blockDiagonal' fun i => V.F i * (V.B i)⁻¹ * V.E i := by
  rw [schurComplement_fromBlocks, inv_blockDiagonal' V.B hB, blockDiagonal'_mul,
    blockDiagonal'_mul]

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **Equations (14.5) and (14.14)** of [saad2003iterative]. If every $B_i$ is nonsingular, then the
Schur complement system $S$ of (14.14) is the Schur complement (14.5) of the global matrix with
respect to the interior variables. -/
theorem schurMatrix_eq (hB : ∀ i, IsUnit (V.B i)) :
    V.schurMatrix = V.globalMatrix.schurComplement :=
  (V.schurComplement_fromBlocks_local hB V.C).symm

omit [Fintype ι] [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **Equation (14.14)** of [saad2003iterative]. The diagonal blocks of the Schur complement system
$S$ are the local Schur complements $S_i$. -/
theorem blockDiagPart_schurMatrix :
    blockDiagPart Sigma.fst V.schurMatrix = blockDiagonal' V.localSchur := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [blockDiagPart_apply]
  split_ifs with h
  · subst h
    rw [blockDiagonal'_apply_eq, schurMatrix, Matrix.sub_apply, blockDiagonal'_apply_eq]
    rfl
  · rw [blockDiagonal'_apply_ne _ _ _ h]

/-! ### Faithfulness of the block structure -/

omit [Fintype ι] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] in
/-- **Equation (14.9)** of [saad2003iterative]. The local matrix $A_i$ is the diagonal block of the
global matrix on the nodes of subdomain $i$. -/
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
/-- **Equation (14.10)** of [saad2003iterative]. Let $i \ne j$. Then the block $A_{ij}$ of the
global matrix (14.8) is zero in its interior–interior, interior–interface and interface–interior
corners, and its interface–interface corner is $E_{ij}$. -/
theorem equation_14_10 {i j : ι} (h : i ≠ j) (a : P i) (b : P j) (c : Q i) (d : Q j) :
    V.globalMatrix (Sum.inl ⟨i, a⟩) (Sum.inl ⟨j, b⟩) = 0
      ∧ V.globalMatrix (Sum.inl ⟨i, a⟩) (Sum.inr ⟨j, d⟩) = 0
      ∧ V.globalMatrix (Sum.inr ⟨i, c⟩) (Sum.inl ⟨j, b⟩) = 0
      ∧ V.globalMatrix (Sum.inr ⟨i, c⟩) (Sum.inr ⟨j, d⟩) = V.offDiag i j c d :=
  ⟨blockDiagonal'_apply_ne _ a b h, blockDiagonal'_apply_ne _ a d h,
    blockDiagonal'_apply_ne _ c b h, rfl⟩

omit [∀ i, DecidableEq (P i)] [∀ i, DecidableEq (Q i)] in
/-- **Equation (14.11)** of [saad2003iterative]. Let $z = (x, y)$ be a vector on all nodes, with
$x_i$ and $y_i$ its interior and interface parts on subdomain $i$. Then the two rows of the
global system that belong to subdomain $i$ are
$$(Az)_{x,i} = B_i x_i + E_i y_i, \qquad (Az)_{y,i} = F_i x_i + C_i y_i + \sum_{j \ne i} E_{ij}
  y_j.$$
-/
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
/-- **Equation (14.12)** of [saad2003iterative]. For an interface vector $y$, the block row of the
Schur complement system at subdomain $i$ is
$$(Sy)_i = S_i y_i + \sum_{j \ne i} E_{ij} y_j.$$
-/
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

/-! ### The two block Gauss–Seidel sweeps -/

omit [Fintype ι] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] in
/-- The block diagonal part $D$ of the global matrix for the subdomain blocks is the block diagonal
matrix of the local matrices $A_i$: its interior blocks are those of $A$, and its interface
block is the block diagonal part of $C$. -/
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

/-- **Algorithm 14.3** of [saad2003iterative]. The block-lower factor $D - E$ of the global matrix
for the subdomain blocks: the sum of its block diagonal part and its strict block-lower part for
the labelling `SaadSparse.Chapter14.nodeLabel`. One block Gauss–Seidel sweep over the subdomains
solves a system with this matrix. -/
def globalLower : Matrix (((i : ι) × P i) ⊕ ((i : ι) × Q i))
    (((i : ι) × P i) ⊕ ((i : ι) × Q i)) 𝕜 :=
  blockDiagPart (nodeLabel P Q) V.globalMatrix + blockStrictLower (nodeLabel P Q) V.globalMatrix

/-- **Equation (14.14)** of [saad2003iterative]. The block-lower factor $D - E$ of the Schur
complement system $S$ for the subdomain blocks: the sum of its block diagonal part and its
strict block-lower part. -/
noncomputable def schurLower : Matrix ((i : ι) × Q i) ((i : ι) × Q i) 𝕜 :=
  blockDiagPart Sigma.fst V.schurMatrix + blockStrictLower Sigma.fst V.schurMatrix

omit [Fintype ι] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] in
/-- The block-lower factor of the global matrix differs from the global matrix only in the
interface–interface corner, where it is the block-lower factor of $C$. The interior rows and
columns of (14.8) are already block diagonal, so the sweep does not change them. -/
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
/-- Let every $B_i$ be nonsingular. Then the Schur complement of the block-lower factor of the
global matrix is the block-lower factor of the Schur complement system $S$.

So the elimination of the interior variables commutes with taking the block-lower triangle. This
is why a Schwarz sweep on (14.8) and a Gauss–Seidel sweep on (14.14) are the same iteration, and
it is the key identity behind `SaadSparse.Chapter14.theorem_14_2`. -/
theorem schurComplement_globalLower (hB : ∀ i, IsUnit (V.B i)) :
    V.globalLower.schurComplement = V.schurLower := by
  rw [globalLower_eq, V.schurComplement_fromBlocks_local hB, schurLower, schurMatrix,
    blockDiagPart_sub_blockDiagonal', blockStrictLower_sub_blockDiagonal']
  abel

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- Let every $B_i$ be nonsingular. Then the Schur complement of the block diagonal part of the
global matrix is the block diagonal part of the Schur complement system $S$. -/
theorem schurComplement_blockDiagPart_globalMatrix (hB : ∀ i, IsUnit (V.B i)) :
    (blockDiagPart (nodeLabel P Q) V.globalMatrix).schurComplement
      = blockDiagPart Sigma.fst V.schurMatrix := by
  rw [blockDiagPart_globalMatrix, V.schurComplement_fromBlocks_local hB, schurMatrix,
    blockDiagPart_sub_blockDiagonal']

/-- **Equation (14.12)** of [saad2003iterative], right-hand side. For a right-hand side $b = (f, g)$
on all nodes, the right-hand side of the Schur complement system is
$$g' = g - \operatorname{diag}(F_i) \operatorname{diag}(B_i)^{-1} f,$$
with block $g_i - F_i B_i^{-1} f_i$ at subdomain $i$. -/
noncomputable def reducedRhs (b : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) :
    ((i : ι) × Q i) → 𝕜 :=
  b ∘ Sum.inr - (blockDiagonal' V.F * (blockDiagonal' V.B)⁻¹) *ᵥ (b ∘ Sum.inl)

/-- **Equation (14.22)** of [saad2003iterative]. An initial guess $z = (x, y)$ is **consistent** for
the right-hand side $b = (f, g)$ if its interior part solves the interior equations of (14.11)
exactly, $B_i x_i + E_i y_i = f_i$ for every $i$. Equivalently, the interior components of the
global residual $b - Az$ vanish. -/
def IsConsistent (b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) : Prop :=
  (V.globalMatrix *ᵥ z) ∘ Sum.inl = b ∘ Sum.inl

/-- **Algorithm 14.3** of [saad2003iterative], one multiplicative Schwarz sweep in matrix form. For
the global matrix $A$, the right-hand side $b$ and the current iterate $z$, the sweep returns
$$z + (D - E)^{-1} (b - Az),$$
where $D - E$ is the block-lower factor of $A$ for the subdomain blocks.

The algorithm solves $A_i \delta_i = r_i$ for each subdomain in turn, each time from the
residual that the previous solve left behind. The accumulated correction solves the block-lower
system $(D - E) \delta = b - Az$; this is
`Matrix.blockGaussSeidelSplitting_step_eq_multiplicativeStep`. -/
noncomputable def schwarzSweep (b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) :
    (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜 :=
  z + V.globalLower⁻¹ *ᵥ (b - V.globalMatrix *ᵥ z)

/-- One block Gauss–Seidel sweep on the Schur complement system (14.12), with the interface unknowns
$y_i$ of the subdomains as blocks: for the right-hand side $g$ and the iterate $y$ it returns
$y + (D_S - E_S)^{-1} (g - Sy)$, where $D_S - E_S$ is the block-lower factor of $S$. -/
noncomputable def schurGaussSeidelSweep (g y : ((i : ι) × Q i) → 𝕜) : ((i : ι) × Q i) → 𝕜 :=
  y + V.schurLower⁻¹ *ᵥ (g - V.schurMatrix *ᵥ y)

/-- **Algorithm 14.3** of [saad2003iterative]. If the block diagonal part of the global matrix is
nonsingular, then the block-lower factor $D - E$ of the sweep is the matrix $M$ of the block
Gauss–Seidel splitting `Matrix.blockGaussSeidelSplitting` of the global matrix for the subdomain
labelling. -/
theorem globalLower_eq_blockGaussSeidelSplitting
    (h : IsUnit (blockDiagPart (nodeLabel P Q) V.globalMatrix)) :
    V.globalLower = (blockGaussSeidelSplitting (nodeLabel P Q) V.globalMatrix h).m := rfl

/-- **Equation (14.12)** of [saad2003iterative]. If the block diagonal part of $S$ is nonsingular,
then the block-lower factor $D_S - E_S$ of the Schur complement system is the matrix $M$ of the
block Gauss–Seidel splitting `Matrix.blockGaussSeidelSplitting` of $S$ for the subdomain
labelling. -/
theorem schurLower_eq_blockGaussSeidelSplitting
    (h : IsUnit (blockDiagPart Sigma.fst V.schurMatrix)) :
    V.schurLower = (blockGaussSeidelSplitting Sigma.fst V.schurMatrix h).m := rfl

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
/-- **Equation (14.12)** of [saad2003iterative], right-hand side on subdomain $i$. If every $B_i$ is
nonsingular, then block $i$ of the reduced right-hand side is $g_i - F_i B_i^{-1} f_i$. -/
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
/-- An initial guess $z = (x, y)$ is consistent if and only if $B_i x_i + E_i y_i = f_i$ for every
subdomain $i$, the first line of (14.11). -/
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
/-- **Equation (14.22)** of [saad2003iterative]. Let every $B_i$ be nonsingular. Then an initial
guess $z = (x, y)$ is consistent if and only if
$$x_i = B_i^{-1} (f_i - E_i y_i)$$
for every subdomain $i$. This is the hypothesis of Theorem 14.2. -/
theorem isConsistent_iff (hB : ∀ i, IsUnit (V.B i))
    (b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜) :
    V.IsConsistent b z ↔ ∀ i, (z ∘ Sum.inl) ∘ Sigma.mk i
      = (V.B i)⁻¹ *ᵥ ((b ∘ Sum.inl) ∘ Sigma.mk i - V.E i *ᵥ ((z ∘ Sum.inr) ∘ Sigma.mk i)) := by
  rw [isConsistent_iff_local V b z]
  exact forall_congr' fun i => mulVec_add_eq_iff (hB i) _ _ _

/-! ### Theorem 14.2 -/

/-- If every local Schur complement $S_i$ is nonsingular, then the block-lower factor of the Schur
complement system is nonsingular. -/
theorem isUnit_schurLower (hS : ∀ i, IsUnit (V.localSchur i)) : IsUnit V.schurLower :=
  isUnit_blockDiagPart_add_blockStrictLower
    (by rw [blockDiagPart_schurMatrix]; exact isUnit_blockDiagonal' _ hS)

/-- If every $B_i$ and every local Schur complement $S_i$ is nonsingular, then the block-lower
factor of the global matrix is nonsingular. The proof applies Proposition 14.1(1). -/
theorem isUnit_globalLower (hB : ∀ i, IsUnit (V.B i)) (hS : ∀ i, IsUnit (V.localSchur i)) :
    IsUnit V.globalLower := by
  refine isUnit_of_isUnit_schurComplement ?_ ?_
  · rw [globalLower_eq, toBlocks_fromBlocks₁₁]
    exact isUnit_blockDiagonal' _ hB
  · rw [schurComplement_globalLower V hB]
    exact isUnit_schurLower V hS

/-- If every $B_i$ and every local Schur complement $S_i$ is nonsingular, then the block diagonal
part of the global matrix, the block diagonal matrix of the local matrices $A_i$, is
nonsingular. This makes the subdomain solves of Algorithm 14.3 well posed. -/
theorem isUnit_blockDiagPart_globalMatrix (hB : ∀ i, IsUnit (V.B i))
    (hS : ∀ i, IsUnit (V.localSchur i)) :
    IsUnit (blockDiagPart (nodeLabel P Q) V.globalMatrix) := by
  refine isUnit_of_isUnit_schurComplement ?_ ?_
  · rw [blockDiagPart_globalMatrix, toBlocks_fromBlocks₁₁]
    exact isUnit_blockDiagonal' _ hB
  · rw [schurComplement_blockDiagPart_globalMatrix V hB, blockDiagPart_schurMatrix]
    exact isUnit_blockDiagonal' _ hS

omit [∀ i, DecidableEq (Q i)] in
/-- **Theorem 14.2** of [saad2003iterative], first half of the proof. Let every $B_i$ be
nonsingular, and let $z = (x, y)$ be consistent for $b = (f, g)$. Then the interface components
of the global residual are the residual of the Schur complement system (14.12) at the same $y$:
$$(b - Az)_y = g' - S y.$$

The substitution of $x_i = B_i^{-1}(f_i - E_i y_i)$ into $g_i - F_i x_i - C_i y_i - \sum_{j \ne
i} E_{ij} y_j$ turns $C_i$ into $S_i$ and $g_i$ into $g_i - F_i B_i^{-1} f_i$. -/
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

/-- **Theorem 14.2** of [saad2003iterative], second half of the proof. Let every $B_i$ and every
$S_i$ be nonsingular, and let $z = (x, y)$ be consistent for $b$. Then the interface part of one
sweep of Algorithm 14.3 from $z$ is one block Gauss–Seidel sweep on the Schur complement system
$Sy = g'$ from $y$.

When the interior residuals $r_{x,i}$ vanish, the subdomain solve $A_i \delta_i = (0, r_{y,i})$
returns $\delta_{y,i} = S_i^{-1} r_{y,i}$ by (14.7). Assembled over the subdomains, this is the
statement that the $(2,2)$ block of $(D - E)^{-1}$ is the inverse of the Schur complement of
$D - E$. -/
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

/-- **Theorem 14.2** of [saad2003iterative], invariance of consistency. Let every $B_i$ and every
$S_i$ be nonsingular. If $z$ is consistent for $b$, then so is the result of one sweep of
Algorithm 14.3 from $z$.

The sweep changes the residual only in its interface components, since the interior rows of the
global matrix and of its block-lower factor agree. This is the book's "because only the $y$
components of the residual vector are modified, this property remains valid throughout the
iterative process". -/
theorem isConsistent_schwarzSweep (hB : ∀ i, IsUnit (V.B i)) (hS : ∀ i, IsUnit (V.localSchur i))
    {b z : (((i : ι) × P i) ⊕ ((i : ι) × Q i)) → 𝕜} (hc : V.IsConsistent b z) :
    V.IsConsistent b (V.schwarzSweep b z) := by
  set d := V.globalLower⁻¹ *ᵥ (b - V.globalMatrix *ᵥ z) with hd
  have hLd : V.globalLower *ᵥ d = b - V.globalMatrix *ᵥ z := by
    rw [hd, mulVec_nonsing_inv_mulVec (isUnit_globalLower V hB hS)]
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

/-- **Theorem 14.2** of [saad2003iterative] (Chan and Goovaerts). Let $A$ be the global matrix of a
vertex-based partitioning (14.8), with every $B_i$ and every local Schur complement $S_i$
nonsingular. Let the initial guess $z = (x^{(0)}, y^{(0)})$ be consistent for $b = (f, g)$, that
is $x_i^{(0)} = B_i^{-1} (f_i - E_i y_i^{(0)})$ (14.22). Then for every $k \ge 0$, the interface
part of the $k$-th iterate of the multiplicative Schwarz procedure (Algorithm 14.3) is the
$k$-th iterate of the block Gauss–Seidel method applied to the Schur complement system (14.12)
$Sy = g'$ from $y^{(0)}$.

The two hypotheses are the nonsingularity that makes the two iterations defined: every $B_i$, so
that the interior variables can be eliminated, and every $S_i$, so that the diagonal blocks of
(14.14) can be solved with. -/
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

/-!
### Section 14.3.1: The restriction matrices and the subdomain spaces

The book introduces $V_i = [e_j : j \in S_i]$ and $A_i = V_i^T A V_i$ in Section 12.2, and Section
14.3.1 uses the same objects under the names $R_i = V_i^T$ and $A_i$. They are therefore
`SaadSparse.Chapter12.restrictSubset`, `SaadSparse.Chapter12.subdomainSpace`,
`SaadSparse.Chapter12.localMatrix`, `SaadSparse.Chapter12.subdomainInverse` and
`SaadSparse.Chapter12.subdomainProjector`, opened here and not defined again. The subdomain solve
$T_i$ of (14.31) is `SaadSparse.Chapter12.subdomainInverse`, and the projector $P_i$ of (14.24) is
`SaadSparse.Chapter12.subdomainProjector`.
-/

open Chapter12

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}

/-! ### Sections 14.3.2 and 14.3.3: The multiplicative and additive procedures -/

section Procedures

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **Equation (14.25)** of [saad2003iterative], the **multiplicative Schwarz procedure**. For a
matrix $A \in \mathbb{K}^{n \times n}$, subdomains $S_0, S_1, \dots$, a right-hand side $b$ and
a starting vector $x$, the sweep over the subdomains $S_0, \dots, S_{i-1}$ in order is defined
by
$$x^{(0)} = x, \qquad x^{(j+1)} = x^{(j)} + T_j (b - A x^{(j)}),$$
where $T_j = R_j^T A_j^{-1} R_j$. Each correction is computed from the iterate that the previous
one produced. -/
noncomputable def multiplicativeSweep (b : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → EuclideanSpace 𝕜 (Fin n) → EuclideanSpace 𝕜 (Fin n)
  | 0, x => x
  | i + 1, x => multiplicativeSweep b i x +
      (subdomainInverse A (S i) ⬝ (b - (A ⬝ multiplicativeSweep b i x)))

/-- A sweep over no subdomains does not change the iterate. -/
@[simp]
theorem multiplicativeSweep_zero (b x : EuclideanSpace 𝕜 (Fin n)) :
    multiplicativeSweep A S b 0 x = x := rfl

/-- One more subdomain adds one more correction $T_i (b - A x^{(i)})$, computed from the current
iterate. -/
theorem multiplicativeSweep_succ (b : EuclideanSpace 𝕜 (Fin n)) (i : ℕ)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    multiplicativeSweep A S b (i + 1) x = multiplicativeSweep A S b i x +
      (subdomainInverse A (S i) ⬝ (b - (A ⬝ multiplicativeSweep A S b i x))) := rfl

/-- **Section 14.3.3** of [saad2003iterative], the **additive Schwarz procedure**. All $s$
corrections are computed from the same iterate and added at once:
$$x \leftarrow x + \sum_{i < s} T_i (b - Ax).$$
-/
noncomputable def additiveSweep (s : ℕ) (b x : EuclideanSpace 𝕜 (Fin n)) :
    EuclideanSpace 𝕜 (Fin n) :=
  x + ∑ i ∈ Finset.range s, (subdomainInverse A (S i) ⬝ (b - (A ⬝ x)))

/-- **Equation (14.26)** of [saad2003iterative]. The **error propagation operator** of one
multiplicative Schwarz sweep over $S_0, \dots, S_{s-1}$,
$$Q_s = (I - P_{s-1}) \cdots (I - P_0),$$
where $P_i = T_i A$. The empty product $Q_0$ is $I$. -/
noncomputable def Q_s : ℕ → Matrix (Fin n) (Fin n) 𝕜
  | 0 => 1
  | i + 1 => (1 - subdomainProjector A (S i)) * Q_s i

/-- The error propagation operator of a sweep over no subdomains is $Q_0 = I$. -/
@[simp]
theorem Q_s_zero : Q_s A S 0 = 1 := rfl

/-- One more subdomain composes one more factor on the left: $Q_{i+1} = (I - P_i) Q_i$. -/
theorem Q_s_succ (i : ℕ) :
    Q_s A S (i + 1) = (1 - subdomainProjector A (S i)) * Q_s A S i := rfl

/-- **Equation (14.37)** of [saad2003iterative]. The **additive Schwarz operator**
$$A_J = \sum_{i < s} P_i.$$
-/
noncomputable def A_J (s : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  ∑ i ∈ Finset.range s, subdomainProjector A (S i)

/-- The additive Schwarz preconditioner $M^{-1} = \sum_{i < s} T_i$ satisfies $M^{-1} A = A_J$. -/
theorem sum_subdomainInverse_mul (s : ℕ) :
    (∑ i ∈ Finset.range s, subdomainInverse A (S i)) * A = A_J A S s := by
  rw [A_J, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (subdomainProjector_eq_mul A (S i)).symm

/-- **Equation (14.26)** of [saad2003iterative], meaning of $Q_s$. Let $A x_* = b$. Then for every
starting vector $x$, the error after a multiplicative sweep over $S_0, \dots, S_{s-1}$ is
$$x_* - x^{(s)} = Q_s (x_* - x).$$

No hypothesis on $A$ is needed: this is the algebra of the corrections, not their optimality. -/
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

/-- **Proposition 14.3** of [saad2003iterative]. Let $A$ be Hermitian positive definite and
$A x_* = b$. Then for every $s$ and every $x$:

* one multiplicative Schwarz sweep is one step of the fixed-point iteration
  $x \leftarrow x + M^{-1}(b - Ax)$ with $M^{-1} = (I - Q_s) A^{-1}$ (14.28), so that
  $M^{-1} A = I - Q_s$ (14.27);
* one additive Schwarz step is the same iteration with $M^{-1} = \sum_{i < s} T_i$;
* this $M^{-1}$ satisfies $M^{-1} A = A_J$, the additive Schwarz operator (14.37). -/
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

/-! ### Section 14.3.2: Lemma 14.4, the recurrences of Algorithms 14.4 and 14.5 -/

section Lemma144

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **Equation (14.35)** of [saad2003iterative]. What a multiplicative sweep adds to the iterate is
$$I - Q_s = \sum_{j < s} P_j Q_j.$$
-/
theorem one_sub_Q_s_eq_sum (s : ℕ) :
    1 - Q_s A S s = ∑ j ∈ Finset.range s, subdomainProjector A (S j) * Q_s A S j := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Q_s_succ, Finset.sum_range_succ, ← ih]
      noncomm_ring

/-- **Lemma 14.4** of [saad2003iterative]. Let $A$ be Hermitian positive definite, and let
$Z_i = I - Q_i$, $M_i = Z_i A^{-1}$ and $T_i = R_i^T A_i^{-1} R_i$. Then for all $i$ and $s$
$$Z_{i+1} = Z_i + P_i (I - Z_i), \qquad M_{i+1} = M_i + T_i (I - A M_i), \qquad I - Q_s =
  \sum_{j < s} P_j Q_j.$$

These are the recurrences (14.32) and (14.33) and the expansion (14.35). The second recurrence
is Algorithm 14.5: it applies $M^{-1}$ without ever forming $A^{-1}$. -/
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

/-! ### Section 14.3.4: The convergence theory -/

section Convergence

variable {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) (S : ℕ → Finset (Fin n))

include hA

/-- The energy space of $A$: the same vectors, with the inner product $(x, y)_A$. -/
private noncomputable abbrev energySpaceType : Type _ :=
  WithEnergy (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)

/-- The subdomain spaces as subspaces of the energy space of $A$. -/
private noncomputable abbrev energySpace (i : ℕ) : Submodule 𝕜 (energySpaceType hA) :=
  WithEnergy.submoduleMap (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
    (subdomainSpace 𝕜 (S i))

private theorem energyNorm_eq_norm_equiv (x : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) x
      = ‖WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x‖ :=
  (WithEnergy.norm_equiv _ _ x).symm

/-- In the energy space, $P_i$ is the orthogonal projector onto the subdomain space $V_i$. -/
private theorem equiv_subdomainProjector (i : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    WithEnergy.equiv (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
        (subdomainProjector A (S i) ⬝ x)
      = (energySpace hA S i).starProjection (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x) := by
  rw [subdomainProjector_eq_energyProjection hA]
  exact Schwarz.equiv_energyProjection _ _ _ x

/-- In the energy space, $Q_s$ is the error operator `Schwarz.errorOp`. -/
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

/-- In the energy space, $A_J$ is the additive Schwarz operator `Schwarz.additiveOperator`. -/
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
/-- If $T$ is symmetric and $a \|u\|^2 \le \operatorname{Re}(Tu, u) \le b \|u\|^2$ for all $u$, then
every eigenvalue $\mu$ of $T$ satisfies $a \le \operatorname{Re} \mu \le b$. -/
private theorem re_mem_Icc_of_hasEigenvalue {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {T : H →ₗ[𝕜] H} {a b : ℝ} (hsym : T.IsSymmetric)
    (hlo : ∀ u, a * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T u) u))
    (hhi : ∀ u, RCLike.re (inner 𝕜 (T u) u) ≤ b * ‖u‖ ^ 2) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue T μ) : RCLike.re μ ∈ Set.Icc a b :=
  LinearMap.IsSymmetricBoundedBy.re_mem_Icc_of_hasEigenvalue ⟨hsym, hlo, hhi⟩ hμ

/-- Every eigenvalue of $A_J$ is an eigenvalue of the additive Schwarz operator of the energy space,
since the two are conjugate by `WithEnergy.equiv`. -/
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

/-! ### Theorem 14.5 and Theorem 14.6: The largest eigenvalue of $A_J$ -/

/-- **Theorem 14.5** of [saad2003iterative], quadratic-form version. Let $A$ be Hermitian positive
definite. Then for every $s$ and every $u$
$$\operatorname{Re} (A_J u, u)_A \le s \, \|u\|_A^2,$$
since each $P_i$ has $A$-norm at most one. -/
theorem re_energyInner_A_J_le (s : ℕ) (u : EuclideanSpace 𝕜 (Fin n)) :
    RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u)
      ≤ s * energyNorm (Matrix.toEuclideanLin A) u ^ 2 := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, energyNorm_eq_norm_equiv hA]
  exact Schwarz.re_inner_additiveOperator_le (energySpace hA S) s _

/-- Let $A$ be Hermitian positive definite. Then the additive Schwarz operator is positive
semidefinite in the energy inner product: $\operatorname{Re} (A_J u, u)_A \ge 0$ for every $u$. -/
theorem re_energyInner_A_J_nonneg (s : ℕ) (u : EuclideanSpace 𝕜 (Fin n)) :
    0 ≤ RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S]
  exact Schwarz.re_inner_additiveOperator_nonneg (energySpace hA S) s _

/-- **Equation (14.37)** of [saad2003iterative]. Let $A$ be Hermitian positive definite. Then the
additive Schwarz operator is self-adjoint for the energy inner product,
$(A_J u, v)_A = (u, A_J v)_A$, so its eigenvalues are real. -/
theorem isSymmetric_energyInner_A_J (s : ℕ) (u v : EuclideanSpace 𝕜 (Fin n)) :
    energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) v
      = energyInner (Matrix.toEuclideanLin A) u (A_J A S s ⬝ v) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), ← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, equiv_A_J hA S]
  exact Schwarz.additiveOperator_isSymmetric (energySpace hA S) s _ _

/-- **Theorem 14.5** of [saad2003iterative]. Let $A$ be Hermitian positive definite. Then every
eigenvalue $\mu$ of the additive Schwarz operator $A_J$ for $s$ subdomains satisfies
$$\operatorname{Re} \mu \le s.$$
That is, $\lambda_{\max}(A_J) \le s$.

The eigenvalues of $A_J$ are real by `SaadSparse.Chapter14.isSymmetric_energyInner_A_J`, so the
statement bounds the real part. -/
theorem theorem_14_5 (s : ℕ) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    RCLike.re μ ≤ s :=
  (re_mem_Icc_of_hasEigenvalue (a := 0)
    (Schwarz.additiveOperator_isSymmetric (energySpace hA S) s)
    (fun u => by simpa using Schwarz.re_inner_additiveOperator_nonneg (energySpace hA S) s u)
    (fun u => Schwarz.re_inner_additiveOperator_le (energySpace hA S) s u)
    (hasEigenvalue_additiveOperator hA S s hμ)).2

/-- If two subdomains have no coupling in $A$, then their subdomain spaces are $A$-orthogonal. -/
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

/-- **Theorem 14.6** of [saad2003iterative]. Let $A$ be Hermitian positive definite, and let the
subdomains $S_0, \dots, S_{s-1}$ be coloured by a map into a finite set of $c$ colours, such
that two different subdomains of the same colour have no coupling in $A$: $a_{lk} = 0$ for $k$
in one of them and $l$ in the other. Then every eigenvalue $\mu$ of $A_J$ satisfies
$$\operatorname{Re} \mu \le c.$$
That is, $\lambda_{\max}(A_J) \le c$.

**Correction.** The book asks only that two subdomains of the same colour "have no common
nodes", and justifies the bound by "$P_{\Theta_i} = \sum_{j \in \Theta_i} P_j$ is again an
orthogonal projector". That step needs the ranges to be $A$-orthogonal, which disjointness does
not give. A counterexample: $n = 2$, $A = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$,
$S_0 = \{0\}$ and $S_1 = \{1\}$, which are disjoint and therefore of one colour. Then $P_0 =
\begin{pmatrix} 1 & 1/2 \\ 0 & 0 \end{pmatrix}$, $P_1 = \begin{pmatrix} 0 & 0 \\ 1/2 & 1
\end{pmatrix}$ and $A_J = \begin{pmatrix} 1 & 1/2 \\ 1/2 & 1 \end{pmatrix}$, whose largest
eigenvalue is $3/2 > 1 = c$. The hypothesis of no coupling is what the proof needs, and a
decoupled colouring provides it. For a positive definite $A$ it forces the subdomains of one
colour to be disjoint.

With a colouring of the interaction graph of the subdomains, the bound does not grow with the
number of subdomains, unlike the bound of Theorem 14.5. -/
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

/-! ### Assumptions 1 and 2 -/

end Convergence

section Assumptions

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **Assumption 1** of [saad2003iterative], Section 14.3.4. The subdomains $S_0, \dots, S_{s-1}$
admit a **stable decomposition** with constant $K_0$ if every vector $u$ splits as
$u = \sum_{i < s} u_i$ with $u_i$ in the subdomain space of $S_i$ and
$$\sum_{i < s} \|u_i\|_A^2 \le K_0 \|u\|_A^2.$$

This is the hypothesis that the subdomains cover the domain stably. For a family of finite
elements, an overlapping partition of unity provides it. -/
def IsStableDecomposition (s : ℕ) (K₀ : ℝ) : Prop :=
  ∀ u : EuclideanSpace 𝕜 (Fin n), ∃ w : ℕ → EuclideanSpace 𝕜 (Fin n),
    (∀ i ∈ Finset.range s, w i ∈ subdomainSpace 𝕜 (S i)) ∧
      ∑ i ∈ Finset.range s, w i = u ∧
        ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A) (w i) ^ 2
          ≤ K₀ * energyNorm (Matrix.toEuclideanLin A) u ^ 2

/-- **Assumption 2** of [saad2003iterative], Section 14.3.4, (14.40). The subdomains
$S_0, \dots, S_{s-1}$ satisfy a **strengthened Cauchy–Schwarz inequality** with constant $K_1$
if for every set $\Pi$ of pairs $(i, j)$ with $i, j < s$, and all vectors $u_i$ and $v_j$ in the
subdomain spaces of $S_i$ and $S_j$,
$$\sum_{(i, j) \in \Pi} \operatorname{Re} (u_i, v_j)_A \le K_1 \Big(\sum_{i < s}
  \|u_i\|_A^2\Big)^{1/2} \Big(\sum_{j < s} \|v_j\|_A^2\Big)^{1/2}.$$

The constant measures how far the subdomain spaces are from being $A$-orthogonal. The set $\Pi$
may contain the diagonal pairs $(i, i)$, so $K_1 \ge 1$ whenever one of the subdomain spaces of
$S_0, \dots, S_{s-1}$ is nonzero. Mutually $A$-orthogonal subdomain spaces admit $K_1 = 1$,
because then only the diagonal pairs contribute, and the plain Cauchy–Schwarz inequality always
gives $K_1 = s$. -/
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

/-- **Theorem 14.7** of [saad2003iterative], quadratic-form version. Let $A$ be Hermitian positive
definite, and let Assumption 1 hold with constant $K_0$. Then for every $u$
$$\frac{\|u\|_A^2}{K_0} \le \operatorname{Re} (A_J u, u)_A.$$

With `SaadSparse.Chapter14.re_energyInner_A_J_le`, this encloses the spectrum of $A_J$ in
$[1/K_0, s]$, so the condition number of the system preconditioned by additive Schwarz is at
most $s K_0$. -/
theorem le_re_energyInner_A_J {s : ℕ} {K₀ : ℝ} (hst : IsStableDecomposition A S s K₀)
    (u : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) u ^ 2 / K₀
      ≤ RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, energyNorm_eq_norm_equiv hA]
  exact Schwarz.le_re_inner_additiveOperator (energySpace hA S)
    (isStableDecompositionWith_of hA S hst) _

/-- **Theorem 14.7** of [saad2003iterative]. Let $A$ be Hermitian positive definite, and let
Assumption 1 hold with constant $K_0$. Then every eigenvalue $\mu$ of $A_J$ satisfies
$$\frac{1}{K_0} \le \operatorname{Re} \mu.$$
That is, $\lambda_{\min}(A_J) \ge 1/K_0$.

With Theorem 14.5, the spectrum of the operator preconditioned by additive Schwarz lies in
$[1/K_0, s]$. So its condition number is at most $s K_0$, and the preconditioned conjugate
gradient method converges at the corresponding rate. -/
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

/-- **Equation (14.39)** of [saad2003iterative]. Let $A$ be Hermitian positive definite. Then for
every $s$ and every $v$
$$\|Q_s v\|_A^2 = \|v\|_A^2 - \sum_{i < s} \|P_i Q_i v\|_A^2.$$
In particular, the $A$-norm of the error does not increase at any substep of a multiplicative
sweep. -/
theorem equation_14_39 (s : ℕ) (v : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) (Q_s A S s ⬝ v) ^ 2
      = energyNorm (Matrix.toEuclideanLin A) v ^ 2
        - ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
            (subdomainProjector A (S i) ⬝ (Q_s A S i ⬝ v)) ^ 2 := by
  simp only [energyNorm_eq_norm_equiv hA, equiv_Q_s hA S, equiv_subdomainProjector hA S]
  exact Schwarz.norm_errorOp_sq_eq (energySpace hA S) s _

/-- **Lemma 14.8** of [saad2003iterative], (14.41). Let $A$ be Hermitian positive definite, and let
Assumption 2 hold with constant $K_1$. Then for every $v$
$$\sum_{i < s} \|P_i v\|_A^2 \le (1 + K_1)^2 \sum_{i < s} \|P_i Q_i v\|_A^2.$$
So the projections of a vector are controlled by the projections of the partially swept vectors. -/
theorem lemma_14_8 {s : ℕ} {K₁ : ℝ} (hcs : IsStrengthenedCauchySchwarz A S s K₁)
    (v : EuclideanSpace 𝕜 (Fin n)) :
    ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
        (subdomainProjector A (S i) ⬝ v) ^ 2
      ≤ (1 + K₁) ^ 2 * ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
          (subdomainProjector A (S i) ⬝ (Q_s A S i ⬝ v)) ^ 2 := by
  simp only [energyNorm_eq_norm_equiv hA, equiv_Q_s hA S, equiv_subdomainProjector hA S]
  exact Schwarz.sum_norm_starProjection_sq_le (energySpace hA S)
    (isStrengthenedCauchySchwarzWith_of hA S hcs) _

/-- **Theorem 14.9** of [saad2003iterative]. Let $A$ be Hermitian positive definite, and let
Assumptions 1 and 2 hold with constants $K_0 > 0$ and $K_1 \ge 0$. Then one multiplicative
Schwarz sweep contracts the $A$-norm of the error:
$$\|Q_s v\|_A \le \sqrt{1 - \frac{1}{K_0 (1 + K_1)^2}} \, \|v\|_A$$
for every $v$. The rate depends only on the two constants, and in particular not on the number
of subdomains. -/
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
