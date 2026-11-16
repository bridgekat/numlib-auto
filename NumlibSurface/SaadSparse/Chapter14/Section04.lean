/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Sum.Order
import Numlib.DomainDecomposition.Schur
import Numlib.Preconditioner.ILU
import NumlibSurface.SaadSparse.Chapter14.Section02

/-!
# Saad, Section 14.4: Schur complement approaches

This module formalizes Sections 14.4.1 and 14.4.2 of [saad2003iterative]. A Schur complement method
solves the reduced system $Sy = g'$ of Section 14.2 by a preconditioned Krylov method. Section
14.4.1 builds the preconditioner for $S$ from a preconditioner $M_A$ of the whole matrix $A$: the
induced preconditioner is $M_S = (R_y M_A^{-1} R_y^T)^{-1}$ (14.46), where $R_y = (0 \ \ I)$
restricts a vector to its interface block. The matrix $A$ itself, used as a preconditioner of $A$,
induces the Schur complement $S$. Proposition 14.10 states that if $M_A = L_A U_A$ is factored with
block triangular factors, as an ILU factorization is in the ordering that lists the interface
variables last, then $M_S = L_S U_S$ with $L_S = R_y L_A R_y^T$ and $U_S = R_y U_A R_y^T$. The
proofs specialize `Numlib.DomainDecomposition.Schur`.

Section 14.4.2 describes probing. The matrix $S$ is dense, but its entries decay away from the
diagonal, so it is replaced by a tridiagonal matrix $T$ that is recovered from three matrix–vector
products. The module formalizes the exact part: the three $3$-periodic probe vectors, the identity
that reads one entry of $T$ in each position, and the resulting fact that the three products
determine a tridiagonal matrix.

## Main definitions

* Section 14.4.1, `SaadSparse.Chapter14.interfaceRestrictMatrix`: the matrix $R_y = (0 \ \ I)$.
* Section 14.4.1, `SaadSparse.Chapter14.interfaceProlongMatrix`: the matrix $R_y^T$.
* Equation (14.46), `SaadSparse.Chapter14.inducedPreconditioner`: the induced preconditioner
  $M_S = (R_y M_A^{-1} R_y^T)^{-1}$.
* Section 14.4.2, `SaadSparse.Chapter14.probeVec`: the probe vectors $w_1$, $w_2$, $w_3$.

## Main results

* Section 14.4.1, `SaadSparse.Chapter14.inducedPreconditioner_eq_schurComplement`: the
  preconditioner that $A$ itself induces is $S$.
* Proposition 14.10, `SaadSparse.Chapter14.proposition_14_10`: for block triangular factors $L_A$
  and $U_A$, $M_S = (R_y L_A R_y^T)(R_y U_A R_y^T)$.
* Proposition 14.10, `SaadSparse.Chapter14.proposition_14_10_of_isILU`: the same for an ILU
  factorization in the ordering of (14.2).
* Section 14.4.2, `SaadSparse.Chapter14.mulVec_probeVec_apply`: $(T w_{r})_i$ is the entry of row
  $i$ of $T$ whose column is congruent to $r$ modulo $3$.
* Section 14.4.2, `SaadSparse.Chapter14.probing_eq`: two tridiagonal matrices with the same three
  probe products are equal.

## Implementation notes

* The global ordering of Section 14.2 lists the interior variables before the interface variables.
  In Lean it is the lexicographic order on `Fin p ⊕ₗ Fin q`. A factorization that is triangular for
  this order is block triangular for the partitioning (14.2), by
  `SaadSparse.Chapter14.toBlocks₁₂_eq_zero_of_isILU` and
  `SaadSparse.Chapter14.toBlocks₂₁_eq_zero_of_isILU`.

## Deviations from the source

* **Proposition 14.10** (generalization). The book assumes an ILU factorization;
  `SaadSparse.Chapter14.proposition_14_10` assumes only block triangular factors. See
  `SaadSparse.Chapter14.proposition_14_10_of_isILU` for the form of the book.

## Not formalized

* **The use of probing in Section 14.4.2.** The approximation of $S$ by the tridiagonal $T$ is a
  heuristic. The book gives no bound on $S - T$, and none holds without hypotheses that it does not
  state.
* **Section 14.4.3** (preconditioning vertex-based Schur complements). It is a paragraph of advice
  with no stated result.
-/

open Matrix DomainDecomposition

namespace SaadSparse.Chapter14

variable {p q : ℕ}

/-! ### The interface restriction as a matrix -/

/-- **Section 14.4.1** of [saad2003iterative]. The matrix $R_y = (0 \ \ I) \in \mathbb{R}^{q \times
(p + q)}$ that restricts a vector of the partitioned system (14.2) to its interface block. It
appears in Proposition 14.1 and in (14.46). -/
noncomputable abbrev interfaceRestrictMatrix (p q : ℕ) : Matrix (Fin q) (Fin p ⊕ Fin q) ℝ :=
  restrictMatrix ℝ (Fin p) (Fin q)

/-- **Section 14.4.1** of [saad2003iterative]. The matrix $R_y^T \in \mathbb{R}^{(p + q) \times q}$
that extends an interface vector by zero. -/
noncomputable abbrev interfaceProlongMatrix (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin q) ℝ :=
  prolongMatrix ℝ (Fin p) (Fin q)

/-- For every $v \in \mathbb{R}^{p + q}$, the product $R_y v$ is the interface block of $v$,
`SaadSparse.Chapter14.interfaceRestrict v`. -/
theorem interfaceRestrictMatrix_mulVec (v : Fin p ⊕ Fin q → ℝ) :
    interfaceRestrictMatrix p q *ᵥ v = interfaceRestrict v :=
  restrictMatrix_mulVec v

/-- $R_y R_y^T = I$: the rows of $R_y$ are orthonormal. -/
theorem interfaceRestrictMatrix_mul_interfaceProlongMatrix :
    interfaceRestrictMatrix p q * interfaceProlongMatrix p q = 1 :=
  restrictMatrix_mul_prolongMatrix

/-! ### Section 14.4.1: Induced preconditioners -/

/-- **Equation (14.46)** of [saad2003iterative]. For a preconditioner
$M_A \in \mathbb{R}^{(p+q) \times (p+q)}$ of the whole matrix, the **induced preconditioner** of
the Schur complement is
$$M_S = (R_y M_A^{-1} R_y^T)^{-1}.$$

To apply $M_S^{-1}$ to $v$ means to solve $M_A (x, y)^T = (0, v)^T$ and to keep $y$, which is
(14.45). The inverses are Mathlib's `Matrix.inv`, which is $0$ at a singular matrix. -/
noncomputable def inducedPreconditioner (MA : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  (interfaceRestrictMatrix p q * MA⁻¹ * interfaceProlongMatrix p q)⁻¹

/-- The induced preconditioner $M_S$ of Section 14.4.1 equals the backbone
`DomainDecomposition.inducedPreconditioner`, which is the inverse of the $(2,2)$ block of
$M_A^{-1}$. -/
theorem inducedPreconditioner_eq (MA : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ) :
    inducedPreconditioner MA = DomainDecomposition.inducedPreconditioner MA :=
  (inducedPreconditioner_eq_inv_restrict_mul MA).symm

/-- **Section 14.4.1** of [saad2003iterative], the remark after (14.46). Let $B$ and $A =
\begin{pmatrix} B & E \\ F & C \end{pmatrix}$ be nonsingular. Then the preconditioner that $A$
induces on the Schur complement is the Schur complement itself:
$$(R_y A^{-1} R_y^T)^{-1} = S = C - F B^{-1} E.$$

So an exact preconditioner of $A$ induces an exact preconditioner of $S$. This is Proposition
14.1(3), `SaadSparse.Chapter14.proposition_14_1_3`, read as a statement about matrices instead
of vectors. -/
theorem inducedPreconditioner_eq_schurComplement {B : Matrix (Fin p) (Fin p) ℝ}
    {E : Matrix (Fin p) (Fin q) ℝ} {F : Matrix (Fin q) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}
    (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    inducedPreconditioner (fromBlocks B E F C) = schurComplement B E F C := by
  rw [inducedPreconditioner_eq, DomainDecomposition.inducedPreconditioner,
    Matrix.toBlocks₂₂_inv_eq_inv_schurComplement (by simpa using hB) hA]
  exact Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 (proposition_14_1_1 hB hA))

/-- **Proposition 14.10** of [saad2003iterative], for block triangular factors. Let
$L_B, U_B \in \mathbb{R}^{p \times p}$ and $L_S, U_S \in \mathbb{R}^{q \times q}$ be
nonsingular, and let $X \in \mathbb{R}^{q \times p}$ and $Y \in \mathbb{R}^{p \times q}$. Let
$$L_A = \begin{pmatrix} L_B & 0 \\ X & L_S \end{pmatrix}, \qquad U_A = \begin{pmatrix} U_B & Y
  \\ 0 & U_S \end{pmatrix}$$
be block lower and block upper triangular for the partitioning (14.2). Then the preconditioner
that $M_A = L_A U_A$ induces on $S$ by (14.46) is
$$M_S = (R_y L_A R_y^T)(R_y U_A R_y^T) = L_S U_S.$$

So the $L$ and $U$ factors of $M_S$ are the $(2,2)$ blocks of the $L$ and $U$ factors of $M_A$.

**Generalization.** The book states the proposition for an ILU factorization of $A$ in the
ordering that lists the interface variables last, whose factors have the block triangular shape
displayed in Section 14.4.1. This version assumes only that shape.
`SaadSparse.Chapter14.proposition_14_10_of_isILU` states the result with the hypothesis of the
book. -/
theorem proposition_14_10 (LB UB : Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin q) (Fin p) ℝ)
    (Y : Matrix (Fin p) (Fin q) ℝ) (LS US : Matrix (Fin q) (Fin q) ℝ) (hLB : IsUnit LB)
    (hLS : IsUnit LS) (hUB : IsUnit UB) (hUS : IsUnit US) :
    inducedPreconditioner (fromBlocks LB 0 X LS * fromBlocks UB Y 0 US)
      = (interfaceRestrictMatrix p q * fromBlocks LB 0 X LS * interfaceProlongMatrix p q)
        * (interfaceRestrictMatrix p q * fromBlocks UB Y 0 US * interfaceProlongMatrix p q) := by
  rw [restrictMatrix_mul_mul_prolongMatrix, restrictMatrix_mul_mul_prolongMatrix,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₂, inducedPreconditioner_eq]
  exact DomainDecomposition.inducedPreconditioner_eq hLB hLS hUB hUS

/-!
### The block structure of an ILU factorization

The ordering `Fin p ⊕ₗ Fin q` is the global ordering of Section 14.2, in which the interior
variables come before the interface variables. A factorization that is triangular for this ordering
is block triangular for the partitioning (14.2).
-/

/-- Let $L U$ be an incomplete $LU$ factorization of $A$ (`Matrix.IsILU`) in the ordering of (14.2).
Then the $L$ factor is block lower triangular: its $(1,2)$ block is zero. -/
theorem toBlocks₁₂_eq_zero_of_isILU {P : Set ((Fin p ⊕ₗ Fin q) × (Fin p ⊕ₗ Fin q))}
    {A L U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ}
    (h : Matrix.IsILU P (A : Matrix (Fin p ⊕ₗ Fin q) (Fin p ⊕ₗ Fin q) ℝ) L U) :
    L.toBlocks₁₂ = 0 := by
  ext i j
  exact h.l_eq_zero_of_lt (toLex (Sum.inl i)) (toLex (Sum.inr j)) (Sum.Lex.inl_lt_inr i j)

/-- Let $L U$ be an incomplete $LU$ factorization of $A$ (`Matrix.IsILU`) in the ordering of (14.2).
Then the $U$ factor is block upper triangular: its $(2,1)$ block is zero. -/
theorem toBlocks₂₁_eq_zero_of_isILU {P : Set ((Fin p ⊕ₗ Fin q) × (Fin p ⊕ₗ Fin q))}
    {A L U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ}
    (h : Matrix.IsILU P (A : Matrix (Fin p ⊕ₗ Fin q) (Fin p ⊕ₗ Fin q) ℝ) L U) :
    U.toBlocks₂₁ = 0 := by
  ext i j
  exact h.u_eq_zero_of_gt (toLex (Sum.inr i)) (toLex (Sum.inl j)) (Sum.Lex.inl_lt_inr j i)

/-- **Proposition 14.10** of [saad2003iterative]. Let $A \in \mathbb{R}^{(p+q) \times (p+q)}$, and
let $M_A = L_A U_A$ be an incomplete $LU$ factorization of $A$ for some zero pattern, in the
ordering of (14.2) that lists the interior variables first and the interface variables last.
Assume that the diagonal blocks of $L_A$ and $U_A$ are nonsingular. Then the preconditioner that
$M_A$ induces on the Schur complement by (14.46) is
$$M_S = L_S U_S, \qquad L_S = R_y L_A R_y^T, \quad U_S = R_y U_A R_y^T.$$

This is the form in which the book states the proposition. The incomplete factorization is
`Matrix.IsILU` for the matrices read in the order `Fin p ⊕ₗ Fin q`. Its factors are block
triangular, so the proof reduces to `SaadSparse.Chapter14.proposition_14_10`. -/
theorem proposition_14_10_of_isILU {P : Set ((Fin p ⊕ₗ Fin q) × (Fin p ⊕ₗ Fin q))}
    {A LA UA : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ}
    (h : Matrix.IsILU P (A : Matrix (Fin p ⊕ₗ Fin q) (Fin p ⊕ₗ Fin q) ℝ) LA UA)
    (hLB : IsUnit LA.toBlocks₁₁) (hLS : IsUnit LA.toBlocks₂₂) (hUB : IsUnit UA.toBlocks₁₁)
    (hUS : IsUnit UA.toBlocks₂₂) :
    inducedPreconditioner (LA * UA)
      = (interfaceRestrictMatrix p q * LA * interfaceProlongMatrix p q)
        * (interfaceRestrictMatrix p q * UA * interfaceProlongMatrix p q) := by
  have hLb : LA = fromBlocks LA.toBlocks₁₁ 0 LA.toBlocks₂₁ LA.toBlocks₂₂ := by
    rw [← toBlocks₁₂_eq_zero_of_isILU h, Matrix.fromBlocks_toBlocks]
  have hUb : UA = fromBlocks UA.toBlocks₁₁ UA.toBlocks₁₂ 0 UA.toBlocks₂₂ := by
    rw [← toBlocks₂₁_eq_zero_of_isILU h, Matrix.fromBlocks_toBlocks]
  rw [restrictMatrix_mul_mul_prolongMatrix, restrictMatrix_mul_mul_prolongMatrix,
    inducedPreconditioner_eq,
    show LA * UA = fromBlocks LA.toBlocks₁₁ 0 LA.toBlocks₂₁ LA.toBlocks₂₂
        * fromBlocks UA.toBlocks₁₁ UA.toBlocks₁₂ 0 UA.toBlocks₂₂ from by rw [← hLb, ← hUb]]
  exact DomainDecomposition.inducedPreconditioner_eq hLB hLS hUB hUS

/-! ### Section 14.4.2: Probing -/

/-- **Section 14.4.2** of [saad2003iterative]. The three $3$-periodic **probe vectors** of the
probing technique,
$$w_1 = (1, 0, 0, 1, 0, 0, \dots)^T, \quad w_2 = (0, 1, 0, 0, 1, 0, \dots)^T, \quad w_3 = (0, 0,
  1, 0, 0, 1, \dots)^T.$$

The book's $w_{r+1}$ is `SaadSparse.Chapter14.probeVec m r`: its entry $i$ (counted from $0$) is
$1$ if $i \equiv r \pmod 3$ and $0$ otherwise. For $r \ge 3$ the vector is $0$. -/
def probeVec (m : ℕ) (r : ℕ) : Fin m → ℝ := fun i => if (i : ℕ) % 3 = r then 1 else 0

/-- A tridiagonal matrix $T$ has $T_{ij} = 0$ whenever $i + 1 < j$ or $j + 1 < i$. -/
private theorem apply_eq_zero_of_isTridiagonal {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : T.IsTridiagonal) {i j : Fin m} (h : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) :
    T i j = 0 := by
  rcases h with h | h
  · refine hT i j (Or.inr ⟨⟨(i : ℕ) + 1, lt_of_lt_of_le h j.isLt.le⟩, ?_, ?_⟩) <;>
      simp [Fin.lt_def, h]
  · refine hT i j (Or.inl ⟨⟨(j : ℕ) + 1, lt_of_lt_of_le h i.isLt.le⟩, ?_, ?_⟩) <;>
      simp [Fin.lt_def, h]

/-- **Section 14.4.2** of [saad2003iterative], the probing identity. Let
$T \in \mathbb{R}^{m \times m}$ be tridiagonal, and let $i, j$ be indices with $|i - j| \le 1$.
Then the product of $T$ with the probe vector for the residue $j \bmod 3$ has the entry $T_{ij}$
in position $i$:
$$(T w_{(j \bmod 3) + 1})_i = T_{ij}.$$

The three columns $i - 1$, $i$, $i + 1$ have three distinct residues modulo $3$. Therefore every
entry of $T$ appears in exactly one of the three products. This is the book's "it is easy to
recover $T$ by applying it to three well-chosen vectors". -/
theorem mulVec_probeVec_apply {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.IsTridiagonal)
    {i j : Fin m}
    (hij : (j : ℕ) ≤ (i : ℕ) + 1 ∧ (i : ℕ) ≤ (j : ℕ) + 1) :
    (T *ᵥ probeVec m ((j : ℕ) % 3)) i = T i j := by
  rw [Matrix.mulVec_apply_eq_sum]
  refine (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intro k _ hkj
    by_cases hk : (i : ℕ) + 1 < (k : ℕ) ∨ (k : ℕ) + 1 < (i : ℕ)
    · rw [apply_eq_zero_of_isTridiagonal hT hk, zero_mul]
    · have hne : ¬ (k : ℕ) % 3 = (j : ℕ) % 3 := fun hmod =>
        hkj (Fin.ext (by obtain ⟨hij₁, hij₂⟩ := hij; omega))
      rw [probeVec, ite_eq_right hne, mul_zero]
  · exact fun h => absurd (Finset.mem_univ j) h
  · rw [probeVec, ite_eq_left rfl, mul_one]

/-- **Section 14.4.2** of [saad2003iterative], the reconstruction. Let
$T, T' \in \mathbb{R}^{m \times m}$ be tridiagonal. If $T w_k = T' w_k$ for every probe vector
$w_k$, then $T = T'$.

So the tridiagonal approximation $T$ of the Schur complement is determined by the three products
$S w_1$, $S w_2$, $S w_3$ alone. The book states no bound on $S - T$, and none holds without
hypotheses that the book does not give. The exact part of the technique is this reconstruction.
The hypothesis is stated for all residues $r$, and only $r = 0, 1, 2$ give nonzero probe
vectors. -/
theorem probing_eq {m : ℕ} {T T' : Matrix (Fin m) (Fin m) ℝ} (hT : T.IsTridiagonal)
    (hT' : T'.IsTridiagonal)
    (h : ∀ r, T *ᵥ probeVec m r = T' *ᵥ probeVec m r) : T = T' := by
  ext i j
  by_cases hij : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)
  · rw [apply_eq_zero_of_isTridiagonal hT hij, apply_eq_zero_of_isTridiagonal hT' hij]
  · rw [← mulVec_probeVec_apply hT ⟨by omega, by omega⟩,
      ← mulVec_probeVec_apply hT' ⟨by omega, by omega⟩, h]

end SaadSparse.Chapter14
