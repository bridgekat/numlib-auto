/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.SymplecticGroup`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Numlib.LinearAlgebra.Matrix.Symmetric

/-!
# Hamiltonian and skew-Hamiltonian matrices

Let $R$ be a commutative ring and let $J = \begin{bmatrix} 0 & -I \\ I & 0 \end{bmatrix}$ be the
canonical skew form on $R^{l \oplus l}$. A matrix $M$ on $l \oplus l$ is **Hamiltonian** if
$J M J^T = -M^T$, equivalently if $JM$ is symmetric, equivalently if $M = \begin{bmatrix} A & G \\ F
& -A^T \end{bmatrix}$ with $F$, $G$ symmetric. A matrix $N$ is **skew-Hamiltonian** if
$J N J^T = N^T$, equivalently if $JN$ is skew-symmetric, equivalently if $N = \begin{bmatrix} A & G
\\ F & A^T \end{bmatrix}$ with $F$, $G$ skew-symmetric. The presentation follows [golub2013matrix]
§1.3.10 and §7.8.1.

The module proves the facts that the Hamiltonian eigenvalue problem needs. Hamiltonian matrices form
a Lie algebra; symplectic similarity preserves both classes; $M^T$ is similar to $-M$ for
Hamiltonian $M$; and the square of a Hamiltonian matrix is skew-Hamiltonian. The orthogonal
symplectic matrices are exactly the block matrices $\begin{bmatrix} Q_1 & Q_2 \\ -Q_2 & Q_1
\end{bmatrix}$ with $Q_1^T Q_2$ symmetric and $Q_1^T Q_1 + Q_2^T Q_2 = I$. An orthonormal isotropic
family in $K^{l \oplus l}$ has at most $|l|$ members.

## Main definitions

* `Matrix.IsHamiltonian`: $J M J^T = -M^T$.
* `Matrix.IsSkewHamiltonian`: $J N J^T = N^T$.
* `Matrix.orthoSymplecticGroup`: the orthogonal symplectic matrices.

## Main results

* `Matrix.isHamiltonian_iff_isSymm_J_mul`, `Matrix.isHamiltonian_iff_mem_sp`,
  `Matrix.isHamiltonian_fromBlocks_iff`: $M$ is Hamiltonian if and only if $JM$ is symmetric, if and
  only if it is in Mathlib's symplectic Lie algebra, if and only if it has the block form above.
* `Matrix.isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule`,
  `Matrix.isSkewHamiltonian_fromBlocks_iff`: $N$ is skew-Hamiltonian if and only if it is
  $J$-self-adjoint, if and only if it has the block form above.
* `Matrix.IsHamiltonian.lie`: the commutator of two Hamiltonian matrices is Hamiltonian.
* `Matrix.IsHamiltonian.conj_symplectic`, `Matrix.IsSkewHamiltonian.conj_symplectic`: symplectic
  similarity preserves both classes.
* `Matrix.IsHamiltonian.transpose_mul_J_eq`: $M^T = JMJ$, so $M^T$ is similar to $-M$.
* `Matrix.IsHamiltonian.isSkewHamiltonian_mul_self`: $M^2$ is skew-Hamiltonian.
* `Matrix.mem_orthogonalGroup_symplecticGroup_iff`: the block form of the orthogonal symplectic
  matrices.
* `Matrix.IsHamiltonian.transpose_mul_mul_of_mem_orthoSymplecticGroup`: orthogonal symplectic
  similarity $Q^T M Q$ preserves Hamiltonian structure.
* `Matrix.card_le_of_transpose_mul_J_mul_eq_zero`: an orthonormal isotropic family in
  $K^{l \oplus l}$ has at most $|l|$ members.

## Implementation notes

* Mathlib has the skew form `Matrix.J l R = fromBlocks 0 (-1) 1 0`, the symplectic group
  `Matrix.symplecticGroup l R` of the matrices $S$ with $S J S^T = J$, and the symplectic Lie
  algebra `LieAlgebra.Symplectic.sp l R` of $J$-skew-adjoint matrices. The last are the Hamiltonian
  matrices, under a name and in a form that numerical texts do not use. This module gives the
  predicate its numerical name and the form $J M J^T = -M^T$ of the textbooks.
* The sign of $J$ does not matter. [golub2013matrix] writes $J = \begin{bmatrix} 0 & I \\ -I & 0
  \end{bmatrix}$, the negative of `Matrix.J`. The conditions $J M J^T = -M^T$, $J N J^T = N^T$ and
  $S J S^T = J$ do not change under $J \mapsto -J$.
* `Matrix.orthoSymplecticGroup` is a submonoid of the matrices, the intersection of the orthogonal
  group and the symplectic group.
-/

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix

variable {l R : Type*} [Fintype l] [CommRing R]

/-- For a skew-symmetric matrix $X$ on $l \oplus l$, the congruence $S^T X S$ is skew-symmetric. -/
private theorem transpose_transpose_mul_mul_of_transpose_eq_neg {X : Matrix (l ⊕ l) (l ⊕ l) R}
    (hX : Xᵀ = -X) (S : Matrix (l ⊕ l) (l ⊕ l) R) : (Sᵀ * X * S)ᵀ = -(Sᵀ * X * S) := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hX]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

variable [DecidableEq l]

/-- The skew form is orthogonal: $J J^T = I$. -/
theorem J_mul_transpose_J : J l R * (J l R)ᵀ = 1 := by
  rw [J_transpose, Matrix.mul_neg, J_squared, neg_neg]

/-- The skew form is orthogonal: $J^T J = I$. -/
theorem transpose_J_mul_J : (J l R)ᵀ * J l R = 1 := by
  rw [J_transpose, Matrix.neg_mul, J_squared, neg_neg]

/-- For matrices $X$, $Y$ on $l \oplus l$, $J X J^T = Y$ if and only if $JX = YJ$, since $J$ is
orthogonal. -/
private theorem J_mul_mul_transpose_J_eq_iff {X Y : Matrix (l ⊕ l) (l ⊕ l) R} :
    J l R * X * (J l R)ᵀ = Y ↔ J l R * X = Y * J l R := by
  constructor
  · rintro rfl
    rw [Matrix.mul_assoc (J l R * X), transpose_J_mul_J, Matrix.mul_one]
  · intro h
    rw [h, Matrix.mul_assoc, J_mul_transpose_J, Matrix.mul_one]

/-- For a symplectic matrix $S$, $J S^{-1} = S^T J$. -/
theorem J_mul_inv_of_mem_symplecticGroup {S : Matrix (l ⊕ l) (l ⊕ l) R}
    (hS : S ∈ symplecticGroup l R) : J l R * S⁻¹ = Sᵀ * J l R := by
  rw [SymplecticGroup.inv_eq_symplectic_inv S hS, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_neg, J_squared, neg_neg, Matrix.one_mul]

/-! ### Hamiltonian matrices -/

/-- A matrix $M$ on $l \oplus l$ over a commutative ring is **Hamiltonian** if $$J M J^T = -M^T.$$
-/
def IsHamiltonian (M : Matrix (l ⊕ l) (l ⊕ l) R) : Prop :=
  J l R * M * (J l R)ᵀ = -Mᵀ

/-- A matrix $M$ is Hamiltonian if and only if $JM = -M^T J$. -/
theorem isHamiltonian_iff_J_mul_eq {M : Matrix (l ⊕ l) (l ⊕ l) R} :
    M.IsHamiltonian ↔ J l R * M = -Mᵀ * J l R :=
  J_mul_mul_transpose_J_eq_iff

/-- A matrix $M$ is Hamiltonian if and only if $JM$ is symmetric. -/
theorem isHamiltonian_iff_isSymm_J_mul {M : Matrix (l ⊕ l) (l ⊕ l) R} :
    M.IsHamiltonian ↔ (J l R * M).IsSymm := by
  rw [isHamiltonian_iff_J_mul_eq, IsSymm, transpose_mul, J_transpose, Matrix.mul_neg,
    Matrix.neg_mul, eq_comm]

/-- A matrix $M$ is Hamiltonian if and only if it is in Mathlib's symplectic Lie algebra
`LieAlgebra.Symplectic.sp`, that is, if it is $J$-skew-adjoint: $M^T J = J(-M)$. -/
theorem isHamiltonian_iff_mem_sp {M : Matrix (l ⊕ l) (l ⊕ l) R} :
    M.IsHamiltonian ↔ M ∈ LieAlgebra.Symplectic.sp l R := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    isHamiltonian_iff_J_mul_eq, Matrix.mul_neg, Matrix.neg_mul]
  constructor <;> intro h <;> rw [h, neg_neg]

/-- Let $A, G, F, H$ be matrices on $l$. The block matrix
$\begin{bmatrix} A & G \\ F & H \end{bmatrix}$ is Hamiltonian if and only if $H = -A^T$,
$F^T = F$ and $G^T = G$. This is the block form of [golub2013matrix] §1.3.10. -/
theorem isHamiltonian_fromBlocks_iff {A G F H : Matrix l l R} :
    (fromBlocks A G F H).IsHamiltonian ↔ H = -Aᵀ ∧ Fᵀ = F ∧ Gᵀ = G := by
  rw [isHamiltonian_iff_isSymm_J_mul, J, fromBlocks_multiply, isSymm_fromBlocks_iff]
  simp only [Matrix.zero_mul, zero_add, Matrix.neg_mul, Matrix.one_mul, add_zero, isSymm_neg_iff]
  constructor
  · rintro ⟨hF, -, hA, hG⟩
    exact ⟨by rw [hA, neg_neg], hF, hG⟩
  · rintro ⟨rfl, hF, hG⟩
    exact ⟨hF, by rw [neg_neg, transpose_transpose], by rw [neg_neg], hG⟩

/-- The zero matrix is Hamiltonian. -/
theorem isHamiltonian_zero : (0 : Matrix (l ⊕ l) (l ⊕ l) R).IsHamiltonian :=
  isHamiltonian_iff_mem_sp.2 (zero_mem _)

namespace IsHamiltonian

variable {M N : Matrix (l ⊕ l) (l ⊕ l) R}

/-- The sum of two Hamiltonian matrices is Hamiltonian. -/
theorem add (hM : M.IsHamiltonian) (hN : N.IsHamiltonian) : (M + N).IsHamiltonian :=
  isHamiltonian_iff_mem_sp.2
    (add_mem (isHamiltonian_iff_mem_sp.1 hM) (isHamiltonian_iff_mem_sp.1 hN))

/-- The negative of a Hamiltonian matrix is Hamiltonian. -/
theorem neg (hM : M.IsHamiltonian) : (-M).IsHamiltonian :=
  isHamiltonian_iff_mem_sp.2 (neg_mem (isHamiltonian_iff_mem_sp.1 hM))

/-- A scalar multiple of a Hamiltonian matrix is Hamiltonian. -/
theorem smul (hM : M.IsHamiltonian) (c : R) : (c • M).IsHamiltonian :=
  isHamiltonian_iff_mem_sp.2 (SMulMemClass.smul_mem c (isHamiltonian_iff_mem_sp.1 hM))

/-- If $M$ and $N$ are Hamiltonian, then the commutator $MN - NM$ is Hamiltonian, so Hamiltonian
matrices form a Lie algebra. -/
theorem lie (hM : M.IsHamiltonian) (hN : N.IsHamiltonian) : (M * N - N * M).IsHamiltonian := by
  have h : ⁅M, N⁆ ∈ LieAlgebra.Symplectic.sp l R :=
    LieSubalgebra.lie_mem _ (isHamiltonian_iff_mem_sp.1 hM) (isHamiltonian_iff_mem_sp.1 hN)
  rw [Ring.lie_def] at h
  exact isHamiltonian_iff_mem_sp.2 h

/-- If $S$ is symplectic and $M$ is Hamiltonian, then $S^{-1} M S$ is Hamiltonian.

The matrix $J S^{-1} M S = S^T (JM) S$ is a congruence of the symmetric matrix $JM$. -/
theorem conj_symplectic {S : Matrix (l ⊕ l) (l ⊕ l) R} (hS : S ∈ symplecticGroup l R)
    (hM : M.IsHamiltonian) : (S⁻¹ * M * S).IsHamiltonian := by
  rw [isHamiltonian_iff_isSymm_J_mul] at hM ⊢
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, J_mul_inv_of_mem_symplecticGroup hS,
    Matrix.mul_assoc Sᵀ]
  exact hM.transpose_mul_mul S

/-- If $M$ is Hamiltonian, then $M^T = JMJ$.

Since $J^{-1} = -J$, this says $M^T = J^{-1} (-M) J$, so $M^T$ is similar to $-M$, and the
spectrum of a Hamiltonian matrix is symmetric about the imaginary axis. -/
theorem transpose_mul_J_eq (hM : M.IsHamiltonian) : Mᵀ = J l R * M * J l R := by
  rw [isHamiltonian_iff_J_mul_eq.1 hM, Matrix.mul_assoc, J_squared, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.mul_one, neg_neg]

end IsHamiltonian

/-! ### Skew-Hamiltonian matrices -/

/-- A matrix $N$ on $l \oplus l$ over a commutative ring is **skew-Hamiltonian** if $$J N J^T =
N^T.$$
-/
def IsSkewHamiltonian (N : Matrix (l ⊕ l) (l ⊕ l) R) : Prop :=
  J l R * N * (J l R)ᵀ = Nᵀ

/-- A matrix $N$ is skew-Hamiltonian if and only if $JN = N^T J$. -/
theorem isSkewHamiltonian_iff_J_mul_eq {N : Matrix (l ⊕ l) (l ⊕ l) R} :
    N.IsSkewHamiltonian ↔ J l R * N = Nᵀ * J l R :=
  J_mul_mul_transpose_J_eq_iff

/-- A matrix $N$ is skew-Hamiltonian if and only if $JN$ is skew-symmetric: $(JN)^T = -JN$. -/
theorem isSkewHamiltonian_iff_transpose_J_mul {N : Matrix (l ⊕ l) (l ⊕ l) R} :
    N.IsSkewHamiltonian ↔ (J l R * N)ᵀ = -(J l R * N) := by
  rw [isSkewHamiltonian_iff_J_mul_eq, transpose_mul, J_transpose, Matrix.mul_neg, neg_inj,
    eq_comm]

/-- A matrix $N$ is skew-Hamiltonian if and only if it is $J$-self-adjoint, $N^T J = JN$, that is,
if it is in Mathlib's `selfAdjointMatricesSubmodule (J l R)`. This is the skew form of
`Matrix.isHamiltonian_iff_mem_sp`. -/
theorem isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule {N : Matrix (l ⊕ l) (l ⊕ l) R} :
    N.IsSkewHamiltonian ↔ N ∈ selfAdjointMatricesSubmodule (J l R) := by
  rw [isSkewHamiltonian_iff_J_mul_eq, mem_selfAdjointMatricesSubmodule, Matrix.IsSelfAdjoint,
    Matrix.IsAdjointPair]
  exact eq_comm

/-- Let $A, G, F, H$ be matrices on $l$. The block matrix
$\begin{bmatrix} A & G \\ F & H \end{bmatrix}$ is skew-Hamiltonian if and only if $H = A^T$,
$F^T = -F$ and $G^T = -G$. This is the block form of [golub2013matrix] Figure 7.8.1. -/
theorem isSkewHamiltonian_fromBlocks_iff {A G F H : Matrix l l R} :
    (fromBlocks A G F H).IsSkewHamiltonian ↔ H = Aᵀ ∧ Fᵀ = -F ∧ Gᵀ = -G := by
  rw [isSkewHamiltonian_iff_transpose_J_mul, J, fromBlocks_multiply, fromBlocks_transpose,
    fromBlocks_neg, fromBlocks_inj]
  simp only [Matrix.zero_mul, zero_add, Matrix.neg_mul, Matrix.one_mul, add_zero, transpose_neg,
    neg_neg, neg_inj]
  constructor
  · rintro ⟨hF, hA, -, hG⟩
    exact ⟨hA.symm, neg_eq_iff_eq_neg.1 hF, hG⟩
  · rintro ⟨rfl, hF, hG⟩
    exact ⟨by rw [hF, neg_neg], rfl, transpose_transpose A, hG⟩

/-- The zero matrix is skew-Hamiltonian. -/
theorem isSkewHamiltonian_zero : (0 : Matrix (l ⊕ l) (l ⊕ l) R).IsSkewHamiltonian :=
  isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule.2 (zero_mem _)

/-- The identity matrix is skew-Hamiltonian. -/
theorem isSkewHamiltonian_one : (1 : Matrix (l ⊕ l) (l ⊕ l) R).IsSkewHamiltonian := by
  rw [isSkewHamiltonian_iff_J_mul_eq, transpose_one, Matrix.mul_one, Matrix.one_mul]

namespace IsSkewHamiltonian

variable {M N : Matrix (l ⊕ l) (l ⊕ l) R}

/-- The sum of two skew-Hamiltonian matrices is skew-Hamiltonian. -/
theorem add (hM : M.IsSkewHamiltonian) (hN : N.IsSkewHamiltonian) :
    (M + N).IsSkewHamiltonian :=
  isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule.2
    (add_mem (isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule.1 hM)
      (isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule.1 hN))

/-- The negative of a skew-Hamiltonian matrix is skew-Hamiltonian. -/
theorem neg (hN : N.IsSkewHamiltonian) : (-N).IsSkewHamiltonian :=
  isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule.2
    (neg_mem (isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule.1 hN))

/-- A scalar multiple of a skew-Hamiltonian matrix is skew-Hamiltonian. -/
theorem smul (hN : N.IsSkewHamiltonian) (c : R) : (c • N).IsSkewHamiltonian :=
  isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule.2
    (SMulMemClass.smul_mem c (isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule.1 hN))

/-- If $S$ is symplectic and $N$ is skew-Hamiltonian, then $S^{-1} N S$ is skew-Hamiltonian.

The matrix $J S^{-1} N S = S^T (JN) S$ is a congruence of the skew-symmetric matrix $JN$. -/
theorem conj_symplectic {S : Matrix (l ⊕ l) (l ⊕ l) R} (hS : S ∈ symplecticGroup l R)
    (hN : N.IsSkewHamiltonian) : (S⁻¹ * N * S).IsSkewHamiltonian := by
  rw [isSkewHamiltonian_iff_transpose_J_mul] at hN ⊢
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, J_mul_inv_of_mem_symplecticGroup hS,
    Matrix.mul_assoc Sᵀ]
  exact transpose_transpose_mul_mul_of_transpose_eq_neg hN S

end IsSkewHamiltonian

/-- If $M$ is Hamiltonian, then $M^2$ is skew-Hamiltonian ([golub2013matrix] §7.8.1).

The proof is $J M^2 = -M^T J M = M^T M^T J = (M^2)^T J$. -/
theorem IsHamiltonian.isSkewHamiltonian_mul_self {M : Matrix (l ⊕ l) (l ⊕ l) R}
    (hM : M.IsHamiltonian) : (M * M).IsSkewHamiltonian := by
  have hJ := isHamiltonian_iff_J_mul_eq.1 hM
  rw [isSkewHamiltonian_iff_J_mul_eq, transpose_mul, ← Matrix.mul_assoc, hJ,
    Matrix.mul_assoc (-Mᵀ), hJ]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

/-! ### Orthogonal symplectic matrices -/

/-- A matrix $Q$ on $l \oplus l$ commutes with $J$ if and only if $Q = \begin{bmatrix} Q_1 & Q_2 \\
-Q_2 & Q_1 \end{bmatrix}$ for some matrices $Q_1$, $Q_2$ on $l$. -/
theorem commute_J_iff {Q : Matrix (l ⊕ l) (l ⊕ l) R} :
    Commute (J l R) Q ↔ ∃ Q₁ Q₂ : Matrix l l R, Q = fromBlocks Q₁ Q₂ (-Q₂) Q₁ := by
  rw [← fromBlocks_toBlocks Q, Commute, SemiconjBy, J, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj]
  simp only [Matrix.zero_mul, zero_add, Matrix.neg_mul, Matrix.one_mul, add_zero, Matrix.mul_zero,
    Matrix.mul_neg, Matrix.mul_one, neg_inj, fromBlocks_inj]
  constructor
  · rintro ⟨h₁, h₂, -, -⟩
    exact ⟨Q.toBlocks₁₁, Q.toBlocks₁₂, rfl, rfl, neg_eq_iff_eq_neg.1 h₁, h₂⟩
  · rintro ⟨Q₁, Q₂, h₁₁, h₁₂, h₂₁, h₂₂⟩
    rw [h₁₁, h₁₂, h₂₁, h₂₂]
    exact ⟨neg_neg _, rfl, rfl, (neg_neg _).symm⟩

/-- An orthogonal matrix $Q$ on $l \oplus l$ is symplectic if and only if it commutes with $J$. -/
theorem mem_symplecticGroup_iff_commute_J_of_mem_orthogonalGroup {Q : Matrix (l ⊕ l) (l ⊕ l) R}
    (hQ : Q ∈ orthogonalGroup (l ⊕ l) R) : Q ∈ symplecticGroup l R ↔ Commute (J l R) Q := by
  rw [SymplecticGroup.mem_iff, Commute, SemiconjBy]
  have h₁ := (mem_orthogonalGroup_iff (l ⊕ l) R).1 hQ
  have h₂ := (mem_orthogonalGroup_iff' (l ⊕ l) R).1 hQ
  constructor
  · intro h
    calc J l R * Q = Q * J l R * Qᵀ * Q := by rw [h]
      _ = Q * J l R := by rw [Matrix.mul_assoc, h₂, Matrix.mul_one]
  · intro h
    rw [← h, Matrix.mul_assoc, h₁, Matrix.mul_one]

/-- The block matrix $\begin{bmatrix} Q_1 & Q_2 \\ -Q_2 & Q_1 \end{bmatrix}$ is orthogonal if and
only if $Q_1^T Q_2$ is symmetric and $Q_1^T Q_1 + Q_2^T Q_2 = I$. -/
theorem fromBlocks_mem_orthogonalGroup_iff {Q₁ Q₂ : Matrix l l R} :
    fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∈ orthogonalGroup (l ⊕ l) R ↔
      (Q₁ᵀ * Q₂).IsSymm ∧ Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 := by
  rw [mem_orthogonalGroup_iff', fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj, IsSymm, transpose_mul, transpose_transpose]
  simp only [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← sub_eq_add_neg,
    sub_eq_zero]
  constructor
  · rintro ⟨h₁, h₂, -, -⟩
    exact ⟨h₂.symm, h₁⟩
  · rintro ⟨hs, h⟩
    exact ⟨h, hs.symm, hs, by rw [add_comm, h]⟩

/-- A matrix $Q$ on $l \oplus l$ is orthogonal and symplectic if and only if $$Q = \begin{bmatrix}
Q_1 & Q_2 \\ -Q_2 & Q_1 \end{bmatrix}$$ for some matrices $Q_1$, $Q_2$ on $l$ with $Q_1^T Q_2$
symmetric and $Q_1^T Q_1 + Q_2^T Q_2 = I$. This is [golub2013matrix] Figure 7.8.1 and P2.5.4. -/
theorem mem_orthogonalGroup_symplecticGroup_iff {Q : Matrix (l ⊕ l) (l ⊕ l) R} :
    Q ∈ orthogonalGroup (l ⊕ l) R ∧ Q ∈ symplecticGroup l R ↔
      ∃ Q₁ Q₂ : Matrix l l R, Q = fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∧
        (Q₁ᵀ * Q₂).IsSymm ∧ Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 := by
  constructor
  · rintro ⟨hO, hS⟩
    obtain ⟨Q₁, Q₂, rfl⟩ := commute_J_iff.1
      ((mem_symplecticGroup_iff_commute_J_of_mem_orthogonalGroup hO).1 hS)
    exact ⟨Q₁, Q₂, rfl, fromBlocks_mem_orthogonalGroup_iff.1 hO⟩
  · rintro ⟨Q₁, Q₂, rfl, h⟩
    have hO := fromBlocks_mem_orthogonalGroup_iff.2 h
    exact ⟨hO, (mem_symplecticGroup_iff_commute_J_of_mem_orthogonalGroup hO).2
      (commute_J_iff.2 ⟨Q₁, Q₂, rfl⟩)⟩

/-! ### The orthogonal symplectic group -/

variable (l R) in
/-- The **orthogonal symplectic** matrices $O(2n) \cap Sp(2n)$ on $l \oplus l$, the matrices that
are both orthogonal and symplectic ([golub2013matrix] §7.8.1). They are the transformations of
the structure-preserving algorithms for the Hamiltonian eigenvalue problem.

This is a submonoid of the matrices on $l \oplus l$, the intersection of
`Matrix.orthogonalGroup` and `Matrix.symplecticGroup`. -/
def orthoSymplecticGroup : Submonoid (Matrix (l ⊕ l) (l ⊕ l) R) :=
  orthogonalGroup (l ⊕ l) R ⊓ symplecticGroup l R

/-- A matrix is in `Matrix.orthoSymplecticGroup` if and only if it is orthogonal and symplectic. -/
theorem mem_orthoSymplecticGroup_iff {Q : Matrix (l ⊕ l) (l ⊕ l) R} :
    Q ∈ orthoSymplecticGroup l R ↔ Q ∈ orthogonalGroup (l ⊕ l) R ∧ Q ∈ symplecticGroup l R :=
  Iff.rfl

namespace OrthoSymplecticGroup

variable {Q : Matrix (l ⊕ l) (l ⊕ l) R} (hQ : Q ∈ orthoSymplecticGroup l R)
include hQ

/-- An orthogonal symplectic matrix is orthogonal. -/
theorem mem_orthogonalGroup : Q ∈ orthogonalGroup (l ⊕ l) R := hQ.1

/-- An orthogonal symplectic matrix is symplectic. -/
theorem mem_symplecticGroup : Q ∈ symplecticGroup l R := hQ.2

/-- An orthogonal symplectic matrix $Q$ satisfies $Q^T Q = I$. -/
theorem transpose_mul_self : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' (l ⊕ l) R).1 hQ.1

/-- An orthogonal symplectic matrix $Q$ satisfies $Q Q^T = I$. -/
theorem mul_transpose_self : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff (l ⊕ l) R).1 hQ.1

/-- The inverse of an orthogonal symplectic matrix is its transpose. -/
theorem inv_eq_transpose : Q⁻¹ = Qᵀ := inv_eq_left_inv (transpose_mul_self hQ)

/-- The transpose of an orthogonal symplectic matrix is orthogonal symplectic. -/
theorem transpose_mem : Qᵀ ∈ orthoSymplecticGroup l R :=
  ⟨(mem_orthogonalGroup_iff (l ⊕ l) R).2 (by rw [transpose_transpose, transpose_mul_self hQ]),
    SymplecticGroup.transpose_mem hQ.2⟩

end OrthoSymplecticGroup

/-- If $M$ is Hamiltonian and $Q$ is orthogonal symplectic, then $Q^T M Q$ is Hamiltonian. -/
theorem IsHamiltonian.transpose_mul_mul_of_mem_orthoSymplecticGroup
    {M Q : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M.IsHamiltonian)
    (hQ : Q ∈ orthoSymplecticGroup l R) : (Qᵀ * M * Q).IsHamiltonian := by
  rw [← OrthoSymplecticGroup.inv_eq_transpose hQ]
  exact hM.conj_symplectic hQ.2

/-- If $N$ is skew-Hamiltonian and $Q$ is orthogonal symplectic, then $Q^T N Q$ is skew-Hamiltonian.
-/
theorem IsSkewHamiltonian.transpose_mul_mul_of_mem_orthoSymplecticGroup
    {N Q : Matrix (l ⊕ l) (l ⊕ l) R} (hN : N.IsSkewHamiltonian)
    (hQ : Q ∈ orthoSymplecticGroup l R) : (Qᵀ * N * Q).IsSkewHamiltonian := by
  rw [← OrthoSymplecticGroup.inv_eq_transpose hQ]
  exact hN.conj_symplectic hQ.2

/-- A matrix $Q$ is orthogonal symplectic if and only if $Q = \begin{bmatrix} Q_1 & Q_2 \\ -Q_2 &
Q_1 \end{bmatrix}$ with $Q_1^T Q_2$ symmetric and $Q_1^T Q_1 + Q_2^T Q_2 = I$. This is
`Matrix.mem_orthogonalGroup_symplecticGroup_iff` for `Matrix.orthoSymplecticGroup`. -/
theorem mem_orthoSymplecticGroup_iff_fromBlocks {Q : Matrix (l ⊕ l) (l ⊕ l) R} :
    Q ∈ orthoSymplecticGroup l R ↔
      ∃ Q₁ Q₂ : Matrix l l R, Q = fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∧
        (Q₁ᵀ * Q₂).IsSymm ∧ Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 :=
  mem_orthogonalGroup_symplecticGroup_iff

/-! ### Isotropic families -/

/-- Let $K$ be a field and let $X_0$ be a matrix with rows indexed by $l \oplus l$ and columns
indexed by a finite type $k$. If $X_0^T X_0 = I$ and $X_0^T J X_0 = 0$, then $|k| \le |l|$: **an
orthonormal isotropic family in $K^{l \oplus l}$ has at most $|l|$ members**.

The columns of $X_0$ and of $J X_0$ together are linearly independent and mutually orthogonal,
so $2|k| \le 2|l|$. -/
theorem card_le_of_transpose_mul_J_mul_eq_zero {K k : Type*} [Field K] [Fintype k] [DecidableEq k]
    {X₀ : Matrix (l ⊕ l) k K} (h1 : X₀ᵀ * X₀ = 1) (h2 : X₀ᵀ * J l K * X₀ = 0) :
    Fintype.card k ≤ Fintype.card l := by
  set Y := J l K * X₀
  have hY : Yᵀ * Y = 1 := by
    rw [transpose_mul, J_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (-J l K),
      Matrix.neg_mul, J_squared, neg_neg, Matrix.one_mul, h1]
  have hrX : Fintype.card k ≤ X₀ᵀ.rank := by
    have := rank_mul_le_left X₀ᵀ X₀
    rwa [h1, rank_one] at this
  have hrY : Fintype.card k ≤ Y.rank := by
    have := rank_mul_le_left Yᵀ Y
    rwa [hY, rank_one, rank_transpose] at this
  have h0 : X₀ᵀ * Y = 0 := by rw [← Matrix.mul_assoc, h2]
  have hle : LinearMap.range Y.mulVecLin ≤ LinearMap.ker X₀ᵀ.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, h0, zero_mulVec]
  have hker := LinearMap.finrank_range_add_finrank_ker X₀ᵀ.mulVecLin
  have hrY' : Y.rank ≤ Module.finrank K (LinearMap.ker X₀ᵀ.mulVecLin) :=
    Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at hker
  change X₀ᵀ.rank + _ = _ at hker
  omega

end Matrix
