/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.SymplecticGroup`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Numlib.LinearAlgebra.Matrix.Symmetric

/-!
# Hamiltonian and skew-Hamiltonian matrices

Mathlib has the canonical skew form `Matrix.J l R = fromBlocks 0 (-1) 1 0` on `l ⊕ l`, the
symplectic group `Matrix.symplecticGroup l R` (`A J Aᵀ = J`), and the symplectic Lie algebra
`LieAlgebra.Symplectic.sp l R` of `J`-skew-adjoint matrices — which *are* the Hamiltonian matrices,
under a name and in a form no numerical text uses. This file gives the predicate its numerical name
in the textbook form `J M Jᵀ = -Mᵀ` (`Matrix.IsHamiltonian`), its two characterizations (`J M`
symmetric; the block form `[A G; F -Aᵀ]` with `F`, `G` symmetric), and the facts the Hamiltonian
eigenvalue problem needs: Hamiltonian matrices form a Lie algebra, symplectic similarity preserves
them, and `Mᵀ` is similar to `-M`.

Beside them, the rest of the structured classes of the Hamiltonian eigenvalue problem:
*skew-Hamiltonian* matrices (`J N Jᵀ = Nᵀ`, i.e. `J N` skew-symmetric; block form `[A G; F Aᵀ]` with
`F`, `G` skew-symmetric), which symplectic similarity also preserves and which contain the squares
of Hamiltonian matrices, and the orthogonal symplectic matrices, which are exactly the block
matrices `[Q₁ Q₂; -Q₂ Q₁]` with `Q₁ᵀ Q₂` symmetric and `Q₁ᵀ Q₁ + Q₂ᵀ Q₂ = I`.

The sign of `J` is immaterial: [golub2013matrix] writes `J = [0 I; -I 0] = -Matrix.J`, and both the
conditions `J M Jᵀ = -Mᵀ`, `J N Jᵀ = Nᵀ` and the symplectic condition `S J Sᵀ = J` are invariant
under `J ↦ -J`.

## Main definitions

* `Matrix.IsHamiltonian`, `Matrix.IsSkewHamiltonian`, `Matrix.orthoSymplecticGroup`.

## Main statements

* `Matrix.isHamiltonian_iff_isSymm_J_mul`, `Matrix.isHamiltonian_iff_mem_sp`,
  `Matrix.isHamiltonian_fromBlocks_iff`, and the skew-Hamiltonian twins
  (`Matrix.isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule`: the `J`-self-adjoint matrices).
* `Matrix.IsHamiltonian.conj_symplectic`, `Matrix.IsSkewHamiltonian.conj_symplectic`.
* `Matrix.IsHamiltonian.transpose_mul_J_eq`: `Mᵀ = J M J`, so `Mᵀ` is similar to `-M`.
* `Matrix.mem_orthogonalGroup_symplecticGroup_iff`: the block form of orthogonal symplectic
  matrices, which form the submonoid `Matrix.orthoSymplecticGroup`; orthogonal symplectic
  similarity `Qᵀ M Q` preserves both structures
  (`Matrix.IsHamiltonian.transpose_mul_mul_of_mem_orthoSymplecticGroup`).

## References

* [golub2013matrix], §1.3.10, §7.8.1 (Figure 7.8.1).
-/

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix

variable {l R : Type*} [Fintype l] [CommRing R]

/-- A congruence `Sᵀ X S` of a skew-symmetric matrix is skew-symmetric. -/
private theorem transpose_transpose_mul_mul_of_transpose_eq_neg {X : Matrix (l ⊕ l) (l ⊕ l) R}
    (hX : Xᵀ = -X) (S : Matrix (l ⊕ l) (l ⊕ l) R) : (Sᵀ * X * S)ᵀ = -(Sᵀ * X * S) := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hX]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

variable [DecidableEq l]

/-- `J Jᵀ = I`. -/
private theorem J_mul_transpose_J : J l R * (J l R)ᵀ = 1 := by
  rw [J_transpose, Matrix.mul_neg, J_squared, neg_neg]

/-- `Jᵀ J = I`. -/
private theorem transpose_J_mul_J : (J l R)ᵀ * J l R = 1 := by
  rw [J_transpose, Matrix.neg_mul, J_squared, neg_neg]

/-- `J X Jᵀ = Y ↔ J X = Y J`, since `J` is orthogonal. -/
private theorem J_mul_mul_transpose_J_eq_iff {X Y : Matrix (l ⊕ l) (l ⊕ l) R} :
    J l R * X * (J l R)ᵀ = Y ↔ J l R * X = Y * J l R := by
  constructor
  · rintro rfl
    rw [Matrix.mul_assoc (J l R * X), transpose_J_mul_J, Matrix.mul_one]
  · intro h
    rw [h, Matrix.mul_assoc, J_mul_transpose_J, Matrix.mul_one]

/-- For a symplectic `S`, `J S⁻¹ = Sᵀ J`. -/
private theorem J_mul_inv_of_mem_symplecticGroup {S : Matrix (l ⊕ l) (l ⊕ l) R}
    (hS : S ∈ symplecticGroup l R) : J l R * S⁻¹ = Sᵀ * J l R := by
  rw [SymplecticGroup.inv_eq_symplectic_inv S hS, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_neg, J_squared, neg_neg, Matrix.one_mul]

/-! ### Hamiltonian matrices -/

/-- A matrix `M` on `l ⊕ l` is *Hamiltonian* if `J M Jᵀ = -Mᵀ`. -/
def IsHamiltonian (M : Matrix (l ⊕ l) (l ⊕ l) R) : Prop :=
  J l R * M * (J l R)ᵀ = -Mᵀ

/-- `M` is Hamiltonian iff `J M = -Mᵀ J`. -/
theorem isHamiltonian_iff_J_mul_eq {M : Matrix (l ⊕ l) (l ⊕ l) R} :
    M.IsHamiltonian ↔ J l R * M = -Mᵀ * J l R :=
  J_mul_mul_transpose_J_eq_iff

/-- `M` is Hamiltonian iff `J M` is symmetric. -/
theorem isHamiltonian_iff_isSymm_J_mul {M : Matrix (l ⊕ l) (l ⊕ l) R} :
    M.IsHamiltonian ↔ (J l R * M).IsSymm := by
  rw [isHamiltonian_iff_J_mul_eq, IsSymm, transpose_mul, J_transpose, Matrix.mul_neg,
    Matrix.neg_mul, eq_comm]

/-- The Hamiltonian matrices are Mathlib's symplectic Lie algebra `LieAlgebra.Symplectic.sp`, the
`J`-skew-adjoint matrices `Mᵀ J = J (-M)`. -/
theorem isHamiltonian_iff_mem_sp {M : Matrix (l ⊕ l) (l ⊕ l) R} :
    M.IsHamiltonian ↔ M ∈ LieAlgebra.Symplectic.sp l R := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    isHamiltonian_iff_J_mul_eq, Matrix.mul_neg, Matrix.neg_mul]
  constructor <;> intro h <;> rw [h, neg_neg]

/-- The block form ([golub2013matrix] §1.3.10): `[A G; F H]` is Hamiltonian iff `H = -Aᵀ` and
`F`, `G` are symmetric. -/
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

/-- A sum of Hamiltonian matrices is Hamiltonian. -/
theorem add (hM : M.IsHamiltonian) (hN : N.IsHamiltonian) : (M + N).IsHamiltonian :=
  isHamiltonian_iff_mem_sp.2
    (add_mem (isHamiltonian_iff_mem_sp.1 hM) (isHamiltonian_iff_mem_sp.1 hN))

/-- The negative of a Hamiltonian matrix is Hamiltonian. -/
theorem neg (hM : M.IsHamiltonian) : (-M).IsHamiltonian :=
  isHamiltonian_iff_mem_sp.2 (neg_mem (isHamiltonian_iff_mem_sp.1 hM))

/-- A scalar multiple of a Hamiltonian matrix is Hamiltonian. -/
theorem smul (hM : M.IsHamiltonian) (c : R) : (c • M).IsHamiltonian :=
  isHamiltonian_iff_mem_sp.2 (SMulMemClass.smul_mem c (isHamiltonian_iff_mem_sp.1 hM))

/-- Hamiltonian matrices form a Lie algebra: the commutator of two Hamiltonian matrices is
Hamiltonian. -/
theorem lie (hM : M.IsHamiltonian) (hN : N.IsHamiltonian) : (M * N - N * M).IsHamiltonian := by
  have h : ⁅M, N⁆ ∈ LieAlgebra.Symplectic.sp l R :=
    LieSubalgebra.lie_mem _ (isHamiltonian_iff_mem_sp.1 hM) (isHamiltonian_iff_mem_sp.1 hN)
  rw [Ring.lie_def] at h
  exact isHamiltonian_iff_mem_sp.2 h

/-- Symplectic similarity preserves Hamiltonian structure: `J S⁻¹ M S = Sᵀ (J M) S` is a congruence
of the symmetric `J M`. -/
theorem conj_symplectic {S : Matrix (l ⊕ l) (l ⊕ l) R} (hS : S ∈ symplecticGroup l R)
    (hM : M.IsHamiltonian) : (S⁻¹ * M * S).IsHamiltonian := by
  rw [isHamiltonian_iff_isSymm_J_mul] at hM ⊢
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, J_mul_inv_of_mem_symplecticGroup hS,
    Matrix.mul_assoc Sᵀ]
  exact hM.transpose_mul_mul S

/-- `Mᵀ = J M J` for a Hamiltonian `M`; since `J⁻¹ = -J`, `Mᵀ = J⁻¹ (-M) J` is similar to `-M`, so
the spectrum of a Hamiltonian matrix is symmetric about the imaginary axis. -/
theorem transpose_mul_J_eq (hM : M.IsHamiltonian) : Mᵀ = J l R * M * J l R := by
  rw [isHamiltonian_iff_J_mul_eq.1 hM, Matrix.mul_assoc, J_squared, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.mul_one, neg_neg]

end IsHamiltonian

/-! ### Skew-Hamiltonian matrices -/

/-- A matrix `N` on `l ⊕ l` is *skew-Hamiltonian* if `J N Jᵀ = Nᵀ`. -/
def IsSkewHamiltonian (N : Matrix (l ⊕ l) (l ⊕ l) R) : Prop :=
  J l R * N * (J l R)ᵀ = Nᵀ

/-- `N` is skew-Hamiltonian iff `J N = Nᵀ J`. -/
theorem isSkewHamiltonian_iff_J_mul_eq {N : Matrix (l ⊕ l) (l ⊕ l) R} :
    N.IsSkewHamiltonian ↔ J l R * N = Nᵀ * J l R :=
  J_mul_mul_transpose_J_eq_iff

/-- `N` is skew-Hamiltonian iff `J N` is skew-symmetric. -/
theorem isSkewHamiltonian_iff_transpose_J_mul {N : Matrix (l ⊕ l) (l ⊕ l) R} :
    N.IsSkewHamiltonian ↔ (J l R * N)ᵀ = -(J l R * N) := by
  rw [isSkewHamiltonian_iff_J_mul_eq, transpose_mul, J_transpose, Matrix.mul_neg, neg_inj,
    eq_comm]

/-- The skew-Hamiltonian matrices are the `J`-self-adjoint matrices `Nᵀ J = J N`, Mathlib's
`selfAdjointMatricesSubmodule (J l R)`. The twin of `Matrix.isHamiltonian_iff_mem_sp`. -/
theorem isSkewHamiltonian_iff_mem_selfAdjointMatricesSubmodule {N : Matrix (l ⊕ l) (l ⊕ l) R} :
    N.IsSkewHamiltonian ↔ N ∈ selfAdjointMatricesSubmodule (J l R) := by
  rw [isSkewHamiltonian_iff_J_mul_eq, mem_selfAdjointMatricesSubmodule, Matrix.IsSelfAdjoint,
    Matrix.IsAdjointPair]
  exact eq_comm

/-- The block form ([golub2013matrix] Figure 7.8.1): `[A G; F H]` is skew-Hamiltonian iff `H = Aᵀ`
and `F`, `G` are skew-symmetric. -/
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

/-- A sum of skew-Hamiltonian matrices is skew-Hamiltonian. -/
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

/-- Symplectic similarity preserves skew-Hamiltonian structure: `J S⁻¹ N S = Sᵀ (J N) S` is a
congruence of the skew-symmetric `J N`. -/
theorem conj_symplectic {S : Matrix (l ⊕ l) (l ⊕ l) R} (hS : S ∈ symplecticGroup l R)
    (hN : N.IsSkewHamiltonian) : (S⁻¹ * N * S).IsSkewHamiltonian := by
  rw [isSkewHamiltonian_iff_transpose_J_mul] at hN ⊢
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, J_mul_inv_of_mem_symplecticGroup hS,
    Matrix.mul_assoc Sᵀ]
  exact transpose_transpose_mul_mul_of_transpose_eq_neg hN S

end IsSkewHamiltonian

/-- The square of a Hamiltonian matrix is skew-Hamiltonian ([golub2013matrix] §7.8.1):
`J M² = -Mᵀ J M = Mᵀ Mᵀ J = (M²)ᵀ J`. -/
theorem IsHamiltonian.isSkewHamiltonian_mul_self {M : Matrix (l ⊕ l) (l ⊕ l) R}
    (hM : M.IsHamiltonian) : (M * M).IsSkewHamiltonian := by
  have hJ := isHamiltonian_iff_J_mul_eq.1 hM
  rw [isSkewHamiltonian_iff_J_mul_eq, transpose_mul, ← Matrix.mul_assoc, hJ,
    Matrix.mul_assoc (-Mᵀ), hJ]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

/-! ### Orthogonal symplectic matrices -/

/-- A matrix commutes with `J` iff it has the block form `[Q₁ Q₂; -Q₂ Q₁]`. -/
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

/-- An orthogonal matrix is symplectic iff it commutes with `J`. -/
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

/-- `[Q₁ Q₂; -Q₂ Q₁]` is orthogonal iff `Q₁ᵀ Q₂` is symmetric and `Q₁ᵀ Q₁ + Q₂ᵀ Q₂ = I`. -/
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

/-- The orthogonal symplectic matrices ([golub2013matrix] Figure 7.8.1, P2.5.4) are exactly the
block matrices `[Q₁ Q₂; -Q₂ Q₁]` with `Q₁ᵀ Q₂` symmetric and `Q₁ᵀ Q₁ + Q₂ᵀ Q₂ = I`. -/
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
/-- The *orthogonal symplectic* matrices `O(2n) ∩ Sp(2n)` ([golub2013matrix] §7.8.1), the
transformations of the structure-preserving Hamiltonian eigenvalue algorithms. -/
def orthoSymplecticGroup : Submonoid (Matrix (l ⊕ l) (l ⊕ l) R) :=
  orthogonalGroup (l ⊕ l) R ⊓ symplecticGroup l R

/-- Membership in `Matrix.orthoSymplecticGroup` is membership in both groups. -/
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

/-- `Qᵀ Q = 1`. -/
theorem transpose_mul_self : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' (l ⊕ l) R).1 hQ.1

/-- `Q Qᵀ = 1`. -/
theorem mul_transpose_self : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff (l ⊕ l) R).1 hQ.1

/-- The inverse of an orthogonal symplectic matrix is its transpose. -/
theorem inv_eq_transpose : Q⁻¹ = Qᵀ := inv_eq_left_inv (transpose_mul_self hQ)

/-- The transpose of an orthogonal symplectic matrix is orthogonal symplectic. -/
theorem transpose_mem : Qᵀ ∈ orthoSymplecticGroup l R :=
  ⟨(mem_orthogonalGroup_iff (l ⊕ l) R).2 (by rw [transpose_transpose, transpose_mul_self hQ]),
    SymplecticGroup.transpose_mem hQ.2⟩

end OrthoSymplecticGroup

/-- Orthogonal symplectic similarity `Qᵀ M Q` preserves Hamiltonian structure. -/
theorem IsHamiltonian.transpose_mul_mul_of_mem_orthoSymplecticGroup
    {M Q : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M.IsHamiltonian)
    (hQ : Q ∈ orthoSymplecticGroup l R) : (Qᵀ * M * Q).IsHamiltonian := by
  rw [← OrthoSymplecticGroup.inv_eq_transpose hQ]
  exact hM.conj_symplectic hQ.2

/-- Orthogonal symplectic similarity `Qᵀ N Q` preserves skew-Hamiltonian structure. -/
theorem IsSkewHamiltonian.transpose_mul_mul_of_mem_orthoSymplecticGroup
    {N Q : Matrix (l ⊕ l) (l ⊕ l) R} (hN : N.IsSkewHamiltonian)
    (hQ : Q ∈ orthoSymplecticGroup l R) : (Qᵀ * N * Q).IsSkewHamiltonian := by
  rw [← OrthoSymplecticGroup.inv_eq_transpose hQ]
  exact hN.conj_symplectic hQ.2

/-- The block form of the orthogonal symplectic matrices,
`Matrix.mem_orthogonalGroup_symplecticGroup_iff` for `Matrix.orthoSymplecticGroup`. -/
theorem mem_orthoSymplecticGroup_iff_fromBlocks {Q : Matrix (l ⊕ l) (l ⊕ l) R} :
    Q ∈ orthoSymplecticGroup l R ↔
      ∃ Q₁ Q₂ : Matrix l l R, Q = fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∧
        (Q₁ᵀ * Q₂).IsSymm ∧ Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 :=
  mem_orthogonalGroup_symplecticGroup_iff

end Matrix
