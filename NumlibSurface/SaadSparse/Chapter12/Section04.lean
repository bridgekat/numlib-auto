import Mathlib.LinearAlgebra.Matrix.IsDiag
import Numlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Saad §12.4: multicolouring and the red–black reduced system

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §12.4.

The section is implementation description — a greedy colouring algorithm and the parallel sweeps a
colouring makes possible — with two pieces of algebra in it.

* §12.4.1.  A 2-colouring of the adjacency graph of `A`, "no two adjacent nodes share a colour",
  makes each *same-colour* submatrix of `A` a diagonal matrix, so that ordering the red unknowns
  before the black ones puts the system in the form (12.18), `(D₁ F; E D₂)(x₁; x₂) = (b₁; b₂)`
  with `D₁` and `D₂` diagonal.  That is `isDiag_submatrix_of_coloring`; which nodes receive which
  colour is a graph problem with no claim attached, and Algorithm 12.3 is a listing.
* §12.4.2.  Eliminating the red unknowns from (12.18) leaves the *reduced system*
  `(D₂ - E D₁⁻¹ F) x₂ = b₂ - E D₁⁻¹ b₁` on the black unknowns alone.  Its matrix is the Schur
  complement of `Numlib/LinearAlgebra/Matrix/SchurComplement`, and `equation_12_18` is the
  equivalence of the reduced system with the full one.  Nothing in it uses that `D₁` is diagonal:
  as Saad says, the same elimination "is more often employed when `D₁` is not diagonal, such as in
  domain decomposition methods", where it is `SaadSparse.Chapter14.blockGaussianElimination_eq`.

Saad's block naming in (12.18) puts `F` in the `(1,2)` corner and `E` in the `(2,1)` corner, the
opposite of the §14.2 partitioning; the statements below keep the book's letters.
-/

open Matrix

namespace SaadSparse.Chapter12

/-! ### §12.4.1: what a 2-colouring gives -/

/-- **§12.4.1**: if no two *distinct* nodes of the same colour are coupled in `A`, then the
submatrix of `A` on the nodes of one colour is a diagonal matrix.  Applied to the two colours of a
red–black ordering, this is the statement that (12.18) has diagonal `D₁` and `D₂`. -/
theorem isDiag_submatrix_of_coloring {V R : Type*} [Zero R] (A : Matrix V V R)
    (c : V → Bool) (hc : ∀ i j, i ≠ j → c i = c j → A i j = 0) (p : Bool) :
    (A.submatrix (Subtype.val : {i // c i = p} → V) Subtype.val).IsDiag := fun i j hij =>
  hc _ _ (fun h => hij (Subtype.ext h)) (i.2.trans j.2.symm)

/-! ### §12.4.2: the reduced system -/

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
variable {D₁ : Matrix m m R} {F : Matrix m n R} {E : Matrix n m R} {D₂ : Matrix n n R}

/-- **(12.18) and the reduced system of §12.4.2**: for a nonsingular `D₁`, the pair `(x₁, x₂)`
solves the red–black system `(D₁ F; E D₂)(x₁; x₂) = (b₁; b₂)` if and only if the black unknown
`x₂` solves the reduced system `(D₂ - E D₁⁻¹ F) x₂ = b₂ - E D₁⁻¹ b₁`, whose matrix is the Schur
complement, and the red unknown is recovered from it by `x₁ = D₁⁻¹(b₁ - F x₂)`. -/
theorem equation_12_18 (hD₁ : IsUnit D₁) (b₁ : m → R) (b₂ : n → R) (x₁ : m → R) (x₂ : n → R) :
    fromBlocks D₁ F E D₂ *ᵥ Sum.elim x₁ x₂ = Sum.elim b₁ b₂
      ↔ (fromBlocks D₁ F E D₂).schurComplement *ᵥ x₂ = b₂ - E *ᵥ (D₁⁻¹ *ᵥ b₁)
          ∧ x₁ = D₁⁻¹ *ᵥ (b₁ - F *ᵥ x₂) := by
  have hdet : IsUnit D₁.det := (Matrix.isUnit_iff_isUnit_det _).1 hD₁
  have hDD : D₁ * D₁⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hDD' : D₁⁻¹ * D₁ = 1 := Matrix.nonsing_inv_mul _ hdet
  have helim : ∀ (u : m → R) (v : n → R),
      Sum.elim u v = Sum.elim b₁ b₂ ↔ u = b₁ ∧ v = b₂ := by
    refine fun u v => ⟨fun h => ⟨funext fun i => congrFun h (Sum.inl i),
      funext fun i => congrFun h (Sum.inr i)⟩, ?_⟩
    rintro ⟨rfl, rfl⟩
    rfl
  have hred : D₁ *ᵥ x₁ + F *ᵥ x₂ = b₁ ↔ x₁ = D₁⁻¹ *ᵥ (b₁ - F *ᵥ x₂) := by
    rw [← eq_sub_iff_add_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← h, Matrix.mulVec_mulVec, hDD', Matrix.one_mulVec]
    · rw [h, Matrix.mulVec_mulVec, hDD, Matrix.one_mulVec]
  have hblack : E *ᵥ (D₁⁻¹ *ᵥ (b₁ - F *ᵥ x₂)) + D₂ *ᵥ x₂ = b₂
      ↔ (fromBlocks D₁ F E D₂).schurComplement *ᵥ x₂ = b₂ - E *ᵥ (D₁⁻¹ *ᵥ b₁) := by
    rw [Matrix.schurComplement_fromBlocks]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
    rw [eq_sub_iff_add_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [← h] <;> abel
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [helim]
  refine ⟨fun h => ⟨?_, hred.1 h.1⟩, fun h => ⟨hred.2 h.2, ?_⟩⟩
  · rw [← hblack, ← hred.1 h.1]
    exact h.2
  · rw [h.2]
    exact hblack.2 h.1

end SaadSparse.Chapter12
