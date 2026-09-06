import Mathlib.Data.Sum.Order
import Numlib.LinearSolve.DomainDecomposition.Schur
import Numlib.LinearSolve.Preconditioner.ILU
import NumlibSurface.SaadSparse.Chapter14.Section02

/-!
# Saad §14.4: Schur complement approaches

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §14.4.1.

A Schur complement method solves the reduced system `S y = g'` of §14.2 by a preconditioned Krylov
method, and §14.4.1 builds the preconditioner for `S` out of one for the whole matrix `A`.

* `interfaceRestrictMatrix` and `interfaceProlongMatrix` are Saad's `R_y = (0 I)` and `R_yᵀ`, the
  matrices of the restriction `interfaceRestrict` of §14.2.
* `inducedPreconditioner` is `M_S = (R_y M_A⁻¹ R_yᵀ)⁻¹` of (14.46), the preconditioner induced on
  `S` by a preconditioner `M_A` of `A`; `inducedPreconditioner_eq_schurComplement` is the remark
  that follows (14.46), that an exact preconditioner of `A` induces an exact one of `S`, which is
  Proposition 14.1 (3) again.
* `proposition_14_10` is the factored case: for `M_A = L_A U_A` with `L_A` block lower triangular
  and `U_A` block upper triangular — the shape Saad displays for an ILU factorization in the
  ordering that lists the interface variables last — the `L` and `U` factors of `M_S` are the
  `(2,2)` blocks of the `L` and `U` factors of `M_A`.  `proposition_14_10_of_isILU` is the same
  statement with Saad's own hypothesis, a `Matrix.IsILU` factorization in the ordering
  `Fin p ⊕ₗ Fin q`, whose factors are block triangular by `toBlocks₁₂_eq_zero_of_isILU` and
  `toBlocks₂₁_eq_zero_of_isILU`.

Everything specializes `Numlib/LinearSolve/DomainDecomposition/Schur`.

§14.4.2 is probing: `S` is dense but its entries decay away from the diagonal, so it is replaced by
a tridiagonal `T` recovered from three matrix–vector products.  The *use* is a heuristic — the book
gives no bound on `S - T`, and none holds without hypotheses it does not state — but the
reconstruction itself is exact, and `probeVec`, `mulVec_probeVec_apply` and `probing_eq` are it: the
three `3`-periodic vectors, the read-off of one entry per position, and the resulting uniqueness.

§14.4.3 (preconditioning vertex-based Schur complements) is a paragraph of advice with no stated
result and is not formalized.
-/

open Matrix DomainDecomposition

namespace SaadSparse.Chapter14

variable {p q : ℕ}

/-! ### The interface restriction as a matrix -/

/-- **`R_y = (0  I)`** of Proposition 14.1 and §14.4.1, as a matrix. -/
noncomputable abbrev interfaceRestrictMatrix (p q : ℕ) : Matrix (Fin q) (Fin p ⊕ Fin q) ℝ :=
  restrictMatrix ℝ (Fin p) (Fin q)

/-- **`R_yᵀ`**, the extension of an interface vector by zero, as a matrix. -/
noncomputable abbrev interfaceProlongMatrix (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin q) ℝ :=
  prolongMatrix ℝ (Fin p) (Fin q)

/-- The matrix `R_y` acts as the restriction `interfaceRestrict` of §14.2. -/
theorem interfaceRestrictMatrix_mulVec (v : Fin p ⊕ Fin q → ℝ) :
    interfaceRestrictMatrix p q *ᵥ v = interfaceRestrict v :=
  restrictMatrix_mulVec v

/-- `R_y R_yᵀ = I`: the rows of `R_y` are orthonormal. -/
theorem interfaceRestrictMatrix_mul_interfaceProlongMatrix :
    interfaceRestrictMatrix p q * interfaceProlongMatrix p q = 1 :=
  restrictMatrix_mul_prolongMatrix

/-! ### §14.4.1: induced preconditioners -/

/-- **(14.46)**: the preconditioner `M_S = (R_y M_A⁻¹ R_yᵀ)⁻¹` that a preconditioner `M_A` of the
whole matrix induces on the Schur complement.  Applying `M_S⁻¹` to `v` means solving
`M_A (x, y) = (0, v)` and keeping `y`, which is (14.45). -/
noncomputable def inducedPreconditioner (MA : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  (interfaceRestrictMatrix p q * MA⁻¹ * interfaceProlongMatrix p q)⁻¹

/-- The induced preconditioner of §14.4.1 is the backbone's. -/
theorem inducedPreconditioner_eq (MA : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ) :
    inducedPreconditioner MA = DomainDecomposition.inducedPreconditioner MA :=
  (inducedPreconditioner_eq_inv_restrict_mul MA).symm

/-- **The remark after (14.46)**: an exact preconditioner of `A` induces an exact preconditioner of
`S`.  This is Proposition 14.1 (3) read as a statement about matrices rather than about vectors. -/
theorem inducedPreconditioner_eq_schurComplement {B : Matrix (Fin p) (Fin p) ℝ}
    {E : Matrix (Fin p) (Fin q) ℝ} {F : Matrix (Fin q) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}
    (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    inducedPreconditioner (fromBlocks B E F C) = schurComplement B E F C := by
  rw [inducedPreconditioner_eq, DomainDecomposition.inducedPreconditioner,
    Matrix.toBlocks₂₂_inv_eq_inv_schurComplement (by simpa using hB) hA]
  exact Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 (proposition_14_1_1 hB hA))

/-- **Proposition 14.10**: let `M_A = L_A U_A` be a preconditioner of `A` in factored form, with
`L_A` block lower triangular and `U_A` block upper triangular for the partitioning (14.2) — the
shape §14.4.1 displays for an ILU factorization of `A` in the ordering that lists the interface
variables last.  Then the preconditioner `M_S` it induces on `S` by (14.46) is `M_S = L_S U_S`, with
`L_S = R_y L_A R_yᵀ` and `U_S = R_y U_A R_yᵀ`: the `L` and `U` factors of `M_S` are the `(2,2)`
blocks of the `L` and `U` factors of `M_A`. -/
theorem proposition_14_10 (LB UB : Matrix (Fin p) (Fin p) ℝ) (X : Matrix (Fin q) (Fin p) ℝ)
    (Y : Matrix (Fin p) (Fin q) ℝ) (LS US : Matrix (Fin q) (Fin q) ℝ) (hLB : IsUnit LB)
    (hLS : IsUnit LS) (hUB : IsUnit UB) (hUS : IsUnit US) :
    inducedPreconditioner (fromBlocks LB 0 X LS * fromBlocks UB Y 0 US)
      = (interfaceRestrictMatrix p q * fromBlocks LB 0 X LS * interfaceProlongMatrix p q)
        * (interfaceRestrictMatrix p q * fromBlocks UB Y 0 US * interfaceProlongMatrix p q) := by
  rw [restrictMatrix_mul_mul_prolongMatrix, restrictMatrix_mul_mul_prolongMatrix,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₂, inducedPreconditioner_eq]
  exact DomainDecomposition.inducedPreconditioner_eq hLB hLS hUB hUS

/-! ### The block structure of an ILU factorization

The ordering `Fin p ⊕ₗ Fin q` is the global ordering of §14.2, in which the interior variables come
before the interface ones; a factorization that is triangular for it is block triangular for the
partitioning (14.2). -/

/-- The `L` factor of an ILU factorization in the ordering of (14.2) is block lower triangular. -/
theorem toBlocks₁₂_eq_zero_of_isILU {P : Set ((Fin p ⊕ₗ Fin q) × (Fin p ⊕ₗ Fin q))}
    {A L U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ}
    (h : Matrix.IsILU P (A : Matrix (Fin p ⊕ₗ Fin q) (Fin p ⊕ₗ Fin q) ℝ) L U) :
    L.toBlocks₁₂ = 0 := by
  ext i j
  exact h.l_eq_zero_of_lt (toLex (Sum.inl i)) (toLex (Sum.inr j)) (Sum.Lex.inl_lt_inr i j)

/-- The `U` factor of an ILU factorization in the ordering of (14.2) is block upper triangular. -/
theorem toBlocks₂₁_eq_zero_of_isILU {P : Set ((Fin p ⊕ₗ Fin q) × (Fin p ⊕ₗ Fin q))}
    {A L U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ}
    (h : Matrix.IsILU P (A : Matrix (Fin p ⊕ₗ Fin q) (Fin p ⊕ₗ Fin q) ℝ) L U) :
    U.toBlocks₂₁ = 0 := by
  ext i j
  exact h.u_eq_zero_of_gt (toLex (Sum.inr i)) (toLex (Sum.inl j)) (Sum.Lex.inl_lt_inr j i)

/-- **Proposition 14.10 for an ILU factorization**, which is the form Saad states it in: if
`M_A = L_A U_A` is an ILU preconditioner for `A` in the ordering of (14.2), and the diagonal blocks
of its factors are nonsingular, then the preconditioner induced on the Schur complement is
`M_S = L_S U_S` with `L_S = R_y L_A R_yᵀ` and `U_S = R_y U_A R_yᵀ`. -/
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

/-! ### §14.4.2: probing -/

/-- **§14.4.2**: the three `3`-periodic probe vectors of the probing technique,
`w_1 = (1,0,0,1,0,0,…)ᵀ`, `w_2 = (0,1,0,0,1,0,…)ᵀ`, `w_3 = (0,0,1,0,0,1,…)ᵀ`; the book's `w_{r+1}`
is `probeVec m r`. -/
def probeVec (m : ℕ) (r : ℕ) : Fin m → ℝ := fun i => if (i : ℕ) % 3 = r then 1 else 0

/-- A tridiagonal matrix vanishes off the three central diagonals, in index arithmetic. -/
private theorem apply_eq_zero_of_isTridiagonal {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : T.IsTridiagonal) {i j : Fin m} (h : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) :
    T i j = 0 := by
  rcases h with h | h
  · refine hT i j (Or.inr ⟨⟨(i : ℕ) + 1, lt_of_lt_of_le h j.isLt.le⟩, ?_, ?_⟩) <;>
      simp [Fin.lt_def, h]
  · refine hT i j (Or.inl ⟨⟨(j : ℕ) + 1, lt_of_lt_of_le h i.isLt.le⟩, ?_, ?_⟩) <;>
      simp [Fin.lt_def, h]

/-- **§14.4.2, the probing identity**: applying a tridiagonal `T` to the probe vector of residue
`r` reads off, in position `i`, the single entry of row `i` whose column is congruent to `r`
modulo `3`.  Since the three columns `i - 1, i, i + 1` have three distinct residues, every entry
of `T` appears in exactly one of the three products — which is Saad's "it is easy to recover `T`
by applying it to three well-chosen vectors". -/
theorem mulVec_probeVec_apply {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.IsTridiagonal) {i j : Fin m}
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

/-- **§14.4.2**: a tridiagonal matrix is *determined* by the three probe products, so the
tridiagonal approximation `T` of the Schur complement can be recovered from `S w_1`, `S w_2`,
`S w_3` alone.  The book states no bound on `S - T`, and none holds without hypotheses it does not
give; what is exact is this reconstruction. -/
theorem probing_eq {T T' : Matrix (Fin m) (Fin m) ℝ} (hT : T.IsTridiagonal)
    (hT' : T'.IsTridiagonal)
    (h : ∀ r, T *ᵥ probeVec m r = T' *ᵥ probeVec m r) : T = T' := by
  ext i j
  by_cases hij : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)
  · rw [apply_eq_zero_of_isTridiagonal hT hij, apply_eq_zero_of_isTridiagonal hT' hij]
  · rw [← mulVec_probeVec_apply hT ⟨by omega, by omega⟩,
      ← mulVec_probeVec_apply hT' ⟨by omega, by omega⟩, h]

end SaadSparse.Chapter14
