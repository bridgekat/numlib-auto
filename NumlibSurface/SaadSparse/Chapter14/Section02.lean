import Mathlib.Analysis.SpecialFunctions.Sqrt
import Numlib.LinearAlgebra.Matrix.SchurComplement
import NumlibSurface.SaadSparse.Common

/-!
# Saad §14.2: block Gaussian elimination and the Schur complement

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §14.2.1–14.2.2 and §14.2.4.

The partitioning is the edge-based one of (14.2): the interior variables come first and the
interface variables last, so the system matrix is `Matrix.fromBlocks B E F C` over the index type
`Fin p ⊕ Fin q` and no reindexing equivalence appears anywhere.

* `schurComplement` is `S = C - F B⁻¹ E` of (14.5), `reducedRhs` is `g' = g - F B⁻¹ f` of (14.4),
  and `interfaceRestrict` is Saad's `R_y`, the restriction of a vector to its interface block.
* `blockGaussianElimination` is Algorithm 14.1 as a function, and `blockGaussianElimination_eq`
  says that it solves the system.
* `equation_14_6` is the block `LU` factorization and `equation_14_7` the block inverse.
* `proposition_14_1_1`, `proposition_14_1_2` and `proposition_14_1_3` are the three clauses of
  Proposition 14.1.
* `equation_14_16` is §14.2.4's `S = ∑ S_i`: a block diagonal interior block and an interface
  block assembled as `C = ∑ C_i` make the Schur complement the sum of the local ones.

Everything specializes `Numlib/LinearAlgebra/Matrix/SchurComplement`.

## §14.2.5, the model problem

§14.2.5 computes the local Schur complement of the five-point Laplacean on a rectangle split by a
vertical line, and it is the only place in the book where a Schur complement is found in closed
form.  The block `LU` factorization of `tridiag(-I, B, -I)` has diagonal blocks obeying (14.20),
`T_1 = B` and `T_{k+1} = B - T_k⁻¹`, and `T_n` is the local Schur complement `S_1`.

What is formalized here is that recurrence *at one eigenvalue* of `B`, which is where all of its
content lies: `modelSchurEigen` is Saad's `λ_k`, `modelRoot` the root `ρ` of `x² - μ x + 1`,
`modelSeq` the linearizing sequence `η_k`, `modelSeq_succ_succ` its linear difference equation,
`modelSchurEigen_eq` the closed form, and `modelRoot_lt_modelSchurEigen` the step Saad calls "it can
easily be shown", that the recurrence never breaks down.  Since `B = tridiag(-1, 4, -1)` has
eigenvalues `4 - 2 cos θ > 2`, the hypothesis `2 < μ` is exactly what the model problem supplies.

Not formalized, and the reason: the *matrix* form.  Transporting `λ_k` back through the discrete
sine basis to `T_k = f_k(B)` would need the inverse of `T_k` read on eigenvectors, and identifying
`T_n` with the Schur complement would need the block `LU` factorization of a block tridiagonal
matrix, which the library does not have; the limit `S_1 → Ŝ = (B + √(B² - 4I))/2` would need a
matrix square root on top of that.  None of it is out of reach —
`Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz` supplies the eigenpairs — but none of it is here.

§14.2.3, the vertex-based block structure (14.8)–(14.14), is built in `Section03.lean` as
`SaadSparse.Chapter14.VertexPartitioning`, next to its one theorem, Theorem 14.2.
-/

open Matrix

namespace SaadSparse.Chapter14

variable {p q : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} {E : Matrix (Fin p) (Fin q) ℝ}
variable {F : Matrix (Fin q) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}

/-- **(14.5)**: the Schur complement `S = C - F B⁻¹ E` associated with the interface variables of
the block partitioning (14.2). -/
noncomputable def schurComplement (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  C - F * B⁻¹ * E

/-- The Schur complement of §14.2, unfolded. -/
theorem schurComplement_def (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) :
    schurComplement B E F C = C - F * B⁻¹ * E := rfl

/-- The Schur complement of §14.2 is the backbone's `Matrix.schurComplement` of the block
matrix. -/
theorem schurComplement_eq (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) :
    schurComplement B E F C = (fromBlocks B E F C).schurComplement := rfl

/-- **(14.4)**: the right-hand side `g' = g - F B⁻¹ f` of the reduced system `S y = g'`. -/
noncomputable def reducedRhs (B : Matrix (Fin p) (Fin p) ℝ) (F : Matrix (Fin q) (Fin p) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : Fin q → ℝ :=
  g - F *ᵥ (B⁻¹ *ᵥ f)

/-- The reduced right-hand side, unfolded. -/
theorem reducedRhs_def (B : Matrix (Fin p) (Fin p) ℝ) (F : Matrix (Fin q) (Fin p) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : reducedRhs B F f g = g - F *ᵥ (B⁻¹ *ᵥ f) := rfl

/-- Saad's `R_y`: the restriction of a vector of the whole space to its interface block. -/
def interfaceRestrict (v : Fin p ⊕ Fin q → ℝ) : Fin q → ℝ := v ∘ Sum.inr

/-- The interface unknown `y = S⁻¹ g'` computed by Algorithm 14.1. -/
noncomputable def interfaceSolution (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) (f : Fin p → ℝ) (g : Fin q → ℝ) :
    Fin q → ℝ :=
  (schurComplement B E F C)⁻¹ *ᵥ reducedRhs B F f g

/-- **Algorithm 14.1** (block Gaussian elimination) as a function: solve `B E' = E` and
`B f' = f`, form `g' = g - F f'` and `S = C - F E'`, solve `S y = g'`, and recover
`x = f' - E' y`. -/
noncomputable def blockGaussianElimination (B : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin p) (Fin q) ℝ) (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : Fin p ⊕ Fin q → ℝ :=
  Sum.elim (B⁻¹ *ᵥ f - (B⁻¹ * E) *ᵥ interfaceSolution B E F C f g)
    (interfaceSolution B E F C f g)

/-- **(14.6)**: the block `LU` factorization of the partitioned matrix, whose second factor is
block upper triangular with the Schur complement in its `(2,2)` corner. -/
theorem equation_14_6 (hB : IsUnit B) :
    fromBlocks B E F C
      = fromBlocks 1 0 (F * B⁻¹) 1 * fromBlocks B E 0 (schurComplement B E F C) :=
  Matrix.fromBlocks_eq_mul_fromBlocks_schurComplement hB

/-- **(14.7)**: the block inverse of the partitioned matrix, with `S⁻¹` in its `(2,2)` corner. -/
theorem equation_14_7 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    (fromBlocks B E F C)⁻¹
      = fromBlocks (B⁻¹ + B⁻¹ * E * (schurComplement B E F C)⁻¹ * F * B⁻¹)
          (-(B⁻¹ * E * (schurComplement B E F C)⁻¹))
          (-((schurComplement B E F C)⁻¹ * F * B⁻¹)) (schurComplement B E F C)⁻¹ :=
  Matrix.inv_fromBlocks_eq hB hA

/-- **Proposition 14.1 (1)**: if the partitioned matrix and its `(1,1)` block are nonsingular,
then so is the Schur complement. -/
theorem proposition_14_1_1 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    IsUnit (schurComplement B E F C) :=
  Matrix.isUnit_schurComplement (by simpa using hB) hA

/-- **Proposition 14.1 (2)**: the Schur complement of a symmetric positive definite matrix is
symmetric positive definite. -/
theorem proposition_14_1_2 (hA : (fromBlocks B E F C).PosDef) :
    (schurComplement B E F C).PosDef :=
  Matrix.PosDef.schurComplement hA

/-- **Proposition 14.1 (3)**: `S⁻¹ y = R_y A⁻¹ (0, y)`, so a solver for the whole system provides
one for the reduced interface system. -/
theorem proposition_14_1_3 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) (y : Fin q → ℝ) :
    (schurComplement B E F C)⁻¹ *ᵥ y
      = interfaceRestrict ((fromBlocks B E F C)⁻¹ *ᵥ Sum.elim 0 y) := by
  have h22 : ((fromBlocks B E F C)⁻¹).toBlocks₂₂ = (schurComplement B E F C)⁻¹ :=
    Matrix.toBlocks₂₂_inv_eq_inv_schurComplement (by simpa using hB) hA
  funext j
  rw [← h22]
  simp [interfaceRestrict, Matrix.mulVec_apply_eq_sum, Fintype.sum_sum_type, Matrix.toBlocks₂₂]

/-- **Algorithm 14.1 solves the system**: the pair `(x, y)` it produces satisfies
`A (x, y) = (f, g)`. -/
theorem blockGaussianElimination_eq (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C))
    (f : Fin p → ℝ) (g : Fin q → ℝ) :
    fromBlocks B E F C *ᵥ blockGaussianElimination B E F C f g = Sum.elim f g := by
  have hBdet : IsUnit B.det := (isUnit_iff_isUnit_det _).1 hB
  have hSdet : IsUnit (schurComplement B E F C).det :=
    (isUnit_iff_isUnit_det _).1 (proposition_14_1_1 hB hA)
  have hBB : B * B⁻¹ = 1 := mul_nonsing_inv B hBdet
  have hSS : schurComplement B E F C * (schurComplement B E F C)⁻¹ = 1 := mul_nonsing_inv _ hSdet
  have hy : schurComplement B E F C *ᵥ interfaceSolution B E F C f g = reducedRhs B F f g := by
    rw [show interfaceSolution B E F C f g
        = (schurComplement B E F C)⁻¹ *ᵥ reducedRhs B F f g from rfl,
      Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
  rw [blockGaussianElimination, Matrix.fromBlocks_mulVec]
  refine congrArg₂ Sum.elim ?_ ?_
  · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hBB, Matrix.one_mul, Matrix.one_mulVec]
    abel
  · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc]
    have hsum : (F * B⁻¹) *ᵥ f - (F * B⁻¹ * E) *ᵥ interfaceSolution B E F C f g
          + C *ᵥ interfaceSolution B E F C f g
        = (F * B⁻¹) *ᵥ f + schurComplement B E F C *ᵥ interfaceSolution B E F C f g := by
      rw [schurComplement_def, Matrix.sub_mulVec]; abel
    rw [hsum, hy, reducedRhs_def, Matrix.mulVec_mulVec]
    abel

/-! ### §14.2.4: the Schur complement of a subdomain partitioning -/

/-- **(14.16)**: when the interior variables split into `s` subdomains with no coupling between
them, so that the interior block of (14.15) is block diagonal, `B = diag(B_1, …, B_s)`, and the
interface block is the sum `C = ∑ C_i` of the contributions assembled on the individual
subdomains, the Schur complement is the sum of the *local* Schur complements
`S_i = C_i - F_i B_i⁻¹ E_i`.

Saad derives this inside §14.2.4, "Schur complement for finite-element partitionings", where
`C = ∑ C_i` comes from the bilinear form splitting over subdomains with disjoint element sets; the
identity itself is block algebra and needs no finite elements, which is why the hypothesis here is
the decomposition of `C` rather than the discretization that produces it. -/
theorem equation_14_16 {s : ℕ} {d : Fin s → ℕ} (B : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℝ)
    (E : Matrix ((i : Fin s) × Fin (d i)) (Fin q) ℝ)
    (F : Matrix (Fin q) ((i : Fin s) × Fin (d i)) ℝ) (C : Fin s → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ i, IsUnit (B i)) :
    (fromBlocks (Matrix.blockDiagonal' B) E F (∑ i, C i)).schurComplement
      = ∑ i, (C i - F.submatrix id (Sigma.mk i) * (B i)⁻¹ * E.submatrix (Sigma.mk i) id) := by
  rw [Matrix.schurComplement_fromBlocks_blockDiagonal' B E F C hB]
  exact Finset.sum_congr rfl fun i _ => Matrix.schurComplement_fromBlocks _ _ _ _

/-! ### §14.2.5: the Schur complement of the model problem, at one eigenvalue -/

section ModelProblem

variable {μ : ℝ}

/-- **(14.20) read at one eigenvalue**: the recurrence `T_1 = B`, `T_{k+1} = B - T_k⁻¹` of the
two-domain model problem of §14.2.5, at an eigenvalue `μ` of `B = tridiag(-1, 4, -1)`.
`modelSchurEigen μ k` is Saad's `λ_{k+1}`, the eigenvalue of `T_{k+1}` on the eigenvector of `B`
for `μ`. -/
noncomputable def modelSchurEigen (μ : ℝ) : ℕ → ℝ
  | 0 => μ
  | k + 1 => μ - 1 / modelSchurEigen μ k

/-- §14.2.5: the larger root `ρ = (μ + √(μ² - 4))/2` of the characteristic equation
`x² - μ x + 1 = 0` of the linearized recurrence; the other root is `1/ρ`. -/
noncomputable def modelRoot (μ : ℝ) : ℝ := (μ + √(μ ^ 2 - 4)) / 2

/-- §14.2.5: the auxiliary sequence `η_k` of Saad's linearization, whose ratios are the `λ_k`.  It
satisfies the *linear* difference equation `η_{k+1} = μ η_k - η_{k-1}` and is therefore available in
closed form, `η_k = ρ^{k+1} - ρ^{-(k+1)}`; the normalizing factor `1/(ρ - ρ^{-1})` of the book is
dropped, since only the ratios are used. -/
noncomputable def modelSeq (μ : ℝ) (m : ℕ) : ℝ := modelRoot μ ^ (m + 1) - (modelRoot μ ^ (m + 1))⁻¹

theorem one_lt_modelRoot (hμ : 2 < μ) : 1 < modelRoot μ := by
  have h1 : (0 : ℝ) ≤ μ ^ 2 - 4 := by nlinarith
  have h2 : (0 : ℝ) ≤ √(μ ^ 2 - 4) := Real.sqrt_nonneg _
  rw [modelRoot]
  linarith

theorem modelRoot_pos (hμ : 2 < μ) : 0 < modelRoot μ :=
  lt_trans zero_lt_one (one_lt_modelRoot hμ)

/-- `ρ` is a root of `x² - μ x + 1`, so `ρ + 1/ρ = μ`: this is what makes the two exponentials
`ρ^k` and `ρ^{-k}` solve the linear difference equation. -/
theorem modelRoot_add_inv (hμ : 2 < μ) : modelRoot μ + (modelRoot μ)⁻¹ = μ := by
  have h1 : (0 : ℝ) ≤ μ ^ 2 - 4 := by nlinarith
  have hs : √(μ ^ 2 - 4) ^ 2 = μ ^ 2 - 4 := Real.sq_sqrt h1
  have hρ : modelRoot μ ≠ 0 := ne_of_gt (modelRoot_pos hμ)
  have hquad : modelRoot μ ^ 2 + 1 = μ * modelRoot μ := by
    rw [modelRoot]
    field_simp
    nlinarith [hs]
  field_simp
  linarith [hquad]

theorem modelSeq_pos (hμ : 2 < μ) (m : ℕ) : 0 < modelSeq μ m := by
  have hρ := one_lt_modelRoot hμ
  have h1 : 1 < modelRoot μ ^ (m + 1) := one_lt_pow₀ hρ (Nat.succ_ne_zero m)
  rw [modelSeq, sub_pos]
  calc (modelRoot μ ^ (m + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    _ < modelRoot μ ^ (m + 1) := h1

/-- The exponential identity behind the difference equation, for an arbitrary nonzero `ρ`. -/
private theorem exp_rec {ρ : ℝ} (hρ : ρ ≠ 0) (m : ℕ) :
    ρ ^ (m + 3) - (ρ ^ (m + 3))⁻¹
      = (ρ + ρ⁻¹) * (ρ ^ (m + 2) - (ρ ^ (m + 2))⁻¹) - (ρ ^ (m + 1) - (ρ ^ (m + 1))⁻¹) := by
  field_simp
  ring

private theorem exp_base {ρ : ℝ} (hρ : ρ ≠ 0) :
    ρ ^ (0 + 1 + 1) - (ρ ^ (0 + 1 + 1))⁻¹ = (ρ + ρ⁻¹) * (ρ ^ (0 + 1) - (ρ ^ (0 + 1))⁻¹) := by
  field_simp
  ring

private theorem exp_mul {ρ : ℝ} (hρ : ρ ≠ 0) (m : ℕ) :
    ρ * (ρ ^ (m + 1) - (ρ ^ (m + 1))⁻¹) = ρ ^ (m + 2) - (ρ ^ m)⁻¹ := by
  field_simp
  ring

/-- **The linear difference equation** `η_{k+1} = μ η_k - η_{k-1}` of §14.2.5. -/
theorem modelSeq_succ_succ (hμ : 2 < μ) (m : ℕ) :
    modelSeq μ (m + 2) = μ * modelSeq μ (m + 1) - modelSeq μ m := by
  have h := exp_rec (ne_of_gt (modelRoot_pos hμ)) m
  rw [modelRoot_add_inv hμ] at h
  simpa [modelSeq] using h

/-- **The closed form of the recurrence** (§14.2.5): the eigenvalue of `T_{k+1}` is the ratio
`η_{k+1}/η_k` of two consecutive terms of the linear sequence.  With `η_k = ρ^{k+1} - ρ^{-(k+1)}`
this is Saad's `λ_k = ρ (1 - ρ^{-2(k+1)})/(1 - ρ^{-2k})`, after dividing numerator and denominator
by `ρ^k`. -/
theorem modelSchurEigen_eq (hμ : 2 < μ) (m : ℕ) :
    modelSchurEigen μ m = modelSeq μ (m + 1) / modelSeq μ m := by
  induction m with
  | zero =>
      have h0 : modelSeq μ 0 ≠ 0 := ne_of_gt (modelSeq_pos hμ 0)
      have h := exp_base (ne_of_gt (modelRoot_pos hμ))
      rw [modelRoot_add_inv hμ] at h
      rw [modelSchurEigen, eq_div_iff h0]
      simpa [modelSeq] using h.symm
  | succ m ih =>
      have h1 : modelSeq μ (m + 1) ≠ 0 := ne_of_gt (modelSeq_pos hμ (m + 1))
      have h0 : modelSeq μ m ≠ 0 := ne_of_gt (modelSeq_pos hμ m)
      rw [modelSchurEigen, ih, one_div_div, eq_div_iff h1]
      have h := modelSeq_succ_succ hμ m
      field_simp
      linarith [h]

/-- **The recurrence does not break down** (§14.2.5): every `λ_k` exceeds `ρ > 1`, so `T_k` is
invertible at every step and `T_{k+1} = B - T_k⁻¹` is defined.  Saad writes "it can easily be shown
that the above recurrence does not break down" and leaves it there; this is the statement. -/
theorem modelRoot_lt_modelSchurEigen (hμ : 2 < μ) (m : ℕ) :
    modelRoot μ < modelSchurEigen μ m := by
  have hρ1 := one_lt_modelRoot hμ
  have hρ : (0 : ℝ) < modelRoot μ := modelRoot_pos hμ
  have h0 : (0 : ℝ) < modelSeq μ m := modelSeq_pos hμ m
  have hlt : (modelRoot μ ^ (m + 2))⁻¹ < (modelRoot μ ^ m)⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) (by positivity)]
    exact pow_lt_pow_right₀ hρ1 (by omega)
  have hkey : modelRoot μ * modelSeq μ m = modelRoot μ ^ (m + 2) - (modelRoot μ ^ m)⁻¹ := by
    rw [modelSeq]
    exact exp_mul (ne_of_gt hρ) m
  have hseq : modelSeq μ (m + 1) = modelRoot μ ^ (m + 2) - (modelRoot μ ^ (m + 2))⁻¹ := by
    rw [modelSeq]
  rw [modelSchurEigen_eq hμ, lt_div_iff₀ h0, hkey, hseq]
  linarith

/-- Every `λ_k` is positive, hence nonzero: the form of `modelRoot_lt_modelSchurEigen` that the
recurrence itself needs. -/
theorem modelSchurEigen_pos (hμ : 2 < μ) (m : ℕ) : 0 < modelSchurEigen μ m :=
  lt_trans (modelRoot_pos hμ) (modelRoot_lt_modelSchurEigen hμ m)

end ModelProblem

end SaadSparse.Chapter14
