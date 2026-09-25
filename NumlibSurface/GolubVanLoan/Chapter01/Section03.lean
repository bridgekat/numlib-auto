import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic.NoncommRing
import Numlib.LinearAlgebra.Matrix.Block
import Numlib.LinearAlgebra.Matrix.Hamiltonian
import Numlib.LinearAlgebra.Matrix.Kronecker
import NumlibSurface.GolubVanLoan.Chapter01.Section02

/-!
# Golub–Van Loan §1.3: block matrices and algorithms

Surface file for §1.3 of Golub and Van Loan, *Matrix Computations* (4th edition): block
multiplication (Theorem 1.3.1), the Kronecker product and its properties (1.3.1)–(1.3.5), the
`vec` identity (1.3.6), Hamiltonian and symplectic matrices (§1.3.10), and Strassen's recursive
multiplication (Algorithm 1.3.1).

## Design

A partition into blocks of sizes `m₁, …, m_q` is a `Sigma` type `(α : Fin q) × Fin (m α)`, laid out
contiguously by Mathlib's `finSigmaFinEquiv : (α : Fin q) × Fin (m α) ≃ Fin (∑ α, m α)`: block
`A_{αβ}` of the book, `A(τ+1:τ+m_α, μ+1:μ+n_β)`, is
`A.submatrix (finSigmaFinEquiv ∘ Sigma.mk α) (finSigmaFinEquiv ∘ Sigma.mk β)`. Theorem 1.3.1 is
the backbone's `Matrix.mul_submatrix_sigmaMk_eq_sum` transported along `finSigmaFinEquiv`.

The Kronecker product `B ⊗ C ∈ ℝ^{m₁m₂ × n₁n₂}` is the backbone's positional
`Matrix.kroneckerFin B C` (the `(i, j)` block is `b_ij C`, row `(i₁ − 1)m₂ + i₂` being
`finProdFinEquiv (i₁, i₂)`), `vec` is `Matrix.vecFin` and the perfect shuffle is
`Matrix.perfectShuffle` (`Numlib/LinearAlgebra/Matrix/Kronecker`, `…/Permutation`).

Hamiltonian matrices are the backbone's `Matrix.IsHamiltonian` on `Fin n ⊕ Fin n`, symplectic
ones Mathlib's `Matrix.symplecticGroup (Fin n) ℝ`. The book's `J = [0 I; −I 0]` is `bookJ n`, the
negative of Mathlib's `Matrix.J`; both defining conditions are invariant under `J ↦ −J`, so they are
stated with the book's `J` and proved equivalent to the Mathlib forms. The `2n × 2n` matrices are
kept in their `2 × 2` block form `Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ`.

Strassen's algorithm recurses on `q` for `n = 2^q`, splitting `Fin (2^(q+1))` as
`Fin (2^q) ⊕ Fin (2^q)` (`twoPowSplit`, the book's `u = 1:m`, `v = m+1:n`); the seven sums and
differences and the four assemblies are entrywise rounded additions `matrixAdd`, `matrixSub`, and
the base case is Algorithm 1.1.5 with `C = 0`.

## Main results

* `theorem_1_3_1` — block multiplication.
* `equation_1_3_1` … `equation_1_3_6` — the Kronecker identities.
* `bookJ`, `isHamiltonian_iff`, `isSymplectic_iff`, `symplectic_blocks` — §1.3.10.
* `algorithm_1_3_1`, `algorithm_1_3_1_spec` — Strassen multiplication.

## Not formalized here

The block-sparse terminology of §1.3.1, §1.3.3's submatrix notation, the unnumbered blocked gaxpys
(§1.3.4) and block products (§1.3.5), the band inheritance of `B ⊗ C`, §1.3.8's multiple Kronecker
reshaping and its `6n⁴` count, §1.3.9's real form of complex multiplication, Strassen's operation
counts and `n^{2.807}`, the MATLAB `reshape` example (`Matrix.reshape` is in the backbone).
-/

open Matrix

namespace GolubVanLoan.Chapter01

/-! ### Theorem 1.3.1: block multiplication -/

/-- **Theorem 1.3.1** (block multiplication). If `A` is partitioned into blocks `A_{αγ}` of sizes
`m_α × p_γ` and `B` into blocks `B_{γβ}` of sizes `p_γ × n_β`, then the blocks of `C = AB` are
`C_{αβ} = ∑_{γ=1}^{s} A_{αγ} B_{γβ}`. The block `X_{αβ}` is `X` restricted to the contiguous rows
of block `α` and columns of block `β`, `finSigmaFinEquiv ∘ Sigma.mk α` and
`finSigmaFinEquiv ∘ Sigma.mk β`. -/
theorem theorem_1_3_1 {q s r : ℕ} {m : Fin q → ℕ} {p : Fin s → ℕ} {n : Fin r → ℕ}
    (A : Matrix (Fin (∑ α, m α)) (Fin (∑ γ, p γ)) ℝ)
    (B : Matrix (Fin (∑ γ, p γ)) (Fin (∑ β, n β)) ℝ) (α : Fin q) (β : Fin r) :
    (A * B).submatrix (finSigmaFinEquiv ∘ Sigma.mk α) (finSigmaFinEquiv ∘ Sigma.mk β) =
      ∑ γ, A.submatrix (finSigmaFinEquiv ∘ Sigma.mk α) (finSigmaFinEquiv ∘ Sigma.mk γ) *
        B.submatrix (finSigmaFinEquiv ∘ Sigma.mk γ) (finSigmaFinEquiv ∘ Sigma.mk β) := by
  have h := mul_submatrix_sigmaMk_eq_sum (A.submatrix finSigmaFinEquiv finSigmaFinEquiv)
    (B.submatrix finSigmaFinEquiv finSigmaFinEquiv) α β
  simp only [submatrix_mul_equiv, submatrix_submatrix] at h
  exact h

/-! ### The Kronecker product (1.3.1)–(1.3.6) -/

section Kronecker

variable {m₁ n₁ m₂ n₂ : ℕ}

/-- **(1.3.1)**: `(B ⊗ C)ᵀ = Bᵀ ⊗ Cᵀ`. -/
theorem equation_1_3_1 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    (kroneckerFin B C)ᵀ = kroneckerFin Bᵀ Cᵀ :=
  transpose_kroneckerFin B C

/-- **(1.3.2)**: `(B ⊗ C)(D ⊗ F) = BD ⊗ CF`. -/
theorem equation_1_3_2 {p₁ p₂ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) (D : Matrix (Fin n₁) (Fin p₁) ℝ)
    (F : Matrix (Fin n₂) (Fin p₂) ℝ) :
    kroneckerFin B C * kroneckerFin D F = kroneckerFin (B * D) (C * F) :=
  kroneckerFin_mul_kroneckerFin B C D F

/-- **(1.3.3)**: for nonsingular `B` and `C`, `B ⊗ C` is nonsingular and
`(B ⊗ C)⁻¹ = B⁻¹ ⊗ C⁻¹`. (Lean's inverse makes the identity hold without the hypotheses; they are
the book's, and give the nonsingularity.) -/
theorem equation_1_3_3 (B : Matrix (Fin m₁) (Fin m₁) ℝ) (C : Matrix (Fin m₂) (Fin m₂) ℝ)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    IsUnit (kroneckerFin B C).det ∧ (kroneckerFin B C)⁻¹ = kroneckerFin B⁻¹ C⁻¹ := by
  refine ⟨?_, inv_kroneckerFin B C⟩
  rw [kroneckerFin, det_submatrix_equiv_self, det_kronecker]
  exact (hB.pow _).mul (hC.pow _)

/-- **(1.3.4)**: `B ⊗ (C ⊗ D) = (B ⊗ C) ⊗ D`, the two sides living on `Fin (m₁ (m₂ m₃))` and
`Fin (m₁ m₂ m₃)`, identified by `Nat.mul_assoc`. -/
theorem equation_1_3_4 {m₃ n₃ : ℕ} (B : Matrix (Fin m₁) (Fin n₁) ℝ)
    (C : Matrix (Fin m₂) (Fin n₂) ℝ) (D : Matrix (Fin m₃) (Fin n₃) ℝ) :
    kroneckerFin B (kroneckerFin C D) =
      (kroneckerFin (kroneckerFin B C) D).submatrix (finCongr (Nat.mul_assoc m₁ m₂ m₃)).symm
        (finCongr (Nat.mul_assoc n₁ n₂ n₃)).symm :=
  kroneckerFin_assoc B C D

/-- **(1.3.5)**: `P (B ⊗ C) Qᵀ = C ⊗ B` for `P = 𝒫_{m₁,m₂}` and `Q = 𝒫_{n₁,n₂}`. -/
theorem equation_1_3_5 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ) :
    perfectShuffle m₁ m₂ * kroneckerFin B C *
        (perfectShuffle n₁ n₂ : Matrix (Fin (n₂ * n₁)) (Fin (n₁ * n₂)) ℝ)ᵀ =
      kroneckerFin C B :=
  perfectShuffle_mul_kroneckerFin_mul_transpose B C

/-- **(1.3.6)**: for `B ∈ ℝ^{m₁×n₁}`, `C ∈ ℝ^{m₂×n₂}` and `X ∈ ℝ^{n₂×n₁}`,
`Y = C X Bᵀ ⇔ vec(Y) = (B ⊗ C) vec(X)`. (The book's dimension `X ∈ ℝ^{n₁×m₂}` is a misprint for
`ℝ^{n₂×n₁}`, the only size for which `C X Bᵀ` is defined.) -/
theorem equation_1_3_6 (B : Matrix (Fin m₁) (Fin n₁) ℝ) (C : Matrix (Fin m₂) (Fin n₂) ℝ)
    (X : Matrix (Fin n₂) (Fin n₁) ℝ) (Y : Matrix (Fin m₂) (Fin m₁) ℝ) :
    Y = C * X * Bᵀ ↔ vecFin Y = kroneckerFin B C *ᵥ vecFin X := by
  rw [kroneckerFin_mulVec_vecFin]
  exact ⟨fun h => h ▸ rfl, fun h => vecFin_injective h⟩

end Kronecker

/-! ### Hamiltonian and symplectic matrices (§1.3.10) -/

/-- **§1.3.10**: the book's `J = [0 I_n; −I_n 0]`, on `Fin n ⊕ Fin n`. -/
def bookJ (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fromBlocks 0 1 (-1) 0

/-- The book's `J` is the negative of Mathlib's `Matrix.J`. -/
theorem bookJ_eq_neg_J (n : ℕ) : bookJ n = -J (Fin n) ℝ := by
  rw [bookJ, J, fromBlocks_neg, neg_zero, neg_neg]

/-- **§1.3.10**: the two definitions of a Hamiltonian matrix agree. `M = [A G; F H]` has the form
`[A G; F −Aᵀ]` with `F`, `G` symmetric iff `J M Jᵀ = −Mᵀ` (the book's `J`), and both are the
backbone's `Matrix.IsHamiltonian`. -/
theorem isHamiltonian_iff {n : ℕ} (A F G H : Matrix (Fin n) (Fin n) ℝ) :
    ((H = -Aᵀ ∧ Fᵀ = F ∧ Gᵀ = G) ↔
        bookJ n * fromBlocks A G F H * (bookJ n)ᵀ = -(fromBlocks A G F H)ᵀ) ∧
      ((fromBlocks A G F H).IsHamiltonian ↔
        bookJ n * fromBlocks A G F H * (bookJ n)ᵀ = -(fromBlocks A G F H)ᵀ) := by
  have h : (fromBlocks A G F H).IsHamiltonian ↔
      bookJ n * fromBlocks A G F H * (bookJ n)ᵀ = -(fromBlocks A G F H)ᵀ := by
    rw [IsHamiltonian]
    simp only [bookJ_eq_neg_J, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact ⟨isHamiltonian_fromBlocks_iff.symm.trans h, h⟩

/-- **§1.3.10**: `S` is symplectic in the book's sense, `Sᵀ J S = J`, iff it lies in Mathlib's
symplectic group. -/
theorem isSymplectic_iff {n : ℕ} (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    Sᵀ * bookJ n * S = bookJ n ↔ S ∈ symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff', bookJ_eq_neg_J, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

/-- **§1.3.10**: if `S = [S₁₁ S₁₂; S₂₁ S₂₂]` is symplectic, then `S₁₁ᵀS₂₁` and `S₂₂ᵀS₁₂` are
symmetric and `S₁₁ᵀS₂₂ = I_n + S₂₁ᵀS₁₂` ("it follows that"; the converse holds as well). -/
theorem symplectic_blocks {n : ℕ} (S₁₁ S₁₂ S₂₁ S₂₂ : Matrix (Fin n) (Fin n) ℝ) :
    (fromBlocks S₁₁ S₁₂ S₂₁ S₂₂)ᵀ * bookJ n * fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ = bookJ n ↔
      (S₁₁ᵀ * S₂₁).IsSymm ∧ (S₂₂ᵀ * S₁₂).IsSymm ∧ S₁₁ᵀ * S₂₂ = 1 + S₂₁ᵀ * S₁₂ := by
  rw [isSymplectic_iff, SymplecticGroup.fromBlocks_mem_iff, IsSymm, IsSymm, transpose_mul,
    transpose_mul, transpose_transpose, transpose_transpose, sub_eq_iff_eq_add]
  exact and_congr eq_comm Iff.rfl

/-! ### Algorithm 1.3.1: Strassen matrix multiplication -/

section Strassen

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The entrywise rounded sum `fl(X + Y)` of two square matrices, `X(i,j) = X(i,j) + Y(i,j)` over
the rows, then the columns. -/
def matrixAdd {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) : M (Matrix (Fin k) (Fin k) ℝ) :=
  (List.finRange k).foldlM (fun Z i =>
    (List.finRange k).foldlM (fun Z j => do
      let z ← rnd (Z i j + Y i j)
      pure (Z.updateRow i (Function.update (Z i) j z))) Z) X

/-- The entrywise rounded difference `fl(X − Y)` of two square matrices. -/
def matrixSub {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) : M (Matrix (Fin k) (Fin k) ℝ) :=
  (List.finRange k).foldlM (fun Z i =>
    (List.finRange k).foldlM (fun Z j => do
      let z ← rnd (Z i j - Y i j)
      pure (Z.updateRow i (Function.update (Z i) j z))) Z) X

/-- The splitting of `Fin (2^(q+1))` into halves, the book's `u = 1:m`, `v = m+1:n` for
`n = 2m = 2^(q+1)`: `Sum.inl` is the first half, `Sum.inr` the second. -/
def twoPowSplit (q : ℕ) : Fin (2 ^ q) ⊕ Fin (2 ^ q) ≃ Fin (2 ^ (q + 1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ, mul_two]))

/-- **Algorithm 1.3.1 (Strassen Matrix Multiplication).** "Suppose `n = 2^q` and that
`A, B ∈ ℝ^{n×n}`. If `n_min = 2^d` with `d ≤ q`, then this algorithm computes `C = AB` by applying
Strassen procedure recursively":
```
function C = strass(A, B, n, n_min)
    if n ≤ n_min
        C = AB (conventionally computed)
    else
        m = n/2; u = 1:m; v = m+1:n
        P₁ = strass(A(u,u) + A(v,v), B(u,u) + B(v,v), m, n_min)
        P₂ = strass(A(v,u) + A(v,v), B(u,u), m, n_min)
        P₃ = strass(A(u,u), B(u,v) − B(v,v), m, n_min)
        P₄ = strass(A(v,v), B(v,u) − B(u,u), m, n_min)
        P₅ = strass(A(u,u) + A(u,v), B(v,v), m, n_min)
        P₆ = strass(A(v,u) − A(u,u), B(u,u) + B(u,v), m, n_min)
        P₇ = strass(A(u,v) − A(v,v), B(v,u) + B(v,v), m, n_min)
        C(u,u) = P₁ + P₄ − P₅ + P₇
        C(u,v) = P₃ + P₅
        C(v,u) = P₂ + P₄
        C(v,v) = P₁ + P₃ − P₂ + P₆
    end
```
The conventional product is Algorithm 1.1.5 with `C = 0`; `n ≤ n_min` is `q ≤ d`. -/
def algorithm_1_3_1 (d : ℕ) :
    (q : ℕ) → Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ → Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ →
      M (Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ)
  | 0, A, B => algorithm_1_1_5 rnd A B 0
  | q + 1, A, B =>
    if q + 1 ≤ d then algorithm_1_1_5 rnd A B 0 else do
      let A' := A.submatrix (twoPowSplit q) (twoPowSplit q)
      let B' := B.submatrix (twoPowSplit q) (twoPowSplit q)
      let P₁ ← algorithm_1_3_1 d q (← matrixAdd rnd A'.toBlocks₁₁ A'.toBlocks₂₂)
        (← matrixAdd rnd B'.toBlocks₁₁ B'.toBlocks₂₂)
      let P₂ ← algorithm_1_3_1 d q (← matrixAdd rnd A'.toBlocks₂₁ A'.toBlocks₂₂) B'.toBlocks₁₁
      let P₃ ← algorithm_1_3_1 d q A'.toBlocks₁₁ (← matrixSub rnd B'.toBlocks₁₂ B'.toBlocks₂₂)
      let P₄ ← algorithm_1_3_1 d q A'.toBlocks₂₂ (← matrixSub rnd B'.toBlocks₂₁ B'.toBlocks₁₁)
      let P₅ ← algorithm_1_3_1 d q (← matrixAdd rnd A'.toBlocks₁₁ A'.toBlocks₁₂) B'.toBlocks₂₂
      let P₆ ← algorithm_1_3_1 d q (← matrixSub rnd A'.toBlocks₂₁ A'.toBlocks₁₁)
        (← matrixAdd rnd B'.toBlocks₁₁ B'.toBlocks₁₂)
      let P₇ ← algorithm_1_3_1 d q (← matrixSub rnd A'.toBlocks₁₂ A'.toBlocks₂₂)
        (← matrixAdd rnd B'.toBlocks₂₁ B'.toBlocks₂₂)
      let C₁₁ ← matrixAdd rnd (← matrixSub rnd (← matrixAdd rnd P₁ P₄) P₅) P₇
      let C₁₂ ← matrixAdd rnd P₃ P₅
      let C₂₁ ← matrixAdd rnd P₂ P₄
      let C₂₂ ← matrixAdd rnd (← matrixSub rnd (← matrixAdd rnd P₁ P₃) P₂) P₆
      pure ((fromBlocks C₁₁ C₁₂ C₂₁ C₂₂).submatrix (twoPowSplit q).symm
        (twoPowSplit q).symm)

end Strassen

/-- The row loop of `matrixAdd`/`matrixSub` after fusion. -/
private def matrixRowOp {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) (op : ℝ → ℝ → ℝ) {k : ℕ}
    (y : Fin k → ℝ) (r : Fin k → ℝ) : M (Fin k → ℝ) :=
  (List.finRange k).foldlM (fun r j => do
    let c ← rnd (op (r j) (y j)); pure (Function.update r j c)) r

/-- An entrywise operation written as a loop over the rows of fused row loops. -/
private theorem foldlM_entrywise_eq {M : Type → Type} [Monad M] [LawfulMonad M] (rnd : ℝ → M ℝ)
    (op : ℝ → ℝ → ℝ) {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) :
    (List.finRange k).foldlM (fun (Z : Matrix (Fin k) (Fin k) ℝ) i =>
      (List.finRange k).foldlM (fun (Z : Matrix (Fin k) (Fin k) ℝ) j => do
        let z ← rnd (op (Z i j) (Y i j))
        pure (Z.updateRow i (Function.update (Z i) j z))) Z) X =
    (List.finRange k).foldlM (fun Z i => do
      let r ← matrixRowOp rnd op (Y i) (Z i); pure (Z.updateRow i r)) X := by
  congr 1
  funext Z i
  exact foldlM_updateRow_row i (fun j c => rnd (op c (Y i j))) _ Z

/-- In exact arithmetic an entrywise loop computes the entrywise operation. -/
private theorem idRun_foldlM_entrywise (op : ℝ → ℝ → ℝ) {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) :
    Id.run ((List.finRange k).foldlM (fun (Z : Matrix (Fin k) (Fin k) ℝ) i =>
      (List.finRange k).foldlM (fun (Z : Matrix (Fin k) (Fin k) ℝ) j => do
        let z ← (pure (op (Z i j) (Y i j)) : Id ℝ)
        pure (Z.updateRow i (Function.update (Z i) j z))) Z) X) =
      Matrix.of fun i j => op (X i j) (Y i j) := by
  rw [foldlM_entrywise_eq pure op X Y]
  ext i j
  rw [idRun_foldlM_updateRow_apply _ _ (List.nodup_finRange k), ite_eq_left (List.mem_finRange i),
    matrixRowOp, idRun_foldlM_update_apply (fun j c => (pure (op c (Y i j)) : Id ℝ)) _
      (List.nodup_finRange k), ite_eq_left (List.mem_finRange j)]
  rfl

/-- In exact arithmetic `matrixAdd` is the sum. -/
theorem matrixAdd_spec {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) :
    Id.run (matrixAdd pure X Y) = X + Y :=
  (idRun_foldlM_entrywise (· + ·) X Y).trans rfl

/-- In exact arithmetic `matrixSub` is the difference. -/
theorem matrixSub_spec {k : ℕ} (X Y : Matrix (Fin k) (Fin k) ℝ) :
    Id.run (matrixSub pure X Y) = X - Y :=
  (idRun_foldlM_entrywise (· - ·) X Y).trans rfl

/-- **Algorithm 1.3.1 computes `C = AB`**, for every `n_min = 2^d`: by induction on `q`, the base
case being Algorithm 1.1.5 and the step Strassen's seven identities ("easily confirmed by
substitution"), which hold in the noncommutative ring of `2^q × 2^q` blocks. -/
theorem algorithm_1_3_1_spec (d : ℕ) :
    ∀ (q : ℕ) (A B : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℝ),
      Id.run (algorithm_1_3_1 pure d q A B) = A * B
  | 0, A, B => by rw [algorithm_1_3_1, algorithm_1_1_5_spec, zero_add]
  | q + 1, A, B => by
    rw [algorithm_1_3_1]
    split_ifs
    · rw [algorithm_1_1_5_spec, zero_add]
    · simp only [Id.run_bind, Id.run_pure, matrixAdd_spec, matrixSub_spec,
        algorithm_1_3_1_spec d q]
      set e := twoPowSplit q
      have hAB : A * B = (A.submatrix e e * B.submatrix e e).submatrix e.symm e.symm := by
        rw [submatrix_mul_equiv, submatrix_submatrix, e.self_comp_symm, submatrix_id_id]
      rw [hAB]
      conv_rhs => rw [← fromBlocks_toBlocks (A.submatrix e e),
        ← fromBlocks_toBlocks (B.submatrix e e), fromBlocks_multiply]
      congr 1
      rw [fromBlocks_inj]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

end GolubVanLoan.Chapter01
