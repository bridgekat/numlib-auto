/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.CyclicReduction
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter03.Section04

/-!
# Golub and Van Loan, Section 4.5: Block tridiagonal systems

This module formalizes §4.5 of [golub2013matrix], linear systems $Ax = b$ whose matrix is block
tridiagonal with $q \times q$ blocks: diagonal blocks $D_i$, subdiagonal blocks $E_i$ and
superdiagonal blocks $F_i$ (4.5.2). If the pivots $U_i$ of the recurrence $U_0 = D_0$,
$L_i U_i = E_i$, $U_{i+1} = D_{i+1} - L_i F_i$ (4.5.4) are nonsingular, then $A$ is the product of a
block unit lower bidiagonal matrix with subdiagonal blocks $L_i$ and a block upper bidiagonal matrix
with diagonal blocks $U_i$ and superdiagonal blocks $F_i$ (4.5.3). The system is then solved by
block forward elimination and block back substitution (4.5.5). Under the block diagonal dominance
(4.5.6), the pivots are nonsingular, $\|L_i\|_1 \le 1$ and $\|U_i\|_1 \le \|A\|_1$
((4.5.7)–(4.5.8)).

The module also treats one step of block cyclic reduction for the system (4.5.9) with constant
commuting blocks and the recovery of the eliminated unknowns (§4.5.3), and the block scaling
(4.5.13)→(4.5.14) of the SPIKE framework (§4.5.4). The section has no numbered theorem and no
numbered algorithm. The proofs specialize the backbone modules
`Numlib.LinearAlgebra.Matrix.BlockTridiagonal` and `Numlib.Direct.CyclicReduction`.

## Main definitions

* (4.5.4), `GolubVanLoan.Chapter04.blockTridiagonalLU`: the block LU recurrence as a program, with
  block solves by Gaussian elimination with partial pivoting.
* (4.5.5), `GolubVanLoan.Chapter04.blockTridiagonalSolve`: block forward elimination and block back
  substitution as a program.

## Main results

* (4.5.3), `GolubVanLoan.Chapter04.equation_4_5_3`: if the pivots $U_0, \dots, U_{N-1}$ are
  nonsingular, then $A$ is the product of the two block bidiagonal factors and $L_i U_i = E_i$.
* (4.5.4), `GolubVanLoan.Chapter04.equation_4_5_4`: the exact run of
  `GolubVanLoan.Chapter04.blockTridiagonalLU` computes the multipliers $L_i$ and the pivots $U_i$ of
  the recurrence.
* (4.5.5), `GolubVanLoan.Chapter04.equation_4_5_5`: with the exact factors, the exact run of
  `GolubVanLoan.Chapter04.blockTridiagonalSolve` solves the block tridiagonal system.
* (4.5.6), `GolubVanLoan.Chapter04.equation_4_5_6`: under block diagonal dominance, every pivot
  $U_i$ and the matrix $A$ are nonsingular.
* (4.5.7), `GolubVanLoan.Chapter04.equation_4_5_7`: under block diagonal dominance,
  $\|L_i\|_1 \le 1$.
* (4.5.8), `GolubVanLoan.Chapter04.equation_4_5_8`: under block diagonal dominance,
  $\|U_i\|_1 \le \|A\|_1$.
* §4.5.3, `GolubVanLoan.Chapter04.cyclicReduction_step`: one step of block cyclic reduction gives a
  system of the same form with commuting blocks $2F^2 - D^2$ and $F^2$, and repeated steps leave one
  $q \times q$ system for the middle unknown.
* §4.5.3, `GolubVanLoan.Chapter04.cyclicReduction_back`: the eliminated unknowns solve $q \times q$
  systems with matrix $D$.
* (4.5.13)→(4.5.14), `GolubVanLoan.Chapter04.equation_4_5_14`: premultiplication by the inverse of
  the block diagonal gives an equivalent block tridiagonal system with identity diagonal blocks.

## Conventions

* The matrix (4.5.2) has $N + 1$ diagonal blocks $D_0, \dots, D_N$, indexed from $0$; the source
  writes $D_1, \dots, D_N$, so its $N$ is one larger. The subdiagonal blocks are
  $E_0, \dots, E_{N-1}$, with $E_i$ in block row $i + 1$ and block column $i$, and the superdiagonal
  blocks are $F_0, \dots, F_{N-1}$, with $F_i$ in block row $i$ and block column $i + 1$.
* The norm $\|\cdot\|_1$ of a block or of $A$ is the matrix norm induced by the vector $1$-norm,
  `Matrix.lpOpNorm 1`.

## Implementation notes

* Over the block ring `Matrix (Fin q) (Fin q) ℝ` the matrix (4.5.2) is `Matrix.tridiagonalOf E D F`.
  The scalar matrix of the source is its flattening `Matrix.blockTridiagonal E D F : Matrix (Fin
  (N + 1) × Fin q) (Fin (N + 1) × Fin q) ℝ` by Mathlib's `Matrix.comp`, which is a ring isomorphism
  (`Matrix.compRingEquiv`).
* The recurrence (4.5.4) is the backbone's `Matrix.tridiagonalLUPivot` (the pivots $U_i$) and
  `Matrix.tridiagonalLUMultiplier` (the multipliers $L_i$). These take $\mathbb{N}$-indexed families
  of blocks, so the blocks in the statements of §4.5.1–4.5.2 are $\mathbb{N}$-indexed families, of
  which only the first $N + 1$ or $N$ members are used.
* The constant-block system (4.5.9) is the backbone operator
  `CyclicReduction.constBlockTridiagonal D F`. It is `Matrix.blockTridiagonal` applied to the
  flattened vector (`CyclicReduction.constBlockTridiagonal_eq_blockTridiagonal_mulVec`).
* The algorithm-shaped displays (4.5.4) and (4.5.5) are the programs
  `GolubVanLoan.Chapter04.blockTridiagonalLU` and `GolubVanLoan.Chapter04.blockTridiagonalSolve`,
  written with a rounding hook as in the algorithm conventions of the library index. Their exact
  specifications are `GolubVanLoan.Chapter04.equation_4_5_4` and
  `GolubVanLoan.Chapter04.equation_4_5_5`. As the source suggests, their block solves call the
  Gaussian elimination with partial pivoting of Chapter 3
  (`GolubVanLoan.Chapter03.solveMultipleRHS`, `GolubVanLoan.Chapter03.solveGEPP`), and their block
  products call Algorithms 1.1.3 and 1.1.5.

## Deviations from the source

* **Reading.** The factorization and exact recurrence require only the pivots used in forming
  multipliers. See `GolubVanLoan.Chapter04.equation_4_5_3`, `GolubVanLoan.Chapter04.equation_4_5_4`.
* **Reading.** The block solve programs specify pivoting, rounding and singular-input behavior. See
  `GolubVanLoan.Chapter04.blockTridiagonalLU`, `GolubVanLoan.Chapter04.blockTridiagonalSolve`.
* **Generalization.** A single cyclic reduction step works with any odd block count. See
  `GolubVanLoan.Chapter04.cyclicReduction_step`.
* **Generalization.** The local back-substitution equations hold without commutativity. See
  `GolubVanLoan.Chapter04.cyclicReduction_back`.
* **Generalization.** The SPIKE scaling is stated for general invertible diagonal blocks. See
  `GolubVanLoan.Chapter04.equation_4_5_14`, `GolubVanLoan.Chapter04.diagonal_inv_mul_tridiagonalOf`.
* **(4.5.8)** (reading). The source prints $\|U_i\|_1 \le \|A_n\|_1$, whose right-hand side has no
  referent in the section. It is read as the $1$-norm of the whole matrix $A$. See
  `GolubVanLoan.Chapter04.equation_4_5_8`.

## Not formalized

* **The flop count of block cyclic reduction.**
* **Buneman's stabilization of block cyclic reduction.**
* **The rest of the SPIKE framework of §4.5.4**, including the displays (4.5.11)–(4.5.12) and the
  refined blockings.
-/

open Matrix Finset

namespace GolubVanLoan.Chapter04

variable {N q : ℕ}

/-! ### §4.5.1 Block tridiagonal LU factorization -/

/-- **Equation (4.5.3)** of [golub2013matrix], with the recurrence (4.5.4). Let
$E_i, D_i, F_i \in \mathbb{R}^{q \times q}$ for $i \in \mathbb{N}$, and let $A$ be the block
tridiagonal matrix with diagonal blocks $D_0, \dots, D_N$, subdiagonal blocks
$E_0, \dots, E_{N-1}$ and superdiagonal blocks $F_0, \dots, F_{N-1}$. Define the pivots and the
multipliers by
$$U_0 = D_0, \qquad L_i = E_i U_i^{-1}, \qquad U_{i+1} = D_{i+1} - E_i U_i^{-1} F_i.$$
If $U_0, \dots, U_{N-1}$ are nonsingular, then $A = LU$, where $L$ is the block lower bidiagonal
matrix with identity diagonal blocks and subdiagonal blocks $L_0, \dots, L_{N-1}$, and $U$ is
the block upper bidiagonal matrix with diagonal blocks $U_0, \dots, U_N$ and superdiagonal
blocks $F_0, \dots, F_{N-1}$. Moreover $L_i U_i = E_i$ for $i < N$.

The source derives the recurrence by comparing blocks in $A = LU$ and remarks that the procedure
is defined as long as the $U_i$ are nonsingular. The pivots and the multipliers are
`Matrix.tridiagonalLUPivot` and `Matrix.tridiagonalLUMultiplier`, with the inverse
`Ring.inverse`. The matrices $A$, $L$ and $U$ are flattened by `Matrix.blockTridiagonal`.

**Reading.** Lean requires invertibility only for the pivots used when forming multipliers. The
source describes the procedure as defined when the pivots are nonsingular, with no separate
exception for the last pivot. Solving the full system still requires the last pivot.
-/
theorem equation_4_5_3 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hU : ∀ i < N, IsUnit (tridiagonalLUPivot E D F i)) :
    blockTridiagonal (N := N) (fun i => E i) (fun i => D i) (fun i => F i) =
        blockTridiagonal (fun i => tridiagonalLUMultiplier E D F i) 1 0 *
          blockTridiagonal 0 (fun i => tridiagonalLUPivot E D F i) (fun i => F i) ∧
      ∀ i < N, tridiagonalLUMultiplier E D F i * tridiagonalLUPivot E D F i = E i := by
  refine ⟨?_, fun i hi => tridiagonalLUMultiplier_mul_tridiagonalLUPivot E D F (hU i hi)⟩
  simp only [blockTridiagonal, ← compRingEquiv_apply, ← map_mul]
  rw [tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot E D F hU]

/-! ### (4.5.4)–(4.5.5): The block programs -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Equation (4.5.4)** of [golub2013matrix], the block LU recurrence as a program. Given $N$ and
the blocks $E_i, D_i, F_i \in \mathbb{R}^{q \times q}$, the program computes the multipliers
$L_i$ and the pivots $U_i$ of the factorization (4.5.3):
```
U_1 = D_1
for i = 2:N
    Solve L_{i−1} U_{i−1} = E_{i−1} for L_{i−1}.
    U_i = D_i − L_{i−1} F_{i−1}
end
```
The program is indexed from $0$. Its state is the pair $(L, U)$ of $\mathbb{N}$-indexed families
of blocks, which starts with $L = 0$ and with $U_0 = D_0$ and all other $U_i = 0$. Pass
$i = 0, \dots, N-1$ solves the transposed system $U_i^T X = E_i^T$ by the multiple right-hand
side procedure (3.4.12) of Chapter 3 (`GolubVanLoan.Chapter03.solveMultipleRHS`, Gaussian
elimination with partial pivoting), sets $L_i = X^T$, and computes
$U_{i+1} = D_{i+1} + (-L_i) F_i$ by Algorithm 1.1.5. The source says that each $U_i$ must be
factored, for example by Gaussian elimination with pivoting. Transposition and negation are
exact.

**Reading.** The programs select the source's suggested Gaussian elimination with pivoting, specify
rounded block updates, and inherit the component solvers' totalized divisions for singular input.
Each program factors the blocks in its own calls to the solvers.
-/
noncomputable def blockTridiagonalLU (N : ℕ) (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ) :
    M ((ℕ → Matrix (Fin q) (Fin q) ℝ) × (ℕ → Matrix (Fin q) (Fin q) ℝ)) :=
  (List.range N).foldlM
    (fun (st : (ℕ → Matrix (Fin q) (Fin q) ℝ) × (ℕ → Matrix (Fin q) (Fin q) ℝ)) (i : ℕ) => do
      let X ← Chapter03.solveMultipleRHS rnd (st.2 i)ᵀ (E i)ᵀ
      let U ← Chapter01.algorithm_1_1_5 rnd (-Xᵀ) (F i) (D (i + 1))
      pure (Function.update st.1 i Xᵀ, Function.update st.2 (i + 1) U))
    (0, Function.update 0 0 (D 0))

/-- **Equation (4.5.5)** of [golub2013matrix], block forward elimination and block back substitution
as a program. Given $N$, the multipliers $L_i$ and the pivots $U_i$ of (4.5.3), the
superdiagonal blocks $F_i$ and a block vector $b$, the program computes $x$:
```
y_1 = b_1
for i = 2:N
    y_i = b_i − L_{i−1} y_{i−1}
end
Solve U_N x_N = y_N for x_N
for i = N−1:−1:1
    Solve U_i x_i = y_i − F_i x_{i+1} for x_i
end
```
The program is indexed from $0$, with $\mathbb{N}$-indexed block vectors; $y$ overwrites $b$,
and the entries of $x$ beyond $N$ are $0$. The block updates are Algorithm 1.1.3 with the
matrices $-L_{i-1}$ and $-F_i$, and each solve is Gaussian elimination with partial pivoting
followed by the triangular solves (`GolubVanLoan.Chapter03.solveGEPP`). Negation is exact.

**Reading.** The programs select the source's suggested Gaussian elimination with pivoting, specify
rounded block updates, and inherit the component solvers' totalized divisions for singular input.
Each program factors the blocks in its own calls to the solvers.
-/
noncomputable def blockTridiagonalSolve (N : ℕ) (L U F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (b : ℕ → Fin q → ℝ) : M (ℕ → Fin q → ℝ) := do
  let y ← (List.range N).foldlM (fun (y : ℕ → Fin q → ℝ) (i : ℕ) => do
      let v ← Chapter01.algorithm_1_1_3 rnd (-L i) (y i) (y (i + 1))
      pure (Function.update y (i + 1) v)) b
  let xN ← Chapter03.solveGEPP rnd (U N) (y N)
  (List.range N).reverse.foldlM (fun (x : ℕ → Fin q → ℝ) (i : ℕ) => do
      let c ← Chapter01.algorithm_1_1_3 rnd (-F i) (x (i + 1)) (y i)
      let xi ← Chapter03.solveGEPP rnd (U i) c
      pure (Function.update x i xi)) (Function.update 0 N xN)

end Programs

/-- **Equation (4.5.4)** of [golub2013matrix], exact correctness. Let
$E_i, D_i, F_i \in \mathbb{R}^{q \times q}$ for $i \in \mathbb{N}$, and let $U_i$ and $L_i$ be
the pivots and the multipliers of the recurrence (4.5.4). If $U_0, \dots, U_{N-1}$ are
nonsingular, then in exact arithmetic `GolubVanLoan.Chapter04.blockTridiagonalLU` returns the
multipliers $L_i$ for $i < N$ and the pivots $U_i$ for $i \le N$.

With `GolubVanLoan.Chapter04.equation_4_5_3`, the program therefore computes the factorization
(4.5.3). The pivots and the multipliers are `Matrix.tridiagonalLUPivot` and
`Matrix.tridiagonalLUMultiplier`.

**Reading.** Lean requires invertibility only for the pivots used when forming multipliers. The
source describes the procedure as defined when the pivots are nonsingular, with no separate
exception for the last pivot. Solving the full system still requires the last pivot.
-/
theorem equation_4_5_4 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hU : ∀ i < N, IsUnit (tridiagonalLUPivot E D F i)) :
    (∀ i < N, (Id.run (blockTridiagonalLU pure N E D F)).1 i = tridiagonalLUMultiplier E D F i) ∧
      ∀ i ≤ N, (Id.run (blockTridiagonalLU pure N E D F)).2 i = tridiagonalLUPivot E D F i := by
  have key := List.idRun_foldlM_induction' (List.range N)
    (fun k (st : (ℕ → Matrix (Fin q) (Fin q) ℝ) × (ℕ → Matrix (Fin q) (Fin q) ℝ)) =>
      (∀ i < k, st.1 i = tridiagonalLUMultiplier E D F i) ∧
        ∀ i ≤ k, st.2 i = tridiagonalLUPivot E D F i)
    (init := (0, Function.update 0 0 (D 0)))
    ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => by
      rw [Nat.le_zero.1 hi]
      simp⟩
    (f := fun (st : (ℕ → Matrix (Fin q) (Fin q) ℝ) × (ℕ → Matrix (Fin q) (Fin q) ℝ)) (i : ℕ) =>
      (do
        let X ← Chapter03.solveMultipleRHS (M := Id) pure (st.2 i)ᵀ (E i)ᵀ
        let U ← Chapter01.algorithm_1_1_5 (M := Id) pure (-Xᵀ) (F i) (D (i + 1))
        pure (Function.update st.1 i Xᵀ, Function.update st.2 (i + 1) U) : Id _))
    fun k hk st ⟨hL, hUk⟩ => by
      rw [List.length_range] at hk
      simp only [List.getElem_range, Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_5_spec]
      have hpiv := hUk k le_rfl
      have hu : IsUnit (st.2 k) := by rw [hpiv]; exact hU k hk
      have hX := (Chapter03.equation_3_4_12 ((isUnit_transpose _).2 hu) (E k)ᵀ).1
      set X := Id.run (Chapter03.solveMultipleRHS pure (st.2 k)ᵀ (E k)ᵀ)
      have hXt : Xᵀ = tridiagonalLUMultiplier E D F k := by
        have h1 : Xᵀ * st.2 k = E k := by
          simpa only [transpose_mul, transpose_transpose] using congrArg transpose hX
        rw [tridiagonalLUMultiplier, ← hpiv, ← h1, Matrix.mul_assoc,
          ← nonsing_inv_eq_ringInverse, mul_nonsing_inv _
            ((isUnit_iff_isUnit_det _).1 hu), Matrix.mul_one]
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · rw [Function.update_of_ne (by omega)]
          exact hL i hi
        · rw [Function.update_self, hXt]
      · rcases Nat.lt_or_eq_of_le hi with hi | rfl
        · rw [Function.update_of_ne (by omega)]
          exact hUk i (by omega)
        · rw [Function.update_self, hXt, tridiagonalLUPivot_succ, neg_mul, ← sub_eq_add_neg]
  rw [List.length_range] at key
  exact key

/-- The exact block forward elimination of (4.5.5): $y_0 = b_0$ and $y_{i+1} = b_{i+1} - L_i y_i$.
-/
private noncomputable def blockForwardSeq (L : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (b : ℕ → Fin q → ℝ) : ℕ → Fin q → ℝ
  | 0 => b 0
  | i + 1 => b (i + 1) - L i *ᵥ blockForwardSeq L b i

/-- **Equation (4.5.5)** of [golub2013matrix], exact correctness. Let
$E_i, D_i, F_i \in \mathbb{R}^{q \times q}$ for $i \in \mathbb{N}$, let $L_i$ and $U_i$ be the
multipliers and the pivots of the recurrence (4.5.4), and assume that $U_0, \dots, U_N$ are
nonsingular. Let $b_i \in \mathbb{R}^q$ for $i \in \mathbb{N}$, and let $x$ be the result of
`GolubVanLoan.Chapter04.blockTridiagonalSolve` in exact arithmetic with the blocks $L_i$, $U_i$
and $F_i$. Then $x$ solves the block tridiagonal system (4.5.1): for $i = 0, \dots, N$,
$$E_{i-1} x_{i-1} + D_i x_i + F_i x_{i+1} = b_i,$$
where the first term is absent for $i = 0$ and the last term is absent for $i = N$. -/
theorem equation_4_5_5 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hU : ∀ i ≤ N, IsUnit (tridiagonalLUPivot E D F i)) (b : ℕ → Fin q → ℝ) (i : ℕ)
    (hi : i ≤ N) :
    (if 0 < i then E (i - 1) *ᵥ
        Id.run (blockTridiagonalSolve pure N (tridiagonalLUMultiplier E D F)
          (tridiagonalLUPivot E D F) F b) (i - 1) else 0) +
      D i *ᵥ Id.run (blockTridiagonalSolve pure N (tridiagonalLUMultiplier E D F)
          (tridiagonalLUPivot E D F) F b) i +
      (if i < N then F i *ᵥ
        Id.run (blockTridiagonalSolve pure N (tridiagonalLUMultiplier E D F)
          (tridiagonalLUPivot E D F) F b) (i + 1) else 0) = b i := by
  set L := tridiagonalLUMultiplier E D F with hL
  set U := tridiagonalLUPivot E D F with hU'
  -- the forward elimination
  obtain ⟨g, hg⟩ : ∃ g : (ℕ → Fin q → ℝ) → ℕ → Id (ℕ → Fin q → ℝ), g = (fun y i => do
      let v ← Chapter01.algorithm_1_1_3 (M := Id) pure (-L i) (y i) (y (i + 1))
      pure (Function.update y (i + 1) v)) := ⟨_, rfl⟩
  obtain ⟨yf, hyf⟩ : ∃ yf, yf = Id.run ((List.range N).foldlM g b) := ⟨_, rfl⟩
  have hfwd := List.idRun_foldlM_induction' (List.range N)
    (fun k (y : ℕ → Fin q → ℝ) => (∀ j ≤ k, y j = blockForwardSeq L b j) ∧ ∀ j, k < j → y j = b j)
    (init := b) ⟨fun j hj => by rw [Nat.le_zero.1 hj]; rfl, fun _ _ => rfl⟩ (f := g)
    fun k hk y ⟨h1, h2⟩ => by
      rw [hg]
      simp only [List.getElem_range, Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_3_spec]
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_eq_of_le hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]
          exact h1 j (by omega)
        · rw [Function.update_self, h1 k le_rfl, h2 (k + 1) (by omega), neg_mulVec,
            ← sub_eq_add_neg]
          rfl
      · rw [Function.update_of_ne (by omega)]
        exact h2 j (by omega)
  rw [List.length_range, ← hyf] at hfwd
  -- the back substitution
  obtain ⟨h, hh⟩ : ∃ h : (ℕ → Fin q → ℝ) → ℕ → Id (ℕ → Fin q → ℝ), h = (fun x i => do
      let c ← Chapter01.algorithm_1_1_3 (M := Id) pure (-F i) (x (i + 1)) (yf i)
      let xi ← Chapter03.solveGEPP (M := Id) pure (U i) c
      pure (Function.update x i xi)) := ⟨_, rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℕ → Fin q → ℝ,
      x₀ = Function.update (0 : ℕ → Fin q → ℝ) N (Id.run (Chapter03.solveGEPP pure (U N) (yf N))) :=
    ⟨_, rfl⟩
  have hrun : Id.run (blockTridiagonalSolve pure N L U F b) =
      Id.run ((List.range N).reverse.foldlM h x₀) := by
    rw [hh, hx₀, hyf, hg]
    rfl
  have hback := List.idRun_foldlM_induction' (List.range N).reverse
    (fun k (x : ℕ → Fin q → ℝ) => ∀ j, N - k ≤ j → j ≤ N →
      U j *ᵥ x j + (if j < N then F j *ᵥ x (j + 1) else 0) = yf j)
    (init := x₀) (fun j hj hjN => by
      have hj : j = N := by omega
      subst hj
      rw [hx₀, ite_eq_right (lt_irrefl _), add_zero, Function.update_self]
      exact Chapter03.solveGEPP_spec (hU _ le_rfl) _) (f := h)
    fun k hk x hx => by
      rw [List.length_reverse, List.length_range] at hk
      have hidx : (List.range N).reverse[k]'(by simpa using hk) = N - 1 - k := by
        rw [List.getElem_reverse, List.getElem_range, List.length_range]
      rw [hidx, hh]
      simp only [Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_3_spec]
      intro j hj hjN
      rcases Nat.lt_or_eq_of_le hj with hj | hj
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hx j (by omega) hjN
      · obtain rfl : j = N - 1 - k := by omega
        rw [Function.update_self, Function.update_of_ne (by omega), ite_eq_left (by omega),
          Chapter03.solveGEPP_spec (hU _ (by omega)), neg_mulVec]
        abel
  rw [List.length_reverse, List.length_range, ← hrun] at hback
  set x := Id.run (blockTridiagonalSolve pure N L U F b) with hx
  have hB : ∀ j ≤ N, U j *ᵥ x j + (if j < N then F j *ᵥ x (j + 1) else 0) =
      blockForwardSeq L b j := fun j hj => by
    rw [hback j (by omega) hj, hfwd.1 j hj]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [ite_eq_right (lt_irrefl 0), zero_add]
    exact hB 0 hi
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hEj : E j = L j * U j := (tridiagonalLUMultiplier_mul_tridiagonalLUPivot E D F
      (hU j (by omega))).symm
    have hDj : D (j + 1) = U (j + 1) + L j * F j := by
      rw [hU', tridiagonalLUPivot_succ]
      abel
    have hBj := hB j (by omega)
    rw [ite_eq_left (by omega : j < N)] at hBj
    have h2 := hB (j + 1) hi
    simp only [blockForwardSeq] at h2
    rw [← hBj, mulVec_add, eq_sub_iff_add_eq] at h2
    rw [ite_eq_left hi0, Nat.add_sub_cancel, hEj, hDj, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      ← h2]
    abel

/-! ### §4.5.2 Block diagonal dominance -/

/-- **Equation (4.5.6)** of [golub2013matrix]. Let $E_i, D_i, F_i \in \mathbb{R}^{q \times q}$ for
$i \in \mathbb{N}$, and let $A$ be the block tridiagonal matrix with diagonal blocks
$D_0, \dots, D_N$. Assume that $A$ is block diagonally dominant: for $i = 0, \dots, N$, the
block $D_i$ is nonsingular and
$$\|D_i^{-1}\|_1 \left(\|F_{i-1}\|_1 + \|E_i\|_1\right) < 1,$$
where $\|F_{-1}\|_1$ and $\|E_N\|_1$ are read as $0$. Then the pivots $U_0, \dots, U_N$ of the
recurrence (4.5.4) are nonsingular, so that the factorization (4.5.3) exists, and $A$ is
nonsingular.

The source states the condition with $E_N \equiv F_0 \equiv 0$ in its $1$-based indexing, and it
presupposes that the $D_i$ are nonsingular. The nonsingularity of $A$ is part (a) of Problem
P4.5.1 of the source. The norm is `Matrix.lpOpNorm 1`. -/
theorem equation_4_5_6 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    (∀ i ≤ N, IsUnit (tridiagonalLUPivot E D F i)) ∧
      IsUnit (blockTridiagonal (N := N) (fun i => E i) (fun i => D i) (fun i => F i)) := by
  have hdom := (isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
  exact ⟨fun i hi => (hdom.isUnit_tridiagonalLUPivot hi).1, hdom.isUnit_blockTridiagonal⟩

/-- **Equation (4.5.7)** of [golub2013matrix]. Let $E_i, D_i, F_i \in \mathbb{R}^{q \times q}$ for
$i \in \mathbb{N}$ satisfy the block diagonal dominance (4.5.6): for $i = 0, \dots, N$, $D_i$ is
nonsingular and $\|D_i^{-1}\|_1 (\|F_{i-1}\|_1 + \|E_i\|_1) < 1$, with $\|F_{-1}\|_1$ and
$\|E_N\|_1$ read as $0$. Then the multipliers of the factorization (4.5.3) satisfy
$$\|L_i\|_1 \le 1, \qquad i = 0, \dots, N-1.$$
-/
theorem equation_4_5_7 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    ∀ i < N, lpOpNorm 1 (tridiagonalLUMultiplier E D F i) ≤ 1 := fun _ hi =>
  ((isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
    ).lpOpNorm_tridiagonalLUMultiplier_le hi

/-- **Equation (4.5.8)** of [golub2013matrix]. Let $E_i, D_i, F_i \in \mathbb{R}^{q \times q}$ for
$i \in \mathbb{N}$ satisfy the block diagonal dominance (4.5.6): for $i = 0, \dots, N$, $D_i$ is
nonsingular and $\|D_i^{-1}\|_1 (\|F_{i-1}\|_1 + \|E_i\|_1) < 1$, with $\|F_{-1}\|_1$ and
$\|E_N\|_1$ read as $0$. Let $A$ be the block tridiagonal matrix with diagonal blocks
$D_0, \dots, D_N$. Then the pivots of the factorization (4.5.3) satisfy
$$\|U_i\|_1 \le \|A\|_1, \qquad i = 0, \dots, N.$$

**Reading.** The source prints $\|U_i\|_1 \le \|A_n\|_1$. The symbol $A_n$ has no referent in
the section, and it is read as the whole matrix $A$. -/
theorem equation_4_5_8 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    ∀ i ≤ N, lpOpNorm 1 (tridiagonalLUPivot E D F i) ≤
      lpOpNorm 1 (blockTridiagonal (N := N) (fun i => E i) (fun i => D i) (fun i => F i)) :=
  fun _ hi => ((isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
    ).lpOpNorm_tridiagonalLUPivot_le hi

/-! ### §4.5.3 Block cyclic reduction -/

open CyclicReduction in
/-- **Section 4.5.3** of [golub2013matrix], one step of block cyclic reduction. Let
$D, F \in \mathbb{R}^{q \times q}$ with $DF = FD$, and let $T$ be the operator of the
constant-block system (4.5.9), $(Tx)_i = F x_{i-1} + D x_i + F x_{i+1}$, where a missing
neighbour is $0$.

1. For every $M$, if $Tx = b$ for block vectors $x, b$ with $2M + 1$ blocks, then the
   odd-indexed unknowns $x_1, x_3, \dots, x_{2M-1}$ solve the system of the same form with $M$
   blocks, the blocks $D^{(1)} = 2F^2 - D^2$ and $F^{(1)} = F^2$, and the right-hand side
   $b^{(1)}_j = F(b_{2j} + b_{2j+2}) - D b_{2j+1}$.
2. The new blocks commute: $D^{(1)} F^{(1)} = F^{(1)} D^{(1)}$.
3. For every $k$, if $Tx = b$ for block vectors with $2^{k+1} - 1$ blocks, then the middle
   unknown solves the single $q \times q$ system $D^{(k)} x_{2^k - 1} = b^{(k)}$, where
   $D^{(k)}$ and $b^{(k)}$ are the diagonal block and the right-hand side after $k$ reduction
   steps.

The source obtains the reduced system by multiplying the equations $i - 1$, $i$ and $i + 1$ by
$F$, $-D$ and $F$ and adding them, and it illustrates the step for $N = 7$. Indices start at
$0$, so the source's even-indexed unknowns are the odd-indexed ones here. The operator is
`CyclicReduction.constBlockTridiagonal`, the new data are `CyclicReduction.reducedDiag`,
`CyclicReduction.reducedOff` and `CyclicReduction.reducedRhs`, and the data after $k$ steps are
`CyclicReduction.diagIter` and `CyclicReduction.rhsIter`. The size $2^{k+1} - 1$ is
`CyclicReduction.size (k + 1)`.

**Generalization.** A single reduction applies to any odd block count. The iterated reduction to one
block retains the source's power-of-two-minus-one size.
-/
theorem cyclicReduction_step {D F : Matrix (Fin q) (Fin q) ℝ} (hDF : D * F = F * D) :
    (∀ (M : ℕ) (x b : Fin (2 * M + 1) → Fin q → ℝ), constBlockTridiagonal D F x = b →
      constBlockTridiagonal (reducedDiag D F) (reducedOff F)
        (fun j : Fin M => x ⟨2 * j + 1, by omega⟩) = reducedRhs D F b) ∧
    reducedDiag D F * reducedOff F = reducedOff F * reducedDiag D F ∧
    (∀ (k : ℕ) (x b : Fin (size (k + 1)) → Fin q → ℝ), constBlockTridiagonal D F x = b →
      diagIter k D F *ᵥ x ⟨size k, by simp only [size]; omega⟩ = rhsIter k D F b) :=
  ⟨fun _ _ _ h => constBlockTridiagonal_reduce hDF h, commute_reduced hDF,
    fun k _ _ h => constBlockTridiagonal_iterate_reduce k hDF h⟩

open CyclicReduction in
/-- **Section 4.5.3** of [golub2013matrix], the back substitution of block cyclic reduction. Let
$D, F \in \mathbb{R}^{q \times q}$, and let $x, b$ be block vectors with $2M + 1$ blocks such
that $Tx = b$ for the constant-block operator of (4.5.9). Then for $j = 0, \dots, M$ the
even-indexed unknowns solve the $q \times q$ systems
$$D x_{2j} = b_{2j} - F(x_{2j-1} + x_{2j+1}),$$
where $x_{-1}$ and $x_{2M+1}$ are read as $0$.

Indices start at $0$, so these are the source's odd-indexed unknowns, which it computes last
from the first, third, fifth and seventh equations of the original system. The missing
neighbours are read through the zero extension `CyclicReduction.extend`. The statement needs no
commutativity of $D$ and $F$.

**Generalization.** Lean proves the local recovery equations at any odd block count, with no
commutativity assumption. The equations hold of a solution even if the recovery block is singular.
-/
theorem cyclicReduction_back {D F : Matrix (Fin q) (Fin q) ℝ} {M : ℕ}
    {x b : Fin (2 * M + 1) → Fin q → ℝ} (h : constBlockTridiagonal D F x = b) (j : Fin (M + 1)) :
    D *ᵥ x ⟨2 * j, by omega⟩ =
      b ⟨2 * j, by omega⟩ - F *ᵥ (extend x (2 * (j : ℕ) - 1) + extend x (2 * (j : ℕ) + 1)) :=
  constBlockTridiagonal_even_eq h j

/-! ### §4.5.4 The SPIKE framework -/

/-- In the block ring, $\operatorname{diag}(D_i^{-1}) \operatorname{tridiag}(E, D, F) =
\operatorname{tridiag}(\tilde E, I, \tilde F)$ with $\tilde F_i = D_i^{-1} F_i$ and
$\tilde E_i = D_{i+1}^{-1} E_i$.

**Generalization.** This scaling identity uses any number of equal-sized blocks and requires only
invertible diagonal blocks. The SPIKE example uses four blocks with banded diagonal blocks and
sparse off-diagonal blocks.
-/
private theorem diagonal_inv_mul_tridiagonalOf (E F : Fin N → Matrix (Fin q) (Fin q) ℝ)
    (D : Fin (N + 1) → Matrix (Fin q) (Fin q) ℝ) (hD : ∀ i, IsUnit (D i)) :
    diagonal (fun i => (D i)⁻¹) * tridiagonalOf E D F =
      tridiagonalOf (fun i => (D i.succ)⁻¹ * E i) (fun _ => 1)
        (fun i => (D i.castSucc)⁻¹ * F i) := by
  ext1 i j
  have hi := i.isLt
  have hj := j.isLt
  rw [diagonal_mul]
  simp only [tridiagonalOf, of_apply]
  split_ifs with h1 h2 h3
  · rw [Fin.ext h1]
    exact nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (hD j))
  · have e : (⟨j, by omega⟩ : Fin N).succ = i := Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [e]
  · congr 2
  · rw [Matrix.mul_zero]

/-- **Equations (4.5.13)→(4.5.14)** of [golub2013matrix], the SPIKE scaling. Let
$E_0, \dots, E_{N-1}$, $D_0, \dots, D_N$ and $F_0, \dots, F_{N-1}$ be in
$\mathbb{R}^{q \times q}$, with every $D_i$ nonsingular, and let $A$ be the block tridiagonal
matrix with these blocks. Then
$$\operatorname{diag}(D_0^{-1}, \dots, D_N^{-1})\, A = \tilde A,$$
where $\tilde A$ is the block tridiagonal matrix with identity diagonal blocks, superdiagonal
blocks $\tilde F_i = D_i^{-1} F_i$ and subdiagonal blocks $\tilde E_i = D_{i+1}^{-1} E_i$.
Moreover, for all $x, b \in \mathbb{R}^{(N+1)q}$, $Ax = b$ if and only if
$\tilde A x = \tilde b$, where $\tilde b_i = D_i^{-1} b_i$.

The source premultiplies by the inverse of $\operatorname{diag}(D_1, D_2, D_3, D_4)$ and writes
$D_i \tilde b_i = b_i$, $D_i \tilde F_i = F_i$ and $D_{i+1} \tilde E_i = E_i$. The block
diagonal matrix is the flattening of `Matrix.diagonal` over the block ring by `Matrix.comp`.

**Generalization.** This scaling identity uses any number of equal-sized blocks and requires only
invertible diagonal blocks. The SPIKE example uses four blocks with banded diagonal blocks and
sparse off-diagonal blocks.
-/
theorem equation_4_5_14 (E F : Fin N → Matrix (Fin q) (Fin q) ℝ)
    (D : Fin (N + 1) → Matrix (Fin q) (Fin q) ℝ) (hD : ∀ i, IsUnit (D i)) :
    comp _ _ _ _ ℝ (diagonal fun i => (D i)⁻¹) * blockTridiagonal E D F =
        blockTridiagonal (fun i => (D i.succ)⁻¹ * E i) (fun _ => 1)
          (fun i => (D i.castSucc)⁻¹ * F i) ∧
      ∀ x b : Fin (N + 1) × Fin q → ℝ, blockTridiagonal E D F *ᵥ x = b ↔
        blockTridiagonal (fun i => (D i.succ)⁻¹ * E i) (fun _ => 1)
            (fun i => (D i.castSucc)⁻¹ * F i) *ᵥ x =
          fun p => ((D p.1)⁻¹ *ᵥ fun k => b (p.1, k)) p.2 := by
  have hmul : comp _ _ _ _ ℝ (diagonal fun i => (D i)⁻¹) * blockTridiagonal E D F =
      blockTridiagonal (fun i => (D i.succ)⁻¹ * E i) (fun _ => 1)
        (fun i => (D i.castSucc)⁻¹ * F i) := by
    simp only [blockTridiagonal, ← compRingEquiv_apply, ← map_mul]
    rw [diagonal_inv_mul_tridiagonalOf E F D hD]
  refine ⟨hmul, fun x b => ?_⟩
  set P := comp _ _ _ _ ℝ (diagonal fun i => (D i)⁻¹)
  have hQP : comp _ _ _ _ ℝ (diagonal D) * P = 1 := by
    simp only [P, ← compRingEquiv_apply, ← map_mul, diagonal_mul_diagonal]
    rw [← map_one (compRingEquiv (Fin (N + 1)) (Fin q) ℝ), ← diagonal_one]
    congr 2
    funext i
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (hD i))
  have hb : P *ᵥ b = fun p => ((D p.1)⁻¹ *ᵥ fun k => b (p.1, k)) p.2 := by
    ext ⟨i, k⟩
    simp only [P, mulVec, dotProduct, comp_apply, Fintype.sum_prod_type, diagonal_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  rw [← hmul, ← mulVec_mulVec, ← hb]
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg (comp _ _ _ _ ℝ (diagonal D) *ᵥ ·) h
    simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hQP, Matrix.one_mul, one_mulVec] using h'

end GolubVanLoan.Chapter04
