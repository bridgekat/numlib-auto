import Numlib.Direct.CyclicReduction
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter03.Section04

/-!
# Golub–Van Loan §4.5: block tridiagonal systems

Surface file for [golub2013matrix] §4.5: the block LU factorization (4.5.3) with its recurrence
(4.5.4) and the block substitutions (4.5.5) as programs, block diagonal dominance (4.5.6) and its
consequences (4.5.7)–(4.5.8), one step of block cyclic reduction and its back substitution (§4.5.3),
and the block scaling (4.5.13)→(4.5.14) of the
SPIKE framework. The section has no numbered theorem and no numbered algorithm.

## Conventions

The matrix (4.5.2) has `q × q` real blocks, `N + 1` diagonal blocks `D 0, …, D N` (0-based; the
book's `D_1, …, D_N` with `N` one larger), subdiagonal blocks `E 0, …, E (N − 1)` and superdiagonal
blocks `F 0, …, F (N − 1)`. In the block ring `Matrix (Fin q) (Fin q) ℝ` it is
`Matrix.tridiagonalOf E D F`, and the book's scalar matrix is its flattening
`Matrix.blockTridiagonal E D F : Matrix (Fin (N + 1) × Fin q) (Fin (N + 1) × Fin q) ℝ` by Mathlib's
`Matrix.comp` (a ring isomorphism, `Matrix.compRingEquiv`). The block recurrence (4.5.4) is the
backbone's `ℕ`-indexed `Matrix.tridiagonalLUPivot` (`U_i`) and `Matrix.tridiagonalLUMultiplier`
(`L_i`), so the blocks of the §4.5.1–4.5.2 statements are `ℕ`-indexed families. The book's `‖·‖₁`
of a block is `Matrix.lpOpNorm 1`. The constant-block system (4.5.9) is the backbone operator
`CyclicReduction.constBlockTridiagonal D F`, which is `Matrix.blockTridiagonal` applied to the
flattened vector (`CyclicReduction.constBlockTridiagonal_eq_blockTridiagonal_mulVec`).

The algorithm-shaped displays (4.5.4) and (4.5.5) are the programs `blockTridiagonalLU` and
`blockTridiagonalSolve` (the algorithm conventions of `NumlibSurface/GolubVanLoan`), with exact
specifications `equation_4_5_4` (the backbone recurrence) and `equation_4_5_5` (the block system
is solved). Their block solves call chapter 3's Gaussian elimination with partial pivoting
(`Chapter03.solveMultipleRHS`, `Chapter03.solveGEPP`) and their block products chapter 1's
Algorithms 1.1.3 and 1.1.5, as the book suggests.

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/BlockTridiagonal` (the recurrence, the factorization, block
dominance) and `Numlib/Direct/CyclicReduction`. The flop count of cyclic reduction, Buneman's
stabilization and the rest of the SPIKE framework (whose displays (4.5.11)–(4.5.12) and the refined
blockings were lost in conversion) are not formalized.

## Readings and errata

(4.5.8) prints `‖U_i‖₁ ≤ ‖A_n‖₁`, whose right-hand side has no referent in the section; it is read
as the `1`-norm of the whole matrix `A`. The `N = 7` display of §4.5.3 prints
`b₄ = F x₅ + D x₄ + F x₅` for `b₄ = F x₃ + D x₄ + F x₅`.
-/

open Matrix Finset

namespace GolubVanLoan.Chapter04

variable {N q : ℕ}

/-! ### §4.5.1 Block tridiagonal LU factorization -/

/-- **(4.5.3) with (4.5.4).** "By comparing blocks in `A = L U` we formally obtain the following
algorithm for computing the `L_i` and `U_i`: `U_1 = D_1`; for `i = 2:N`, solve `L_{i−1} U_{i−1} =
E_{i−1}` for `L_{i−1}`, `U_i = D_i − L_{i−1} F_{i−1}`. The procedure is defined as long as the `U_i`
are nonsingular." If the pivots `U_0, …, U_{N−1}` are nonsingular, the block tridiagonal matrix is
the product of the block unit lower bidiagonal matrix with subdiagonal blocks `L_i` and the block
upper bidiagonal matrix with diagonal blocks `U_i` and superdiagonal blocks `F_i`; the multipliers
solve `L_i U_i = E_i`. -/
theorem equation_4_5_3 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hU : ∀ i < N, IsUnit (tridiagonalLUPivot E D F i)) :
    blockTridiagonal (N := N) (fun i => E i) (fun i => D i) (fun i => F i) =
        blockTridiagonal (fun i => tridiagonalLUMultiplier E D F i) 1 0 *
          blockTridiagonal 0 (fun i => tridiagonalLUPivot E D F i) (fun i => F i) ∧
      ∀ i < N, tridiagonalLUMultiplier E D F i * tridiagonalLUPivot E D F i = E i := by
  refine ⟨?_, fun i hi => tridiagonalLUMultiplier_mul_tridiagonalLUPivot E D F (hU i hi)⟩
  simp only [blockTridiagonal, ← compRingEquiv_apply, ← map_mul]
  rw [tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot E D F hU]

/-! ### (4.5.4)–(4.5.5): the block programs -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **(4.5.4), the block LU recurrence as a program**:
```
U_1 = D_1
for i = 2:N
    Solve L_{i−1} U_{i−1} = E_{i−1} for L_{i−1}.
    U_i = D_i − L_{i−1} F_{i−1}
end
```
0-based, on the state `(L, U)` of `ℕ`-indexed block families. "Each `U_i` must be factored since
linear systems involving these submatrices are solved. This could be done using Gaussian
elimination with pivoting": the solve `L U = E` is the transposed system `Uᵀ Lᵀ = Eᵀ` by chapter
3's multiple right-hand side procedure (3.4.12) (`Chapter03.solveMultipleRHS`, Gaussian
elimination with partial pivoting; transposition is a copy), and `D_i − L F` is chapter 1's
Algorithm 1.1.5 on `C = D_i`, `A = −L` (negation is exact). -/
noncomputable def blockTridiagonalLU (N : ℕ) (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ) :
    M ((ℕ → Matrix (Fin q) (Fin q) ℝ) × (ℕ → Matrix (Fin q) (Fin q) ℝ)) :=
  (List.range N).foldlM
    (fun (st : (ℕ → Matrix (Fin q) (Fin q) ℝ) × (ℕ → Matrix (Fin q) (Fin q) ℝ)) (i : ℕ) => do
      let X ← Chapter03.solveMultipleRHS rnd (st.2 i)ᵀ (E i)ᵀ
      let U ← Chapter01.algorithm_1_1_5 rnd (-Xᵀ) (F i) (D (i + 1))
      pure (Function.update st.1 i Xᵀ, Function.update st.2 (i + 1) U))
    (0, Function.update 0 0 (D 0))

/-- **(4.5.5), block forward elimination and block back substitution** with the factors `L_i`,
`U_i` of (4.5.3) and the superdiagonal blocks `F_i`:
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
0-based, with `ℕ`-indexed block vectors (`y` overwrites `b`). The block gaxpys are chapter 1's
Algorithm 1.1.3 with `A = −L_{i−1}`, `−F_i` (negation is exact), and the solves are Gaussian
elimination with partial pivoting followed by the triangular solves (`Chapter03.solveGEPP`). -/
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

/-- **Exact correctness of (4.5.4)**: if the pivots `U_0, …, U_{N−1}` used by the solves are
nonsingular, the exact run computes the multipliers `L_i = tridiagonalLUMultiplier E D F i`
(`i < N`) and the pivots `U_i = tridiagonalLUPivot E D F i` (`i ≤ N`) of the backbone recurrence,
hence the factorization (4.5.3) (`equation_4_5_3`). -/
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

/-- The exact block forward elimination of (4.5.5): `y_0 = b_0`, `y_{i+1} = b_{i+1} − L_i y_i`. -/
private noncomputable def blockForwardSeq (L : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (b : ℕ → Fin q → ℝ) : ℕ → Fin q → ℝ
  | 0 => b 0
  | i + 1 => b (i + 1) - L i *ᵥ blockForwardSeq L b i

/-- **Exact correctness of (4.5.5)**: with the exact factors of (4.5.4) — the multipliers
`L_i = tridiagonalLUMultiplier E D F i` and the pivots `U_i = tridiagonalLUPivot E D F i`, all
nonsingular — the exact run of the block substitutions solves the block tridiagonal system (4.5.1),
`E_{i−1} x_{i−1} + D_i x_i + F_i x_{i+1} = b_i` for `i = 0:N` (a missing neighbour omitted). -/
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

/-- **(4.5.6).** "If we have `‖D_i⁻¹‖₁ (‖F_{i−1}‖₁ + ‖E_i‖₁) < 1`, `E_N ≡ F_0 ≡ 0`, for
`i = 1:N`, then the factorization (4.5.3) exists": every pivot `U_i` is nonsingular (so (4.5.3)
holds, `equation_4_5_3`), and the matrix `A` itself is nonsingular (the book's P4.5.1(a)). The
condition is stated 0-based, with the nonsingularity of the `D_i` it presupposes. -/
theorem equation_4_5_6 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    (∀ i ≤ N, IsUnit (tridiagonalLUPivot E D F i)) ∧
      IsUnit (blockTridiagonal (N := N) (fun i => E i) (fun i => D i) (fun i => F i)) := by
  have hdom := (isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
  exact ⟨fun i hi => (hdom.isUnit_tridiagonalLUPivot hi).1, hdom.isUnit_blockTridiagonal⟩

/-- **(4.5.7).** Under the block diagonal dominance (4.5.6), the multipliers of (4.5.3) satisfy
`‖L_i‖₁ ≤ 1`. -/
theorem equation_4_5_7 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    ∀ i < N, lpOpNorm 1 (tridiagonalLUMultiplier E D F i) ≤ 1 := fun _ hi =>
  ((isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
    ).lpOpNorm_tridiagonalLUMultiplier_le hi

/-- **(4.5.8)**, read as `‖U_i‖₁ ≤ ‖A‖₁`: under the block diagonal dominance (4.5.6), the pivots of
(4.5.3) are bounded by the `1`-norm of the whole block tridiagonal matrix `A` (the printed
`‖A_n‖₁` has no referent in the section). -/
theorem equation_4_5_8 (E D F : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (h : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
      ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1))) + (if i < N then lpOpNorm 1 (E i) else 0))
        < 1) :
    ∀ i ≤ N, lpOpNorm 1 (tridiagonalLUPivot E D F i) ≤
      lpOpNorm 1 (blockTridiagonal (N := N) (fun i => E i) (fun i => D i) (fun i => F i)) :=
  fun _ hi => ((isStrictBlockColDiagDominant_tridiagonalOf_iff (N := N) E D F).2 h
    ).lpOpNorm_tridiagonalLUPivot_le hi

/-! ### §4.5.3 Block-cyclic reduction -/

open CyclicReduction in
/-- **§4.5.3, block cyclic reduction.** For the system (4.5.9) with constant blocks `D`, `F`
satisfying `D F = F D`: "for `i = 2, 4, 6` we multiply equations `i − 1`, `i`, and `i + 1` by `F`,
`−D`, and `F`, respectively, and add the resulting equations"; "we have removed the odd-indexed
`x_i` and are left with a reduced block tridiagonal system … where `D⁽¹⁾ = 2F² − D²` and
`F⁽¹⁾ = F²` commute." In general (0-based, `2M + 1` unknowns): the unknowns `x_1, x_3, …` solve the
system of the same form with blocks `D⁽¹⁾ = 2F² − D²` (`reducedDiag`), `F⁽¹⁾ = F²` (`reducedOff`)
and right-hand side `b⁽¹⁾_j = F (b_{2j} + b_{2j+2}) − D b_{2j+1}` (`reducedRhs`); the new blocks
commute; and for `N = 2^{k+1} − 1` unknowns (`size (k + 1)`) the reduction repeated `k` times
leaves "a single `q × q` system" `D_k x_{2^k − 1} = b_k` for the middle unknown. -/
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
/-- **§4.5.3, the back substitution.** "The vectors `x_2` and `x_6` are then found by solving the
systems `D⁽¹⁾ x_2 = b⁽¹⁾_2 − F⁽¹⁾ x_4`, … Finally, we use the first, third, fifth, and seventh
equations in the original system to compute `x_1, x_3, x_5`, and `x_7`": once the odd-indexed
unknowns (0-based) are known, the even-indexed ones solve `q × q` systems with matrix `D`,
`D x_{2j} = b_{2j} − F (x_{2j−1} + x_{2j+1})`, a missing neighbour being zero (`extend`). -/
theorem cyclicReduction_back {D F : Matrix (Fin q) (Fin q) ℝ} {M : ℕ}
    {x b : Fin (2 * M + 1) → Fin q → ℝ} (h : constBlockTridiagonal D F x = b) (j : Fin (M + 1)) :
    D *ᵥ x ⟨2 * j, by omega⟩ =
      b ⟨2 * j, by omega⟩ - F *ᵥ (extend x (2 * (j : ℕ) - 1) + extend x (2 * (j : ℕ) + 1)) :=
  constBlockTridiagonal_even_eq h j

/-! ### §4.5.4 The SPIKE framework -/

/-- The block scaling in the block ring: `diag(D_i⁻¹) · tridiag(E, D, F) = tridiag(Ẽ, I, F̃)` with
`F̃_i = D_i⁻¹ F_i` and `Ẽ_i = D_{i+1}⁻¹ E_i`. -/
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

/-- **(4.5.13)→(4.5.14), the SPIKE scaling.** "If we premultiply the above matrix by the inverse of
`diag(D_1, D_2, D_3, D_4)`, then … the original linear system (4.5.13) transforms to (4.5.14),
where `D_i b̃_i = b_i`, `D_i F̃_i = F_i`, and `D_{i+1} Ẽ_i = E_i`": for nonsingular diagonal blocks,
`diag(D_i⁻¹) A` is the block tridiagonal matrix with identity diagonal blocks, superdiagonal
blocks `F̃_i = D_i⁻¹ F_i` and subdiagonal blocks `Ẽ_i = D_{i+1}⁻¹ E_i`, and `A x = b` iff
`(diag(D_i⁻¹) A) x = b̃` with `b̃_i = D_i⁻¹ b_i`. -/
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
