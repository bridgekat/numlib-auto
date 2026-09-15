import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section09

/-!
# Quarteroni–Sacco–Saleri §3.10: accuracy of the solution achieved using GEM

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.10, over the backbone `Numlib/FloatingPoint/LU` (the backward error
of the LU solve, `FloatingPoint.exists_roundsLU_solve_eq`, and Wilkinson's normwise bound
`FloatingPoint.linfty_opNorm_le_of_roundsLU_solve`) and `Numlib/LinearAlgebra/Matrix/LU/Pivoting`
(the growth factor `Matrix.growthFactor` and its bounds).

## Conventions

The computed solution `x̂` of `A x = b` by GEM is described relationally: computed factors
`L̂`, `Û` (an admissible `FloatingPoint.RoundsLU m A L̂ Û`), then a forward substitution
`FloatingPoint.RoundsForwardSubst m L̂ b ŷ` and a backward substitution
`FloatingPoint.RoundsBackSubst m Û ŷ x̂`, all in the relational model
`m : FloatingPoint.RoundingModel ℝ` of `Numlib/FloatingPoint/Model` with unit roundoff `m.u`;
`γ_k = k u / (1 - k u)` is `FloatingPoint.gamma m.u k`. The book's displays (3.64), (3.65),
(3.67) are first order in `u` (`+ O(u²)`); the surface states the rigorous `γ`-forms of
[higham2002accuracy] Theorems 9.4 and 9.5, whose leading terms are the book's constants up to a
factor. The growth factor `ρ_n` of (3.66) is `Matrix.growthFactor A`, defined on the *exact*
stages `Matrix.gemStage A k` of Gaussian elimination without pivoting; for GEM with partial
pivoting it is `growthFactor (P A)` with `P` the permutation matrix of §3.5 (the pivoted
stages are the plain stages of `P A` up to the order of the rows). `max_{i,j} |a_ij|` is
`Matrix.supAbs A`. Norms are the `∞`-norms of §3.1: `‖A‖_∞` is Mathlib's scoped
`Matrix.Norms.Operator` instance, `‖x‖_∞` the sup norm of `Fin n → ℝ`, `K_∞(A) = condNumber ⊤ A`.

## Contents

* `equation_3_64`, `equation_3_65`, `equation_3_66`, `equation_3_66_spec`, `equation_3_67` —
  the backward error of GEM and the growth factor.
* `growthFactor_le_two_pow`, `growthFactor_tridiagonal`, `growthFactor_hessenberg`,
  `growthFactor_posDef`, `growthFactor_colDiagDominant` — the bounds on `ρ_n`; the banded bound
  (Bohte) and the complete-pivoting bound (Wilkinson) are planned as not formalized. The backbone
  proves a weaker banded bound with the same qualitative content, `ρ_n ≤ 2^{p+q}` for lower
  bandwidth `p` and upper bandwidth `q` (`Matrix.growthFactor_le_two_pow_of_hasBandwidth`); it is
  not restated here because it is not the book's inequality.
* `example_3_7_cond`, `example_3_7_lu`, `residual_error_bound`, `example_3_8`, `equation_3_69`
  — the examples and the role of the condition number.

## Readings and errata

(3.64) prints `|δA| ≤ n u (3|A| + 5|L̂||Û|) + O(u²)` (Golub–Van Loan); the rigorous statement is
`|δA| ≤ γ_{3n} |L̂||Û|` with `γ_{3n} = 3 n u + O(u²)`, which implies the printed one since
`|A| ≤ |L̂||Û| + O(u)` by (3.40). (3.66) defines `ρ_n` with the computed entries `â^{(k)}_ij`;
bounds are available only for the exact stages ([higham2002accuracy], after Theorem 9.5), and
(3.67) is stated in Higham's conditional form: under `|l̂_ij| ≤ 1` and `|û_ij| ≤ ρ max |a_ij|` —
the facts about the exact factors that the book, like Higham, borrows for the computed ones —
`‖δA‖_∞ ≤ n² γ_{3n} ρ ‖A‖_∞`, which is the book's `8 u n³ ρ_n ‖A‖_∞` up to the constant. Item
(4) of the growth-factor list says "strictly diagonally dominant by columns"; the bound holds for
nonsingular weakly dominant matrices, which the strict ones are.
-/

open Finset Matrix
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### (3.64)–(3.67): the backward error of GEM and the growth factor -/

section Backward

open FloatingPoint
open scoped Matrix.Norms.Operator

variable {m : RoundingModel ℝ} {A L U : Matrix (Fin n) (Fin n) ℝ} {b y x : Fin n → ℝ}

/-- **(3.64), rigorous form.** The solution `x̂` computed by GEM in floating-point arithmetic
with unit roundoff `u`, `3 n u < 1` — computed factors `L̂`, `Û` with nonzero pivots, then the two
substitutions — is the exact solution of a perturbed system `(A + δA) x̂ = b` with
`|δA| ≤ γ_{3n} |L̂| |Û|`, `γ_{3n} = 3 n u / (1 - 3 n u) = 3 n u + O(u²)` (backbone
`FloatingPoint.exists_roundsLU_solve_eq`, [higham2002accuracy] Theorem 9.4). The book's
`n u (3|A| + 5|L̂||Û|) + O(u²)` follows, since `|A| ≤ |L̂||Û| + O(u)` by (3.40). -/
theorem equation_3_64 [NeZero n] (hn : ((3 * n : ℕ) : ℝ) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) (hy : RoundsForwardSubst m L b y) (hx : RoundsBackSubst m U y x) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ ((3 * n : ℕ) * m.u / (1 - (3 * n : ℕ) * m.u)) • (L.abs * U.abs) ∧
        (A + δA) *ᵥ x = b := by
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by norm_num) (NeZero.ne n))
    nlinarith [m.u_nonneg]
  obtain ⟨δA, hδA, hAx⟩ := exists_roundsLU_solve_eq hu (by rwa [Fintype.card_fin]) h hd hy hx
  refine ⟨δA, ?_, hAx⟩
  rwa [Fintype.card_fin, gamma_def] at hδA

/-- The `∞`-norm of the entrywise absolute value is the `∞`-norm. -/
private theorem linfty_opNorm_abs (B : Matrix (Fin n) (Fin n) ℝ) : ‖B.abs‖ = ‖B‖ :=
  le_antisymm (linfty_opNorm_le_of_abs_entrywiseLE fun i j => by simp)
    (linfty_opNorm_le_of_abs_entrywiseLE fun i j => by simp)

/-- **(3.65), rigorous form.** With partial pivoting the entries of `L̂` are bounded by `1`, so
`‖L̂‖_∞ ≤ n` and (3.64) becomes `‖δA‖_∞ ≤ n γ_{3n} ‖Û‖_∞` for the perturbation `δA` of (3.64)
(backbone `Matrix.linfty_opNorm_le_of_abs_entrywiseLE` and the submultiplicativity of `‖·‖_∞`);
the book's `n u (3‖A‖_∞ + 5 n ‖Û‖_∞) + O(u²)` follows as for (3.64). -/
theorem equation_3_65 [NeZero n] (hn : ((3 * n : ℕ) : ℝ) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) (hy : RoundsForwardSubst m L b y) (hx : RoundsBackSubst m U y x)
    (hL : ∀ i j, |L i j| ≤ 1) :
    ‖L‖ ≤ n ∧ ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      ‖δA‖ ≤ n * ((3 * n : ℕ) * m.u / (1 - (3 * n : ℕ) * m.u)) * ‖U‖ ∧ (A + δA) *ᵥ x = b := by
  have hLn : ‖L‖ ≤ n := linfty_opNorm_le_of_forall_sum_le (Nat.cast_nonneg n) fun i => by
    calc ∑ j, |L i j| ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => hL i j
      _ = n := by simp
  obtain ⟨δA, hδA, hAx⟩ := equation_3_64 hn h hd hy hx
  refine ⟨hLn, δA, ?_, hAx⟩
  set γ : ℝ := (3 * n : ℕ) * m.u / (1 - (3 * n : ℕ) * m.u) with hγ
  have hγ0 : 0 ≤ γ := by
    rw [hγ]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) m.u_nonneg) (by linarith)
  have h1 : ‖δA‖ ≤ ‖γ • (L.abs * U.abs)‖ := by
    refine linfty_opNorm_le_of_abs_entrywiseLE fun i j => ?_
    have := hδA i j
    have hM : 0 ≤ (L.abs * U.abs) i j := by
      rw [mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    simp only [Matrix.abs_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
    rw [abs_mul, abs_of_nonneg hγ0, abs_of_nonneg hM]
    exact this
  calc ‖δA‖ ≤ ‖γ • (L.abs * U.abs)‖ := h1
    _ = γ * ‖L.abs * U.abs‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
    _ ≤ γ * (‖L.abs‖ * ‖U.abs‖) := mul_le_mul_of_nonneg_left (linfty_opNorm_mul _ _) hγ0
    _ = γ * (‖L‖ * ‖U‖) := by rw [linfty_opNorm_abs, linfty_opNorm_abs]
    _ ≤ γ * (n * ‖U‖) := by gcongr
    _ = n * γ * ‖U‖ := by ring

/-- **(3.66), the growth factor** `ρ_n = max_{i,j,k} |a^{(k)}_ij| / max_{i,j} |a_ij|` of Gaussian
elimination on `A`, over the stages `A^{(k)}`, `k = 1, …, n` — the backbone's
`Matrix.growthFactor A`, on the exact stages `Matrix.gemStage A k` (the book writes the computed
entries `â^{(k)}_ij`; bounds are available for the exact ones). For GEM with partial pivoting
the growth factor is that of `P A`, `P` the permutation matrix of §3.5. -/
noncomputable def equation_3_66 (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := growthFactor A

/-- **(3.66), spelled out**: `ρ_n` is the quotient of the largest entry of any stage by the
largest entry of `A`, and every entry of every stage — of `Û = A^{(n)}` in particular —
satisfies `|u_ij| ≤ ρ_n max_{i,j} |a_ij|` (backbone
`Matrix.abs_gemStage_le_growthFactor_mul_supAbs`). -/
theorem equation_3_66_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    equation_3_66 A =
      (⨆ p : Fin n × Fin n × Fin n, |gemStage A p.1 p.2.1 p.2.2|) /
        ⨆ p : Fin n × Fin n, |A p.1 p.2| ∧
    ∀ (k : ℕ) (i j : Fin n),
      |gemStage A k i j| ≤ equation_3_66 A * ⨆ p : Fin n × Fin n, |A p.1 p.2| :=
  ⟨rfl, fun k i j => abs_gemStage_le_growthFactor_mul_supAbs A k i j⟩

/-- **(3.67), Wilkinson's bound, conditional form.** If the computed factors satisfy
`|l̂_ij| ≤ 1` (partial pivoting) and `|û_ij| ≤ ρ max_{i,j} |a_ij|` (the growth-factor bound of
(3.66), which the book borrows from the exact factors), then the computed solution `x̂` of GEM
(`3 n u < 1`) solves `(A + δA) x̂ = b` with `‖δA‖_∞ ≤ n² γ_{3n} ρ ‖A‖_∞` — the book's
`8 u n³ ρ_n ‖A‖_∞ + O(u²)` up to the constant, `n² γ_{3n} = 3 n³ u + O(u²)` (backbone
`FloatingPoint.linfty_opNorm_le_of_roundsLU_solve`, [higham2002accuracy] Theorem 9.5). -/
theorem equation_3_67 [NeZero n] (hn : ((3 * n : ℕ) : ℝ) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) (hy : RoundsForwardSubst m L b y) (hx : RoundsBackSubst m U y x)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hL : ∀ i j, |L i j| ≤ 1)
    (hU : ∀ i j, |U i j| ≤ ρ * ⨆ p : Fin n × Fin n, |A p.1 p.2|) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      ‖δA‖ ≤ (n : ℝ) ^ 2 * ((3 * n : ℕ) * m.u / (1 - (3 * n : ℕ) * m.u)) * ρ * ‖A‖ ∧
        (A + δA) *ᵥ x = b := by
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by norm_num) (NeZero.ne n))
    nlinarith [m.u_nonneg]
  obtain ⟨δA, hδA, hAx⟩ := linfty_opNorm_le_of_roundsLU_solve hu (by rwa [Fintype.card_fin]) h hd
    hy hx hρ hL hU
  refine ⟨δA, ?_, hAx⟩
  rwa [Fintype.card_fin, gamma_def] at hδA

end Backward

/-! ### The bounds on the growth factor -/

section Growth

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **§3.10, `ρ_n ≤ 2^{n-1}`.** The growth factor of Gaussian elimination is at most `2^{n-1}`
whenever the multipliers have modulus at most `1`, hence with partial pivoting: for
`P A = L U` of §3.5, `ρ_n(P A) ≤ 2^{n-1}` (backbone `Matrix.growthFactor_le_two_pow`,
`Matrix.growthFactor_le_two_pow_of_partialPivotRow`). Exercise 5's matrix attains the bound. -/
theorem growthFactor_le_two_pow :
    ((∀ (k : ℕ) (hk : k < n) (i : Fin n), ⟨k, hk⟩ < i →
      |gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩| ≤ 1) →
      equation_3_66 A ≤ 2 ^ (n - 1)) ∧
    equation_3_66 ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) ≤ 2 ^ (n - 1) :=
  ⟨fun hmul => Matrix.growthFactor_le_two_pow A hmul, growthFactor_le_two_pow_of_partialPivotRow A⟩

/-- **§3.10 (1), the tridiagonal case.** For a tridiagonal `A`, GEM with partial pivoting has
`ρ_n ≤ 2` (backbone `Matrix.growthFactor_le_two_of_isTridiagonal`); this is the case `p = 1` of
Bohte's banded bound, which itself is not formalized. -/
theorem growthFactor_tridiagonal (hA : A.IsTridiagonal) :
    equation_3_66 ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) ≤ 2 :=
  growthFactor_le_two_of_isTridiagonal hA

/-- **§3.10 (2), Hessenberg matrices.** For an upper Hessenberg `A`, GEM with partial pivoting
has `ρ_n ≤ n` (backbone `Matrix.growthFactor_le_card_of_isUpperHessenberg`). -/
theorem growthFactor_hessenberg (hA : A.IsUpperHessenberg) :
    equation_3_66 ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) ≤ n :=
  growthFactor_le_card_of_isUpperHessenberg hA

/-- **§3.10 (3), symmetric positive definite matrices.** `ρ_n = 1`: Gaussian elimination
without pivoting never increases the largest entry (backbone
`Matrix.growthFactor_eq_one_of_posDef`). -/
theorem growthFactor_posDef [NeZero n] (hA : A.PosDef) : equation_3_66 A = 1 :=
  growthFactor_eq_one_of_posDef hA (Nat.pos_of_ne_zero (NeZero.ne n))

/-- **§3.10 (4), matrices strictly diagonally dominant by columns.** `ρ_n ≤ 2` without
pivoting; the bound holds for every nonsingular matrix weakly dominant by columns (backbone
`Matrix.growthFactor_le_two_of_isColDiagDominant`), and strict dominance gives both. -/
theorem growthFactor_colDiagDominant (hA : A.IsStrictColDiagDominant) : equation_3_66 A ≤ 2 :=
  growthFactor_le_two_of_isColDiagDominant hA.isUnit hA.isColDiagDominant

end Growth

/-! ### Examples 3.7–3.8 and the role of the condition number -/

section Examples

open scoped Matrix.Norms.Operator

/-- The `∞`-norm of a `2 × 2` real matrix is the larger of its two absolute row sums. -/
private theorem linfty_opNorm_fin_two_eq {B : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ}
    (h0 : |B 0 0| + |B 0 1| ≤ c) (h1 : |B 1 0| + |B 1 1| ≤ c)
    (hc : |B 0 0| + |B 0 1| = c ∨ |B 1 0| + |B 1 1| = c) : ‖B‖ = c := by
  have hc0 : 0 ≤ c := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans h0
  refine le_antisymm (linfty_opNorm_le_of_forall_sum_le hc0 fun i => ?_) ?_
  · fin_cases i
    · simpa [Fin.sum_univ_two] using h0
    · simpa [Fin.sum_univ_two] using h1
  · rcases hc with hc | hc
    · rw [← hc]
      simpa [Fin.sum_univ_two] using sum_abs_apply_le_linfty_opNorm B 0
    · rw [← hc]
      simpa [Fin.sum_univ_two] using sum_abs_apply_le_linfty_opNorm B 1

/-- **Example 3.7, (3.68), the conditioning.** For `ε > 0`, the system with `A = [ε, 1; 1, 0]`
and `b = (1 + ε, 1)` has the exact solution `x = (1, 1)`, and `A` is well conditioned:
`A⁻¹ = [0, 1; 1, -ε]`, `‖A‖_∞ = ‖A⁻¹‖_∞ = 1 + ε` and `K_∞(A) = (1 + ε)²`. -/
theorem example_3_7_cond {ε : ℝ} (hε : 0 < ε) :
    !![ε, 1; 1, 0] *ᵥ ![1, 1] = ![1 + ε, 1] ∧ (!![ε, 1; 1, 0])⁻¹ = !![0, 1; 1, -ε] ∧
      lpOpNorm ⊤ !![ε, 1; 1, 0] = 1 + ε ∧ lpOpNorm ⊤ (!![ε, 1; 1, 0])⁻¹ = 1 + ε ∧
      condNumber ⊤ !![ε, 1; 1, 0] = (1 + ε) ^ 2 := by
  have hinv : (!![ε, 1; 1, 0])⁻¹ = !![0, 1; 1, -ε] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hA : lpOpNorm ⊤ !![ε, 1; 1, 0] = 1 + ε := by
    rw [lpOpNorm_top]
    refine linfty_opNorm_fin_two_eq ?_ ?_ (Or.inl ?_)
    · simp [abs_of_pos hε, add_comm]
    · simp
      linarith
    · simp [abs_of_pos hε, add_comm]
  have hAinv : lpOpNorm ⊤ (!![ε, 1; 1, 0])⁻¹ = 1 + ε := by
    rw [hinv, lpOpNorm_top]
    refine linfty_opNorm_fin_two_eq ?_ ?_ (Or.inr ?_)
    · simp
      linarith
    · simp [abs_of_pos hε]
    · simp [abs_of_pos hε]
  refine ⟨?_, hinv, hA, hAinv, ?_⟩
  · ext i
    fin_cases i
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
  · rw [condNumber, hA, hAinv, sq]

/-- **Example 3.7 with Exercise 6, the factorizations.** For `ε ≠ 0` the LU factorization of
`A = [ε, 1; 1, 0]` without pivoting is `L = [1, 0; 1/ε, 1]`, `U = [ε, 1; 0, -1/ε]` — unique by
Theorem 3.4, with entries of modulus `1/ε`, large for small `ε` — while with partial pivoting
(`|ε| ≤ 1`, so the second row is the pivot row) `P A = [1, 0; ε, 1] = L U` with
`L = [1, 0; ε, 1]`, `U = I`, whose entries are bounded by `1`. -/
theorem example_3_7_lu {ε : ℝ} (hε : ε ≠ 0) :
    IsLU !![ε, 1; 1, 0] !![1, 0; ε⁻¹, 1] !![ε, 1; 0, -ε⁻¹] ∧
      (∀ L U, IsLU !![ε, 1; 1, 0] L U → L = !![1, 0; ε⁻¹, 1] ∧ U = !![ε, 1; 0, -ε⁻¹]) ∧
      IsLU (!![(0 : ℝ), 1; 1, 0] * !![ε, 1; 1, 0]) !![1, 0; ε, 1] 1 ∧
      (|ε| ≤ 1 → ∀ i j, |(!![1, 0; ε, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1) := by
  have hprod : !![ε, 1; 1, 0] = !![1, 0; ε⁻¹, 1] * !![ε, 1; 0, -ε⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hε]
  have hLU : IsLU !![ε, 1; 1, 0] !![1, 0; ε⁻¹, 1] !![ε, 1; 0, -ε⁻¹] := by
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, hprod.symm⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> simp
    · fin_cases i <;> fin_cases j <;> simp_all
  have hstrict :
      ∀ k, IsUnit ((!![ε, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).strictLeadingPrincipalSubmatrix k) :=
    (gemStage_pivots_ne_zero_iff _).1 fun k hk hk1 => by
      interval_cases k
      · simpa using hε
      · exact absurd hk1 (by norm_num)
  have hPA : !![(0 : ℝ), 1; 1, 0] * !![ε, 1; 1, 0] = !![1, 0; ε, 1] * 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hLU, fun L U h => h.unique hLU hstrict, ?_, fun hε1 i j => ?_⟩
  · rw [hPA]
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, rfl⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> simp
    · exact one_apply_ne hij.ne'
  · fin_cases i <;> fin_cases j <;> simp [hε1]

/-- **§3.10, the residual and the error.** If `δb` in (3.11) is regarded as the residual
`r̂ = b - A x̂` of a computed solution `x̂`, then for `A` nonsingular, `A x = b`, `b ≠ 0`:
`‖x - x̂‖ / ‖x‖ ≤ K(A) ‖r̂‖ / (‖A‖ ‖x‖) ≤ K(A) ‖r̂‖ / ‖b‖` in any induced `p`-norm — a small
residual does not guarantee a small error when `K(A) ≫ 1` (Example 3.8). -/
theorem residual_error_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ}
    {b x : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0) (xhat : Fin n → ℝ) :
    ‖WithLp.toLp p (x - xhat)‖ / ‖WithLp.toLp p x‖ ≤
        condNumber p A * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ / (lpOpNorm p A * ‖WithLp.toLp p x‖) ∧
      condNumber p A * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ / (lpOpNorm p A * ‖WithLp.toLp p x‖) ≤
        condNumber p A * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ / ‖WithLp.toLp p b‖ := by
  have hne : NeZero n := ⟨fun h => hb (by subst h; exact Subsingleton.elim _ _)⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have hxn : 0 < ‖WithLp.toLp p x‖ := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  have hbn : 0 < ‖WithLp.toLp p b‖ := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  have hK0 : 0 ≤ condNumber p A := mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  have hApos : 0 < lpOpNorm p A := by
    have h1 := one_le_condNumberLp p hA
    rw [condNumberLp] at h1
    refine (lpOpNorm_nonneg p A).lt_of_ne fun h => ?_
    rw [← h, zero_mul] at h1
    norm_num at h1
  have hr0 : 0 ≤ ‖WithLp.toLp p (b - A *ᵥ xhat)‖ := norm_nonneg _
  -- `x - x̂ = A⁻¹ (b - A x̂)`
  have herr : x - xhat = A⁻¹ *ᵥ (b - A *ᵥ xhat) := by
    rw [mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hA),
      one_mulVec, ← hx, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hA),
      one_mulVec]
  have h1 : ‖WithLp.toLp p (x - xhat)‖ ≤ lpOpNorm p A⁻¹ * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ := by
    rw [herr]
    exact (lpCLM p A⁻¹).le_opNorm (WithLp.toLp p (b - A *ᵥ xhat))
  -- `‖b‖ ≤ ‖A‖ ‖x‖`
  have h2 : ‖WithLp.toLp p b‖ ≤ lpOpNorm p A * ‖WithLp.toLp p x‖ := by
    rw [← hx]
    exact (lpCLM p A).le_opNorm (WithLp.toLp p x)
  constructor
  · rw [div_le_div_iff₀ hxn (mul_pos hApos hxn)]
    calc ‖WithLp.toLp p (x - xhat)‖ * (lpOpNorm p A * ‖WithLp.toLp p x‖)
        ≤ lpOpNorm p A⁻¹ * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ * (lpOpNorm p A * ‖WithLp.toLp p x‖) :=
          mul_le_mul_of_nonneg_right h1 (mul_pos hApos hxn).le
      _ = condNumber p A * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ * ‖WithLp.toLp p x‖ := by
          rw [condNumber]; ring
  · exact div_le_div_of_nonneg_left (mul_nonneg hK0 hr0) hbn h2

/-- **Example 3.8.** The matrix `A = [1, 1.0001; 1.0001, 1]` is ill conditioned,
`K_∞(A) = 20001` (`‖A‖_∞ = 2.0001`, `‖A⁻¹‖_∞ = 10000`), and for `b = (1, 1)` the vector
`x̂ = (-4.499775, 5.5002249)` has the small residual `‖b - A x̂‖_∞ ≤ 10⁻³` although it is far
from the exact solution `x = A⁻¹ b = (0.499975…, 0.499975…)`: `‖x̂ - x‖_∞ ≥ 4`. -/
theorem example_3_8 :
    condNumber ⊤ !![(1 : ℝ), 1.0001; 1.0001, 1] = 20001 ∧
      ‖![(1 : ℝ), 1] - !![(1 : ℝ), 1.0001; 1.0001, 1] *ᵥ ![-4.499775, 5.5002249]‖ ≤ 1 / 1000 ∧
      4 ≤ ‖![(-4.499775 : ℝ), 5.5002249] - (!![(1 : ℝ), 1.0001; 1.0001, 1])⁻¹ *ᵥ ![1, 1]‖ := by
  have hinv : (!![(1 : ℝ), 1.0001; 1.0001, 1])⁻¹ =
      !![-(1 / 0.00020001), 1.0001 / 0.00020001; 1.0001 / 0.00020001, -(1 / 0.00020001)] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · rw [condNumber, hinv, lpOpNorm_top, lpOpNorm_top,
      linfty_opNorm_fin_two_eq (c := 2.0001) (by norm_num) (by norm_num) (Or.inl (by norm_num)),
      linfty_opNorm_fin_two_eq (c := 10000) (by norm_num) (by norm_num) (Or.inl (by norm_num))]
    norm_num
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two, Real.norm_eq_abs, abs_le]
  · rw [hinv]
    refine le_trans ?_ (norm_le_pi_norm _ 0)
    norm_num [mulVec, dotProduct, Fin.sum_univ_two, Real.norm_eq_abs, le_abs]

/-- **(3.69), the display before it.** Applying (3.13) with `γ = u` and assuming
`u K_∞(A) ≤ 1/2`, the computed solution of `A x = b` (in the setting of Theorem 3.3 in the
`∞`-norm) satisfies `‖δx‖_∞ / ‖x‖_∞ ≤ 2 u K_∞(A) / (1 - u K_∞(A)) ≤ 4 u K_∞(A)`. The
"`≃ u K_∞(A)`" of (3.69) and the count of `t - m` exact digits are heuristics. -/
theorem equation_3_69 {A δA : Matrix (Fin n) (Fin n) ℝ} {b δb x δx : Fin n → ℝ} (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hb : b ≠ 0) (hδx : (A + δA) *ᵥ (x + δx) = b + δb) {u : ℝ} (hu : 0 ≤ u)
    (hδA : lpOpNorm ⊤ δA ≤ u * lpOpNorm ⊤ A) (hδb : ‖δb‖ ≤ u * ‖b‖)
    (hK : u * condNumber ⊤ A ≤ 1 / 2) :
    ‖δx‖ / ‖x‖ ≤ 2 * u * condNumber ⊤ A / (1 - u * condNumber ⊤ A) ∧
      2 * u * condNumber ⊤ A / (1 - u * condNumber ⊤ A) ≤ 4 * u * condNumber ⊤ A := by
  have hK0 : 0 ≤ u * condNumber ⊤ A :=
    mul_nonneg hu (mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _))
  have h := theorem_3_3 (p := ⊤) hA hx hb hδx hδA (by rwa [PiLp.norm_toLp, PiLp.norm_toLp])
    (by linarith)
  rw [PiLp.norm_toLp, PiLp.norm_toLp] at h
  refine ⟨h.trans (le_of_eq (by ring)), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Examples

end QuarteroniSaccoSaleri.Chapter03
