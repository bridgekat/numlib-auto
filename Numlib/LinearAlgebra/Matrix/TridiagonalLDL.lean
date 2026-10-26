import Mathlib.Algebra.Order.Star.Real
import Numlib.LinearAlgebra.Matrix.LU

/-!
# The `LDLᵀ` factorization of a shifted symmetric tridiagonal matrix

For a symmetric tridiagonal matrix `T` with diagonal `ρ` and off-diagonal `γ` (`γ i` couples rows
`i - 1` and `i`), the shifted matrix `T + μ I` factors as `L D Lᵀ` with `L` unit lower bidiagonal
and `D = diag(d)`, where the pivots satisfy the scalar recurrence
`d₀ = ρ₀ + μ`, `d_{i+1} = ρ_{i+1} + μ - γ_{i+1}² / d_i`, and `L (i+1) i = γ_{i+1} / d_i`
(Cartis–Gould–Toint (10.2.5)–(10.2.6), Algorithms 10.2.1–10.2.2; [golub2013matrix] §4.3.6).
This is the symmetric case of the Thomas algorithm (`Matrix.isLU_tridiagonal_thomas`): the upper
Thomas factor is `D Lᵀ`. Positive definiteness of `T + μ I` is detected by the pivots, and the
factors give the forward–diagonal–backward substitution solver.

## Main definitions

* `Matrix.symTridiag ρ γ k`: the `k × k` symmetric tridiagonal matrix.
* `Matrix.ldlPivot ρ γ μ i`: the pivots `dᵢ(μ)` of (10.2.6).
* `Matrix.tridiagSolve ρ γ μ k b`: the solution of `(T + μ I) x = b` by Algorithm 10.2.2.

## Main statements

* `Matrix.symTridiag_add_smul_one_eq_ldl`: `T + μ I = L D Lᵀ` when the pivots `d_i`, `i < k - 1`,
  are nonzero ((10.2.6)).
* `Matrix.posDef_symTridiag_add_iff`: `T + μ I` is positive definite iff all its pivots are
  positive; `Matrix.posDef_symTridiag_succ_add_iff` is the update test of §10.2.1.
* `Matrix.mulVec_tridiagSolve`: Algorithm 10.2.2 solves the system.
-/

open Finset

namespace Matrix

/-! ### The matrix -/

section Def

variable {R : Type*}

/-- The `k × k` symmetric tridiagonal matrix with diagonal `ρ i` and off-diagonal entries `γ i`
at `(i, i - 1)` and `(i - 1, i)` (`γ 0` is unused): `Matrix.tridiagonalOfNat ρ γ (γ ∘ succ) k`. -/
def symTridiag [Zero R] (ρ γ : ℕ → R) (k : ℕ) : Matrix (Fin k) (Fin k) R :=
  tridiagonalOfNat ρ γ (fun i => γ (i + 1)) k

/-- The entries of `Matrix.symTridiag`. -/
theorem symTridiag_apply [Zero R] (ρ γ : ℕ → R) {k : ℕ} (i j : Fin k) :
    symTridiag ρ γ k i j =
      if (i : ℕ) = j then ρ i else if (j : ℕ) + 1 = i then γ i
      else if (i : ℕ) + 1 = j then γ j else 0 := by
  simp only [symTridiag, tridiagonalOfNat, of_apply]
  split_ifs <;> first | rfl | congr 1

/-- `Matrix.symTridiag` is symmetric. -/
theorem symTridiag_transpose [Zero R] (ρ γ : ℕ → R) (k : ℕ) :
    (symTridiag ρ γ k)ᵀ = symTridiag ρ γ k := by
  ext i j
  simp only [transpose_apply, symTridiag_apply]
  split_ifs <;> first | rfl | omega | congr 1

/-- `Matrix.symTridiag` is tridiagonal. -/
theorem isTridiagonal_symTridiag [Zero R] (ρ γ : ℕ → R) (k : ℕ) :
    (symTridiag ρ γ k).IsTridiagonal := by
  rintro i j (⟨l, hjl, hli⟩ | ⟨l, hil, hlj⟩) <;>
  · simp only [Fin.lt_def] at *
    rw [symTridiag_apply]
    split_ifs <;> first | rfl | omega

/-- The leading `n × n` block of `Matrix.symTridiag ρ γ k` is `Matrix.symTridiag ρ γ n`. -/
theorem symTridiag_submatrix_castLE [Zero R] (ρ γ : ℕ → R) {n k : ℕ} (h : n ≤ k) :
    (symTridiag ρ γ k).submatrix (Fin.castLE h) (Fin.castLE h) = symTridiag ρ γ n := by
  ext i j
  simp [symTridiag_apply]

/-- A shift by a multiple of the identity shifts the diagonal. -/
theorem symTridiag_add_smul_one [Ring R] (ρ γ : ℕ → R) (μ : R) (k : ℕ) :
    symTridiag ρ γ k + μ • (1 : Matrix (Fin k) (Fin k) R) = symTridiag (fun i => ρ i + μ) γ k := by
  ext i j
  simp only [add_apply, smul_apply, one_apply, symTridiag_apply, Fin.ext_iff, smul_eq_mul]
  split_ifs <;> simp

end Def

/-! ### The pivots -/

section Pivot

variable {K : Type*} [Field K] (ρ γ : ℕ → K) (μ : K)

/-- The pivots `dᵢ(μ)` of the `LDLᵀ` factorization of `T + μ I` (Cartis–Gould–Toint (10.2.6)):
`d₀ = ρ₀ + μ`, `d_{i+1} = ρ_{i+1} + μ - γ_{i+1}² / d_i`. -/
noncomputable def ldlPivot : ℕ → K
  | 0 => ρ 0 + μ
  | i + 1 => ρ (i + 1) + μ - γ (i + 1) ^ 2 / ldlPivot i

@[simp]
theorem ldlPivot_zero : ldlPivot ρ γ μ 0 = ρ 0 + μ := rfl

theorem ldlPivot_succ (i : ℕ) :
    ldlPivot ρ γ μ (i + 1) = ρ (i + 1) + μ - γ (i + 1) ^ 2 / ldlPivot ρ γ μ i := rfl

/-- The pivots are the Thomas pivots of the shifted matrix. -/
theorem ldlPivot_eq_thomasAlpha :
    ldlPivot ρ γ μ = thomasAlpha (fun i => ρ i + μ) γ (fun i => γ (i + 1)) := by
  funext i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [ldlPivot_succ, thomasAlpha_succ, thomasBeta_succ, ← ih]
    ring

/-- The multipliers `l_{i+1} = γ_{i+1} / d_i` of the `L` factor, with `l₀ = 0`; they are the
Thomas multipliers of the shifted matrix. -/
noncomputable def ldlMult (i : ℕ) : K := thomasBeta (fun i => ρ i + μ) γ (fun i => γ (i + 1)) i

theorem ldlMult_succ (i : ℕ) : ldlMult ρ γ μ (i + 1) = γ (i + 1) / ldlPivot ρ γ μ i := by
  rw [ldlMult, thomasBeta_succ, ldlPivot_eq_thomasAlpha]

/-- The unit lower bidiagonal factor `L`, with `γ_{i+1} / d_i` at `(i + 1, i)`. -/
noncomputable def ldlLower (k : ℕ) : Matrix (Fin k) (Fin k) K :=
  thomasLower (fun i => ρ i + μ) γ (fun i => γ (i + 1)) k

/-- `L` is unit lower bidiagonal with the multipliers on the subdiagonal. -/
theorem ldlLower_eq (k : ℕ) : ldlLower ρ γ μ k = lowerBidiagonalOf (ldlMult ρ γ μ) k := rfl

/-- **The `LDLᵀ` factorization** (Cartis–Gould–Toint (10.2.6)): if the pivots `d_i`, `i + 1 < k`,
are nonzero, then `T + μ I = L D Lᵀ`, with `L = ldlLower ρ γ μ k` unit lower bidiagonal with
`L (i+1) i = γ_{i+1} / d_i` and `D = diag(d)`. -/
theorem symTridiag_add_smul_one_eq_ldl {k : ℕ} (hd : ∀ i, i + 1 < k → ldlPivot ρ γ μ i ≠ 0) :
    symTridiag ρ γ k + μ • (1 : Matrix (Fin k) (Fin k) K) =
      ldlLower ρ γ μ k * diagonal (fun i : Fin k => ldlPivot ρ γ μ i) * (ldlLower ρ γ μ k)ᵀ := by
  have hα : ∀ i, i + 1 < k → thomasAlpha (fun i => ρ i + μ) γ (fun i => γ (i + 1)) i ≠ 0 := by
    intro i hi
    rw [← ldlPivot_eq_thomasAlpha]
    exact hd i hi
  have hLU := isLU_tridiagonal_thomas (fun i => ρ i + μ) γ (fun i => γ (i + 1)) hα
  rw [symTridiag_add_smul_one, symTridiag, ← hLU.mul_eq, mul_assoc, ldlLower]
  congr 1
  ext i j
  simp only [thomasUpper, thomasLower, diagonal_mul, transpose_apply, of_apply, Fin.ext_iff,
    ← ldlPivot_eq_thomasAlpha]
  by_cases hij : (i : ℕ) = j
  · simp [hij]
  · simp only [hij, ite_false, Ne.symm hij]
    by_cases hij' : (i : ℕ) + 1 = j
    · have hj : (j : ℕ) = i + 1 := hij'.symm
      rw [ite_eq_left hij', ite_eq_left hij', hj, thomasBeta_succ, ← ldlPivot_eq_thomasAlpha,
        mul_div_cancel₀ _ (hd i (by omega))]
    · simp [hij']

/-- The determinant of `T + μ I` is the product of the pivots, when the pivots `d_i`,
`i + 1 < k`, are nonzero. -/
theorem det_symTridiag_add_smul_one {k : ℕ} (hd : ∀ i, i + 1 < k → ldlPivot ρ γ μ i ≠ 0) :
    (symTridiag ρ γ k + μ • (1 : Matrix (Fin k) (Fin k) K)).det =
      ∏ i : Fin k, ldlPivot ρ γ μ i := by
  have hα : ∀ i, i + 1 < k → thomasAlpha (fun i => ρ i + μ) γ (fun i => γ (i + 1)) i ≠ 0 := by
    intro i hi
    rw [← ldlPivot_eq_thomasAlpha]
    exact hd i hi
  rw [symTridiag_add_smul_one, symTridiag,
    (isLU_tridiagonal_thomas (fun i => ρ i + μ) γ (fun i => γ (i + 1)) hα).det_eq_prod_diag]
  simp [thomasUpper, ldlPivot_eq_thomasAlpha]

end Pivot

/-! ### Positive definiteness -/

section PosDef

variable (ρ γ : ℕ → ℝ) (μ : ℝ)

/-- The factor `L` is invertible: its transpose acts injectively. -/
theorem injective_mulVec_ldlLower_transpose (k : ℕ) :
    Function.Injective (ldlLower ρ γ μ k)ᵀ.mulVec := by
  have hL : (ldlLower ρ γ μ k).IsUnitLowerTriangular :=
    ⟨(isLowerBidiagonal_thomasLower _ _ _ k).isLowerTriangular, fun i => by
      simp [ldlLower, thomasLower]⟩
  refine mulVec_injective_of_isUnit ?_
  rw [isUnit_iff_isUnit_det, det_transpose, hL.det_eq_one]
  exact isUnit_one

/-- **Positive definiteness via the pivots** (Cartis–Gould–Toint §10.2.1): `T + μ I` is positive
definite iff all its pivots `d_i(μ)`, `i < k`, are positive. -/
theorem posDef_symTridiag_add_iff {k : ℕ} :
    (symTridiag ρ γ k + μ • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef ↔
      ∀ i < k, 0 < ldlPivot ρ γ μ i := by
  constructor
  · intro hP i hi
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have hpos : ∀ j < i, 0 < ldlPivot ρ γ μ j := fun j hj => ih j hj (hj.trans hi)
      -- the leading `(i+1) × (i+1)` block is positive definite, with determinant `∏_{j ≤ i} d_j`
      have hsub : (symTridiag ρ γ (i + 1) + μ • (1 : Matrix (Fin (i + 1)) (Fin (i + 1)) ℝ)).PosDef
          := by
        have := hP.submatrix (Fin.castLE_injective (show i + 1 ≤ k by omega))
        have heq : (symTridiag ρ γ k + μ • (1 : Matrix (Fin k) (Fin k) ℝ)).submatrix
            (Fin.castLE (show i + 1 ≤ k by omega)) (Fin.castLE (show i + 1 ≤ k by omega)) =
            symTridiag ρ γ (i + 1) + μ • (1 : Matrix (Fin (i + 1)) (Fin (i + 1)) ℝ) := by
          ext a b
          simp [symTridiag_apply, one_apply, Fin.ext_iff]
        rwa [heq] at this
      have hdet := hsub.det_pos
      rw [det_symTridiag_add_smul_one ρ γ μ fun j hj => (hpos j (by omega)).ne',
        Fin.prod_univ_castSucc] at hdet
      have hprod : 0 < ∏ j : Fin i, ldlPivot ρ γ μ (Fin.castSucc j : ℕ) :=
        prod_pos fun j _ => hpos j j.2
      simpa using pos_of_mul_pos_right hdet hprod.le
  · intro hd
    rw [symTridiag_add_smul_one_eq_ldl ρ γ μ fun i (hi : i + 1 < k) => (hd i (by omega)).ne']
    have hD : (diagonal fun i : Fin k => ldlPivot ρ γ μ i).PosDef :=
      posDef_diagonal_iff.2 fun i => hd i i.2
    have := hD.conjTranspose_mul_mul_same (injective_mulVec_ldlLower_transpose ρ γ μ k)
    simpa [conjTranspose_eq_transpose_of_trivial] using this

/-- **The update test** (Cartis–Gould–Toint §10.2.1): if `T_{k+1} + μ I` is positive definite, then
`T_{k+2} + μ I` is positive definite iff `ρ_{k+1} + μ > γ_{k+1}² / d_k(μ)`. -/
theorem posDef_symTridiag_succ_add_iff {k : ℕ}
    (h : (symTridiag ρ γ (k + 1) + μ • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)).PosDef) :
    (symTridiag ρ γ (k + 2) + μ • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)).PosDef ↔
      γ (k + 1) ^ 2 / ldlPivot ρ γ μ k < ρ (k + 1) + μ := by
  rw [posDef_symTridiag_add_iff] at h ⊢
  rw [← sub_pos, ← ldlPivot_succ]
  constructor
  · intro h'
    exact h' (k + 1) (by omega)
  · intro h' i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact h i hi
    · exact h'

end PosDef

/-! ### The solver -/

section Solve

variable {K : Type*} [Field K] (ρ γ : ℕ → K) (μ : K)

/-- The forward substitution `L y = b` of Algorithm 10.2.2: `y₀ = b₀`,
`y_{i+1} = b_{i+1} - l_{i+1} y_i`. -/
noncomputable def ldlForward (b : ℕ → K) : ℕ → K
  | 0 => b 0
  | i + 1 => b (i + 1) - ldlMult ρ γ μ (i + 1) * ldlForward b i

/-- The backward substitution `Lᵀ z = w` of Algorithm 10.2.2 on `Fin k`: `z_{k-1} = w_{k-1}`,
`z_i = w_i - l_{i+1} z_{i+1}`. -/
noncomputable def ldlBackward (k : ℕ) (w : ℕ → K) (i : ℕ) : K :=
  if i + 1 < k then w i - ldlMult ρ γ μ (i + 1) * ldlBackward k w (i + 1) else w i
termination_by k - i

theorem ldlBackward_eq (k : ℕ) (w : ℕ → K) (i : ℕ) :
    ldlBackward ρ γ μ k w i =
      if i + 1 < k then w i - ldlMult ρ γ μ (i + 1) * ldlBackward ρ γ μ k w (i + 1) else w i := by
  rw [ldlBackward]

/-- **Algorithm 10.2.2** (Cartis–Gould–Toint): the solution of `(T + μ I) x = b` from the
`LDLᵀ` factors: forward substitution with `L`, scaling by the reciprocal pivots `rᵢ = 1/dᵢ`,
backward substitution with `Lᵀ`. -/
noncomputable def tridiagSolve (k : ℕ) (b : Fin k → K) : Fin k → K :=
  fun i => ldlBackward ρ γ μ k
    (fun j => ldlForward ρ γ μ (fun j => if h : j < k then b ⟨j, h⟩ else 0) j / ldlPivot ρ γ μ j) i

/-- `L` as a tridiagonal matrix. -/
theorem ldlLower_eq_tridiagonalOfNat (k : ℕ) :
    ldlLower ρ γ μ k = tridiagonalOfNat 1 (ldlMult ρ γ μ) 0 k := by
  ext i j
  simp only [ldlLower, thomasLower, tridiagonalOfNat, of_apply, Fin.ext_iff, Pi.one_apply,
    Pi.zero_apply]
  split_ifs <;> rfl

/-- `Lᵀ` as a tridiagonal matrix. -/
theorem ldlLower_transpose_eq_tridiagonalOfNat (k : ℕ) :
    (ldlLower ρ γ μ k)ᵀ = tridiagonalOfNat 1 0 (fun i => ldlMult ρ γ μ (i + 1)) k := by
  ext i j
  simp only [transpose_apply, ldlLower, thomasLower, tridiagonalOfNat, of_apply, Fin.ext_iff,
    Pi.one_apply, Pi.zero_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- **Algorithm 10.2.2 solves the shifted system**: if the pivots `d_i`, `i < k`, are nonzero (in
particular if `T + μ I` is positive definite, `Matrix.posDef_symTridiag_add_iff`), then
`(T + μ I) (tridiagSolve ρ γ μ k b) = b`. -/
theorem mulVec_tridiagSolve {k : ℕ} (hd : ∀ i < k, ldlPivot ρ γ μ i ≠ 0) (b : Fin k → K) :
    (symTridiag ρ γ k + μ • (1 : Matrix (Fin k) (Fin k) K)) *ᵥ tridiagSolve ρ γ μ k b = b := by
  set b' : ℕ → K := fun j => if h : j < k then b ⟨j, h⟩ else 0 with hb'
  set y : ℕ → K := ldlForward ρ γ μ b' with hy
  set w : ℕ → K := fun j => y j / ldlPivot ρ γ μ j with hw
  rw [symTridiag_add_smul_one_eq_ldl ρ γ μ fun i (hi : i + 1 < k) => hd i (by omega),
    ← mulVec_mulVec,
    ← mulVec_mulVec]
  -- backward substitution: `Lᵀ z = w`
  have h1 : (ldlLower ρ γ μ k)ᵀ *ᵥ tridiagSolve ρ γ μ k b = fun i : Fin k => w i := by
    funext i
    rw [ldlLower_transpose_eq_tridiagonalOfNat, tridiagonalOfNat_mulVec]
    simp only [Pi.zero_apply, zero_mul, dite_eq_ite, ite_self, zero_add, Pi.one_apply, one_mul,
      tridiagSolve]
    rw [ldlBackward_eq]
    split_ifs <;> simp [hw, hy, hb']
  -- scaling: `D w = y`
  have h2 : diagonal (fun i : Fin k => ldlPivot ρ γ μ i) *ᵥ (fun i : Fin k => w i) =
      fun i : Fin k => y i := by
    funext i
    rw [mulVec_diagonal, hw]
    exact mul_div_cancel₀ _ (hd i i.2)
  -- forward substitution: `L y = b`
  have h3 : ldlLower ρ γ μ k *ᵥ (fun i : Fin k => y i) = b := by
    funext i
    rw [ldlLower_eq_tridiagonalOfNat, tridiagonalOfNat_mulVec]
    simp only [Pi.zero_apply, zero_mul, dite_eq_ite, ite_self, add_zero, Pi.one_apply, one_mul]
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => simp [hy, ldlForward, hb', hi]
    | succ i =>
      simp only [Nat.succ_pos, dite_true, hy, ldlForward, hb', hi, dite_true]
      simp
  rw [h1, h2, h3]

end Solve

end Matrix
