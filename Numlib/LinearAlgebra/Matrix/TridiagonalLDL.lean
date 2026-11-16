/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Star.Real
import Numlib.LinearAlgebra.Matrix.LU

/-!
# The $LDL^T$ factorization of a shifted symmetric tridiagonal matrix

Let $T$ be the $k \times k$ symmetric tridiagonal matrix with diagonal entries
$\rho_0, \dots, \rho_{k-1}$ and off-diagonal entries $\gamma_1, \dots, \gamma_{k-1}$, where
$\gamma_i$ couples rows $i - 1$ and $i$. For a shift $\mu$, the matrix $T + \mu I$ factors as
$L D L^T$, with $L$ unit lower bidiagonal and $D = \operatorname{diag}(d_0, \dots, d_{k-1})$. The
pivots satisfy the scalar recurrence
$$d_0 = \rho_0 + \mu, \qquad d_{i+1} = \rho_{i+1} + \mu - \frac{\gamma_{i+1}^2}{d_i},$$
and the subdiagonal of $L$ is $L_{i+1,i} = \gamma_{i+1} / d_i$. This is (10.2.5)–(10.2.6) and
Algorithms 10.2.1–10.2.2 of [cartis2022evaluation]; see also [golub2013matrix] §4.3.6.

The factorization is the symmetric case of the Thomas algorithm `Matrix.isLU_tridiagonal_thomas`:
the upper Thomas factor is $D L^T$. The pivots detect positive definiteness of $T + \mu I$, and the
factors give a solver by forward substitution, diagonal scaling and backward substitution.

## Main definitions

* `Matrix.symTridiag`: the $k \times k$ symmetric tridiagonal matrix $T$ with diagonal $\rho$ and
  off-diagonal $\gamma$.
* `Matrix.ldlPivot`: the pivots $d_i(\mu)$ of (10.2.6) of [cartis2022evaluation].
* `Matrix.tridiagSolve`: the solution of $(T + \mu I) x = b$ by Algorithm 10.2.2 of
  [cartis2022evaluation].

## Main results

* `Matrix.symTridiag_add_smul_one_eq_ldl`: $T + \mu I = L D L^T$ when the pivots $d_i$, $i < k - 1$,
  are nonzero.
* `Matrix.posDef_symTridiag_add_iff`: $T + \mu I$ is positive definite if and only if all its pivots
  are positive.
* `Matrix.posDef_symTridiag_succ_add_iff`: the update test, which decides positive definiteness of
  the next leading block from one pivot.
* `Matrix.mulVec_tridiagSolve`: Algorithm 10.2.2 solves $(T + \mu I) x = b$ when all pivots are
  nonzero.

## Implementation notes

* Sequences are indexed by `ℕ`, and the matrices by `Fin k`. The value $\gamma_0$ is not used.
* The pivots use the division of a field, so a zero pivot $d_i = 0$ gives $\gamma_{i+1}^2 / d_i = 0$
  in the next step. The factorization theorems therefore assume that the relevant pivots are
  nonzero.
-/

open Finset

namespace Matrix

/-! ### The matrix -/

section Def

variable {R : Type*}

/-- The $k \times k$ **symmetric tridiagonal matrix** with diagonal entries $\rho_i$ and
off-diagonal entries $\gamma_i$ at the positions $(i, i - 1)$ and $(i - 1, i)$, for
$1 \le i < k$.

The value $\gamma_0$ is not used. The matrix is `Matrix.tridiagonalOfNat ρ γ (fun i => γ (i +
1)) k`. -/
def symTridiag [Zero R] (ρ γ : ℕ → R) (k : ℕ) : Matrix (Fin k) (Fin k) R :=
  tridiagonalOfNat ρ γ (fun i => γ (i + 1)) k

/-- The entries of `Matrix.symTridiag ρ γ k`: the entry $(i, j)$ is $\rho_i$ if $i = j$, $\gamma_i$
if $j + 1 = i$, $\gamma_j$ if $i + 1 = j$, and $0$ otherwise. -/
theorem symTridiag_apply [Zero R] (ρ γ : ℕ → R) {k : ℕ} (i j : Fin k) :
    symTridiag ρ γ k i j =
      if (i : ℕ) = j then ρ i else if (j : ℕ) + 1 = i then γ i
      else if (i : ℕ) + 1 = j then γ j else 0 := by
  simp only [symTridiag, tridiagonalOfNat, of_apply]
  split_ifs <;> first | rfl | congr 1

/-- The matrix `Matrix.symTridiag ρ γ k` is symmetric. -/
theorem symTridiag_transpose [Zero R] (ρ γ : ℕ → R) (k : ℕ) :
    (symTridiag ρ γ k)ᵀ = symTridiag ρ γ k := by
  ext i j
  simp only [transpose_apply, symTridiag_apply]
  split_ifs <;> first | rfl | omega | congr 1

/-- The matrix `Matrix.symTridiag ρ γ k` is tridiagonal. -/
theorem isTridiagonal_symTridiag [Zero R] (ρ γ : ℕ → R) (k : ℕ) :
    (symTridiag ρ γ k).IsTridiagonal := by
  rintro i j (⟨l, hjl, hli⟩ | ⟨l, hil, hlj⟩) <;>
  · simp only [Fin.lt_def] at *
    rw [symTridiag_apply]
    split_ifs <;> first | rfl | omega

/-- For $n \le k$, the leading $n \times n$ block of `Matrix.symTridiag ρ γ k` is
`Matrix.symTridiag ρ γ n`. -/
theorem symTridiag_submatrix_castLE [Zero R] (ρ γ : ℕ → R) {n k : ℕ} (h : n ≤ k) :
    (symTridiag ρ γ k).submatrix (Fin.castLE h) (Fin.castLE h) = symTridiag ρ γ n := by
  ext i j
  simp [symTridiag_apply]

/-- A shift by a multiple of the identity shifts the diagonal: $T + \mu I$ is the symmetric
tridiagonal matrix with diagonal $\rho_i + \mu$ and the same off-diagonal $\gamma$. -/
theorem symTridiag_add_smul_one [Ring R] (ρ γ : ℕ → R) (μ : R) (k : ℕ) :
    symTridiag ρ γ k + μ • (1 : Matrix (Fin k) (Fin k) R) = symTridiag (fun i => ρ i + μ) γ k := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, symTridiag_apply, Fin.ext_iff,
      smul_eq_mul]
  split_ifs <;> simp

end Def

/-! ### The pivots -/

section Pivot

variable {K : Type*} [Field K] (ρ γ : ℕ → K) (μ : K)

/-- The **pivots** $d_i(\mu)$ of the $L D L^T$ factorization of $T + \mu I$, defined by the
recurrence
$$d_0 = \rho_0 + \mu, \qquad d_{i+1} = \rho_{i+1} + \mu - \frac{\gamma_{i+1}^2}{d_i}.$$
This is (10.2.6) of [cartis2022evaluation].

The pivots are defined for all $i \in \mathbb{N}$, with the division of a field: if $d_i = 0$,
then $d_{i+1} = \rho_{i+1} + \mu$. -/
noncomputable def ldlPivot : ℕ → K
  | 0 => ρ 0 + μ
  | i + 1 => ρ (i + 1) + μ - γ (i + 1) ^ 2 / ldlPivot i

/-- The first pivot is $d_0 = \rho_0 + \mu$. -/
@[simp]
theorem ldlPivot_zero : ldlPivot ρ γ μ 0 = ρ 0 + μ := rfl

/-- The pivot recurrence: $d_{i+1} = \rho_{i+1} + \mu - \gamma_{i+1}^2 / d_i$. -/
theorem ldlPivot_succ (i : ℕ) :
    ldlPivot ρ γ μ (i + 1) = ρ (i + 1) + μ - γ (i + 1) ^ 2 / ldlPivot ρ γ μ i := rfl

/-- The pivots $d_i(\mu)$ are the pivots `Matrix.thomasAlpha` of the Thomas algorithm for the
shifted matrix, with diagonal $\rho_i + \mu$, subdiagonal $\gamma_i$ and superdiagonal
$\gamma_{i+1}$. -/
theorem ldlPivot_eq_thomasAlpha :
    ldlPivot ρ γ μ = thomasAlpha (fun i => ρ i + μ) γ (fun i => γ (i + 1)) := by
  funext i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [ldlPivot_succ, thomasAlpha_succ, thomasBeta_succ, ← ih]
    ring

/-- The **multipliers** of the factor $L$: $l_0 = 0$ and $l_{i+1} = \gamma_{i+1} / d_i$. They are
the multipliers `Matrix.thomasBeta` of the Thomas algorithm for the shifted matrix. -/
noncomputable def ldlMult (i : ℕ) : K := thomasBeta (fun i => ρ i + μ) γ (fun i => γ (i + 1)) i

/-- The multiplier recurrence: $l_{i+1} = \gamma_{i+1} / d_i$. -/
theorem ldlMult_succ (i : ℕ) : ldlMult ρ γ μ (i + 1) = γ (i + 1) / ldlPivot ρ γ μ i := by
  rw [ldlMult, thomasBeta_succ, ldlPivot_eq_thomasAlpha]

/-- The unit lower bidiagonal factor $L$ of order $k$, with the multiplier
$l_{i+1} = \gamma_{i+1} / d_i$ at the position $(i + 1, i)$. It is the lower factor
`Matrix.thomasLower` of the Thomas algorithm for the shifted matrix. -/
noncomputable def ldlLower (k : ℕ) : Matrix (Fin k) (Fin k) K :=
  thomasLower (fun i => ρ i + μ) γ (fun i => γ (i + 1)) k

/-- The factor $L$ is the unit lower bidiagonal matrix `Matrix.lowerBidiagonalOf` with the
multipliers $l_i$ on the subdiagonal. -/
theorem ldlLower_eq (k : ℕ) : ldlLower ρ γ μ k = lowerBidiagonalOf (ldlMult ρ γ μ) k := rfl

/-- The **$L D L^T$ factorization** of a shifted symmetric tridiagonal matrix. Let $T$ be the
$k \times k$ symmetric tridiagonal matrix with diagonal $\rho$ and off-diagonal $\gamma$, and
let $\mu$ be a scalar. If the pivots $d_i(\mu)$ are nonzero for $i + 1 < k$, then
$$T + \mu I = L D L^T,$$
where $L$ is unit lower bidiagonal with $L_{i+1,i} = \gamma_{i+1} / d_i$ and
$D = \operatorname{diag}(d_0, \dots, d_{k-1})$. This is (10.2.6) of [cartis2022evaluation].

The factor $L$ is `Matrix.ldlLower ρ γ μ k`. The last pivot $d_{k-1}$ may be zero. The proof
specializes `Matrix.isLU_tridiagonal_thomas`. -/
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

/-- If the pivots $d_i(\mu)$ are nonzero for $i + 1 < k$, then the determinant of $T + \mu I$ is the
product $d_0 d_1 \cdots d_{k-1}$ of the pivots. -/
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

/-- The real matrix $L^T$ acts injectively on vectors, so the factor $L$ is invertible. -/
theorem injective_mulVec_ldlLower_transpose (k : ℕ) :
    Function.Injective (ldlLower ρ γ μ k)ᵀ.mulVec := by
  have hL : (ldlLower ρ γ μ k).IsUnitLowerTriangular :=
    ⟨(isLowerBidiagonal_thomasLower _ _ _ k).isLowerTriangular, fun i => by
      simp [ldlLower, thomasLower]⟩
  refine mulVec_injective_of_isUnit ?_
  rw [isUnit_iff_isUnit_det, det_transpose, hL.det_eq_one]
  exact isUnit_one

/-- **Positive definiteness via the pivots.** Let $T$ be the $k \times k$ real symmetric tridiagonal
matrix with diagonal $\rho$ and off-diagonal $\gamma$, and let $\mu \in \mathbb{R}$. Then
$T + \mu I$ is positive definite if and only if
$$d_i(\mu) > 0 \quad \text{for all } i < k.$$
This is §10.2.1 of [cartis2022evaluation]. -/
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
          simp [symTridiag_apply, Matrix.one_apply, Fin.ext_iff]
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

/-- **The update test.** Let $T_j$ denote the $j \times j$ real symmetric tridiagonal matrix with
diagonal $\rho$ and off-diagonal $\gamma$, and let $\mu \in \mathbb{R}$. If $T_{k+1} + \mu I$ is
positive definite, then $T_{k+2} + \mu I$ is positive definite if and only if
$$\rho_{k+1} + \mu > \frac{\gamma_{k+1}^2}{d_k(\mu)}.$$
This is the update test of §10.2.1 of [cartis2022evaluation]. -/
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

/-- The **forward substitution** $L y = b$ of Algorithm 10.2.2 of [cartis2022evaluation]:
$y_0 = b_0$ and $y_{i+1} = b_{i+1} - l_{i+1} y_i$, for a right-hand side $b$ indexed by `ℕ`. -/
noncomputable def ldlForward (b : ℕ → K) : ℕ → K
  | 0 => b 0
  | i + 1 => b (i + 1) - ldlMult ρ γ μ (i + 1) * ldlForward b i

/-- The **backward substitution** $L^T z = w$ of Algorithm 10.2.2 of [cartis2022evaluation] in order
$k$: $z_i = w_i - l_{i+1} z_{i+1}$ for $i + 1 < k$, and $z_i = w_i$ otherwise. In particular
$z_{k-1} = w_{k-1}$. -/
noncomputable def ldlBackward (k : ℕ) (w : ℕ → K) (i : ℕ) : K :=
  if i + 1 < k then w i - ldlMult ρ γ μ (i + 1) * ldlBackward k w (i + 1) else w i
termination_by k - i

/-- The defining equation of the backward substitution: $z_i = w_i - l_{i+1} z_{i+1}$ if
$i + 1 < k$, and $z_i = w_i$ otherwise. -/
theorem ldlBackward_eq (k : ℕ) (w : ℕ → K) (i : ℕ) :
    ldlBackward ρ γ μ k w i =
      if i + 1 < k then w i - ldlMult ρ γ μ (i + 1) * ldlBackward ρ γ μ k w (i + 1) else w i := by
  rw [ldlBackward]

/-- **Algorithm 10.2.2** of [cartis2022evaluation]: the solution of $(T + \mu I) x = b$ from the
$L D L^T$ factors. The algorithm solves $L y = b$ by forward substitution, scales by the
reciprocal pivots, $w_i = y_i / d_i$, and solves $L^T x = w$ by backward substitution.

The right-hand side $b \in K^k$ is extended by zero to a sequence indexed by `ℕ`. -/
noncomputable def tridiagSolve (k : ℕ) (b : Fin k → K) : Fin k → K :=
  fun i => ldlBackward ρ γ μ k
    (fun j => ldlForward ρ γ μ (fun j => if h : j < k then b ⟨j, h⟩ else 0) j / ldlPivot ρ γ μ j) i

/-- The factor $L$ is the tridiagonal matrix `Matrix.tridiagonalOfNat` with diagonal $1$,
subdiagonal $l_i$ and superdiagonal $0$. -/
theorem ldlLower_eq_tridiagonalOfNat (k : ℕ) :
    ldlLower ρ γ μ k = tridiagonalOfNat 1 (ldlMult ρ γ μ) 0 k := by
  ext i j
  simp only [ldlLower, thomasLower, tridiagonalOfNat, of_apply, Fin.ext_iff, Pi.one_apply,
    Pi.zero_apply]
  split_ifs <;> rfl

/-- The factor $L^T$ is the tridiagonal matrix `Matrix.tridiagonalOfNat` with diagonal $1$,
subdiagonal $0$ and superdiagonal $l_{i+1}$. -/
theorem ldlLower_transpose_eq_tridiagonalOfNat (k : ℕ) :
    (ldlLower ρ γ μ k)ᵀ = tridiagonalOfNat 1 0 (fun i => ldlMult ρ γ μ (i + 1)) k := by
  ext i j
  simp only [transpose_apply, ldlLower, thomasLower, tridiagonalOfNat, of_apply, Fin.ext_iff,
    Pi.one_apply, Pi.zero_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- **Algorithm 10.2.2** of [cartis2022evaluation] solves the shifted system. Let $T$ be the
$k \times k$ symmetric tridiagonal matrix with diagonal $\rho$ and off-diagonal $\gamma$ over a
field, and let $\mu$ be a scalar. If the pivots $d_i(\mu)$ are nonzero for all $i < k$, then for
every $b \in K^k$ the vector $x$ that the algorithm computes satisfies
$$(T + \mu I)\, x = b.$$

The vector $x$ is `Matrix.tridiagSolve ρ γ μ k b`.

Over $\mathbb{R}$ the hypothesis holds when $T + \mu I$ is positive definite, by
`Matrix.posDef_symTridiag_add_iff`. -/
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
