import Mathlib.Algebra.Order.Star.Real
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Toeplitz

/-!
# The Levinson–Durbin–Trench theory of Toeplitz systems

Symmetric positive definite Toeplitz systems ([golub2013matrix] §4.7; Durbin 1960, Levinson 1947,
Trench 1964, Cybenko 1980). With `T_k = Matrix.symmToeplitz k r` (`r 0 = 1`), the Yule–Walker
system `T_k y = −(r₁, …, r_k)` is solved order by order by **Durbin's recurrence** ((4.7.1)): from
`y^{(k)}`, with `β_k = 1 + rᵀ y^{(k)}` and `α_k = −(r_{k+1} + rᵀ ℰ_k y^{(k)})/β_k`,
`y^{(k+1)} = (y^{(k)} + α_k ℰ_k y^{(k)}, α_k)`.

* `Durbin.sol`, `Durbin.beta`, `Durbin.alpha`: the recurrence, `ℕ`-indexed;
  `Durbin.symmToeplitz_mulVec_sol`: it solves the Yule–Walker systems.
* `Durbin.beta_succ`, `Durbin.det_symmToeplitz_succ`, `Durbin.beta_pos`,
  `Durbin.abs_alpha_lt_one`: `β_{k+1} = (1 − α_k²) β_k`, `det T_{k+1} = β_k det T_k`, and for a
  positive definite `T_n` the `β_k` are positive and the reflection coefficients satisfy
  `|α_k| < 1`; conversely `T_n` is positive definite when every `β_k` is positive
  (`Durbin.posDef_symmToeplitz_iff`).
* `Durbin.transpose_mul_mul_eq_diagonal`, `Durbin.inv_symmToeplitz_eq_mul`: `Uᵀ T U = diag(β)`
  and `T⁻¹ = U diag(β)⁻¹ Uᵀ`, `U` the unit upper triangular matrix of the reversed solutions
  (`Durbin.unitUpper`).
* `Durbin.sum_sol_add_one`, `Durbin.sum_abs_sol_eq`: the sums of the solutions ((4.7.7));
  `Durbin.inv_beta_le_lpOpNorm_one_inv` and `Durbin.lpOpNorm_one_inv_le`: the lower and upper
  bounds of (4.7.6) for `‖T_n⁻¹‖₁`, the upper one (Cybenko's, quoted without proof in the book)
  through the Szegő recursion `p_{k+1}^* = z p_k^* + α_k p_k` of the columns of `U`
  (`Durbin.revSol_succ`), which bounds the row sums of `U` (`Durbin.sum_abs_revSol_le`).
* `Levinson.sol`, `Levinson.symmToeplitz_mulVec_sol`: Levinson's recurrence (4.7.2)–(4.7.3) for a
  general right-hand side; `Levinson.bordered_solve_toeplitz`: the unsymmetric bordering of
  §4.7.8.
* `Trench.inv_symmToeplitz_last`, `Trench.inv_symmToeplitz_eq`,
  `Trench.inv_symmToeplitz_apply_succ`: Trench's description of `T_n⁻¹` ((4.7.4)–(4.7.5)).

## Design

The growing solution vectors are `ℕ`-indexed functions, zero from index `k` on: `Durbin.sol r k`
is `y^{(k)}`, and everything is 0-based, so the book's `y^{(k)} = (y_1, …, y_k)` is
`(sol r k 0, …, sol r k (k − 1))`. The recurrence starts at `k = 0` with the empty solution, so
that the book's `β_k`, `α_k` of (4.7.1) are `Durbin.beta r k`, `Durbin.alpha r k` (`β₀ = 1`,
`α₀ = −r₁`), and Cybenko's reflection coefficients `α_j = y^{(j)}_j` of (4.7.6)–(4.7.7) are
`Durbin.alpha r (j − 1)`. Statements read the solutions on `Fin k` through
`fun i : Fin k => Durbin.sol r k i`; proofs work with the `ℕ`-indexed sums of
`Matrix.symmToeplitz_mulVec_apply`. Where the book's lower bounds of (4.7.6) carry a factor
`1 / (n − 1)`, the statement here omits it (stronger).

The one computation behind all the recurrences is the bordering step of a Toeplitz matrix
(`Levinson.toeplitz_bordered_sum`): `T_{k+1} (x + μ ℰ y, μ) = (T_k x, pᵀ ℰ x + μ (1 + pᵀ y))` when
`T_kᵀ y = −r`. It uses the persymmetry of `T_k` (`T_k ℰ = ℰ T_kᵀ`) and no invertibility; the
symmetric case (`Levinson.bordered_sum`) and the transposed one are instances.

The secular function of §4.7.7 is `Matrix.borderedSecularFunction` of `Numlib.Eigen.DivideConquer`.

## References

* [golub2013matrix] §4.7.
-/

open Matrix Finset

section Sums

variable {K : Type*} [CommRing K] {k : ℕ}

/-- Reversing a sum over `range k`. -/
private theorem sum_range_mul_reflect (f g : ℕ → K) :
    ∑ j ∈ range k, f j * g (k - 1 - j) = ∑ j ∈ range k, f (k - 1 - j) * g j := by
  rw [← sum_range_reflect (fun j => f (k - 1 - j) * g j) k]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [show k - 1 - (k - 1 - j) = j by omega]

/-- A vector given on `Fin k`, extended by zero to `ℕ`. -/
private def ofFin (y : Fin k → K) (j : ℕ) : K := if h : j < k then y ⟨j, h⟩ else 0

private theorem ofFin_coe (y : Fin k → K) : (fun j : Fin k => ofFin y j) = y := by
  funext j
  simp [ofFin]

private theorem sum_fin_eq_sum_ofFin (f : ℕ → K) (y : Fin k → K) :
    ∑ i : Fin k, f i * y i = ∑ i ∈ range k, f i * ofFin y i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => f i * ofFin y i) k]
  simp [ofFin]

end Sums

namespace Levinson

variable {K : Type*} [Field K] {k : ℕ}

/-- **The bordering step of a Toeplitz matrix** ([golub2013matrix] §4.7.3, §4.7.8), `ℕ`-indexed,
with `T_k = toeplitz ρ`, `ρ 0 = 1`: if `T_kᵀ y = −(ρ 1, …, ρ k)`, `T_k x = b` and
`μ (1 + pᵀ y) = b_k − pᵀ ℰ x` (`p_j = ρ (−(j + 1))`), then `T_{k+1} (x + μ ℰ y, μ) = (b₀, …, b_k)`.
The persymmetry of `T_k` replaces any invertibility. -/
theorem toeplitz_bordered_sum {ρ : ℤ → K} (hρ : ρ 0 = 1) {y x b : ℕ → K}
    (hy : ∀ l < k, ∑ j ∈ range k, ρ ((l : ℤ) - j) * y j = -ρ (l + 1))
    (hx : ∀ i < k, ∑ j ∈ range k, ρ ((j : ℤ) - i) * x j = b i) (μ : K)
    (hμ : μ * (1 + ∑ j ∈ range k, ρ (-((j : ℤ) + 1)) * y j) =
      b k - ∑ j ∈ range k, ρ ((j : ℤ) - k) * x j) :
    ∀ i < k + 1, ∑ j ∈ range (k + 1), ρ ((j : ℤ) - i) *
      (if j < k then x j + μ * y (k - 1 - j) else if j = k then μ else 0) = b i := by
  intro i hi
  rw [sum_range_succ, ite_eq_right (lt_irrefl k), ite_eq_left rfl]
  have hsplit : ∑ j ∈ range k, ρ ((j : ℤ) - i) *
      (if j < k then x j + μ * y (k - 1 - j) else if j = k then μ else 0) =
      ∑ j ∈ range k, ρ ((j : ℤ) - i) * x j +
        μ * ∑ j ∈ range k, ρ (((k - 1 - j : ℕ) : ℤ) - i) * y j := by
    rw [← sum_range_mul_reflect (fun j => ρ ((j : ℤ) - i)) y, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [ite_eq_left (mem_range.mp hj)]
    ring
  rw [hsplit]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · -- a row of the leading block: `T_k ℰ y = ℰ T_kᵀ y = −ℰ r`
    have hrefl : ∑ j ∈ range k, ρ (((k - 1 - j : ℕ) : ℤ) - i) * y j = -ρ ((k : ℤ) - i) := by
      rw [show (k : ℤ) - i = ((k - 1 - i : ℕ) : ℤ) + 1 by omega, ← hy (k - 1 - i) (by omega)]
      refine sum_congr rfl fun j hj => ?_
      rw [show ((k - 1 - j : ℕ) : ℤ) - i = ((k - 1 - i : ℕ) : ℤ) - j by
        have := mem_range.mp hj; omega]
    rw [hrefl, hx i hi]
    ring
  · -- the last row
    have h2 : ∑ j ∈ range i, ρ (((i - 1 - j : ℕ) : ℤ) - i) * y j =
        ∑ j ∈ range i, ρ (-((j : ℤ) + 1)) * y j :=
      sum_congr rfl fun j hj => by
        rw [show ((i - 1 - j : ℕ) : ℤ) - i = -((j : ℤ) + 1) by have := mem_range.mp hj; omega]
    rw [h2, sub_self, hρ]
    linear_combination hμ

/-- **The symmetric bordering step** ([golub2013matrix] §4.7.3), `ℕ`-indexed: if
`T_k y = −(r₁, …, r_k)`, `T_k x = b` and `μ β = b_k − ∑ r_{k−j} x_j` with `β = 1 + ∑ r_{j+1} y_j`,
then `T_{k+1} (x + μ ℰ y, μ) = (b₀, …, b_k)`, `T_k = symmToeplitz k r`, `r 0 = 1`. -/
theorem bordered_sum {r : ℕ → K} (hr : r 0 = 1) {y x b : ℕ → K}
    (hy : ∀ i < k, ∑ j ∈ range k, r ((i : ℤ) - j).natAbs * y j = -r (i + 1))
    (hx : ∀ i < k, ∑ j ∈ range k, r ((i : ℤ) - j).natAbs * x j = b i) (μ : K)
    (hμ : μ * (1 + ∑ j ∈ range k, r (j + 1) * y j) = b k - ∑ j ∈ range k, r (k - j) * x j) :
    ∀ i < k + 1, ∑ j ∈ range (k + 1), r ((i : ℤ) - j).natAbs *
      (if j < k then x j + μ * y (k - 1 - j) else if j = k then μ else 0) = b i := by
  have hcomm : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := fun a b => by
    rw [← Int.natAbs_neg, neg_sub]
  have e1 : ∑ j ∈ range k, r (-((j : ℤ) + 1)).natAbs * y j = ∑ j ∈ range k, r (j + 1) * y j :=
    sum_congr rfl fun j _ => by congr 2
  have e2 : ∑ j ∈ range k, r ((j : ℤ) - k).natAbs * x j = ∑ j ∈ range k, r (k - j) * x j :=
    sum_congr rfl fun j hj => by have := mem_range.mp hj; congr 2; omega
  have h := toeplitz_bordered_sum (ρ := fun d => r d.natAbs) (k := k) (x := x) (b := b)
    (by simpa using hr) hy
    (fun i hi => by rw [← hx i hi]; exact sum_congr rfl fun j _ => by rw [hcomm]) μ
    (by rw [e1, e2]; exact hμ)
  intro i hi
  rw [← h i hi]
  exact sum_congr rfl fun j _ => by rw [hcomm]

/-- The vector `(x + μ ℰ_k y, μ)` of the bordering step, read on `ℕ`. -/
private theorem snoc_eq {y x : Fin k → K} (μ : K) :
    Fin.snoc (α := fun _ => K) (x + μ • (exchange k *ᵥ y)) μ = fun j : Fin (k + 1) =>
      (if (j : ℕ) < k then ofFin x j + μ * ofFin y (k - 1 - j) else if (j : ℕ) = k then μ
        else 0) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast j =>
    have h1 : k - 1 - (j : ℕ) < k := by omega
    have hr : Fin.rev j = ⟨k - 1 - (j : ℕ), h1⟩ := Fin.ext (by
      rw [Fin.val_rev]
      exact (by omega : k - ((j : ℕ) + 1) = k - 1 - (j : ℕ)))
    simp only [Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, exchange_mulVec_apply,
      smul_eq_mul, Fin.val_castSucc, j.isLt, ite_true, ofFin, dite_true, h1, hr]

omit [Field K] in
private theorem snoc_apply_eq (b : Fin k → K) (b' : K) (i : Fin (k + 1)) :
    Fin.snoc (α := fun _ => K) b b' i = if h : (i : ℕ) < k then b ⟨i, h⟩ else b' := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [Fin.snoc_castSucc, i.isLt]

/-- **The bordering step of a Toeplitz matrix** ([golub2013matrix] §4.7.8), `T_k = toeplitz ρ`,
`ρ 0 = 1`: if `T_kᵀ y = −(ρ 1, …, ρ k)`, `T_k x = b` and `μ (1 + pᵀ y) = b' − pᵀ ℰ_k x` with
`p_i = ρ (−(i + 1))`, then `T_{k+1} (x + μ ℰ_k y, μ) = (b, b')`. -/
theorem toeplitz_bordered_solve {ρ : ℤ → K} (hρ : ρ 0 = 1) {y x b : Fin k → K} (b' : K)
    (hy : (toeplitz ρ : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ y = fun l : Fin k => -ρ (((l : ℕ) : ℤ) + 1))
    (hx : (toeplitz ρ : Matrix (Fin k) (Fin k) K) *ᵥ x = b) (μ : K)
    (hμ : μ * (1 + ∑ i : Fin k, ρ (-(((i : ℕ) : ℤ) + 1)) * y i) =
      b' - ∑ i : Fin k, ρ (((i : ℕ) : ℤ) - k) * x i) :
    (toeplitz ρ : Matrix (Fin (k + 1)) (Fin (k + 1)) K) *ᵥ
      Fin.snoc (α := fun _ => K) (x + μ • (exchange k *ᵥ y)) μ =
        Fin.snoc (α := fun _ => K) b b' := by
  have hy' : ∀ l < k, ∑ j ∈ range k, ρ ((l : ℤ) - j) * ofFin y j = -ρ (l + 1) := by
    intro l hl
    have := congrFun hy ⟨l, hl⟩
    rw [transpose_toeplitz, ← ofFin_coe y, toeplitz_mulVec_apply] at this
    simp only [neg_sub] at this
    exact_mod_cast this
  have hx' : ∀ i < k, ∑ j ∈ range k, ρ ((j : ℤ) - i) * ofFin x j =
      (fun i => if h : i < k then b ⟨i, h⟩ else b') i := by
    intro i hi
    have := congrFun hx ⟨i, hi⟩
    rw [← ofFin_coe x, toeplitz_mulVec_apply] at this
    simpa [hi] using this
  have h := toeplitz_bordered_sum hρ hy' hx' μ (by
    rw [← sum_fin_eq_sum_ofFin (fun i => ρ (-((i : ℤ) + 1))),
      ← sum_fin_eq_sum_ofFin (fun i => ρ ((i : ℤ) - k)), hμ]
    simp)
  funext i
  rw [snoc_eq, toeplitz_mulVec_apply (v := fun j : ℕ =>
    if j < k then ofFin x j + μ * ofFin y (k - 1 - j) else if j = k then μ else 0), h i i.isLt,
    snoc_apply_eq]

/-- **Levinson's bordering step** ([golub2013matrix] (4.7.2)–(4.7.3)): with
`T_k = symmToeplitz k r`, `r 0 = 1`, if `T_k y = −(r₁, …, r_k)`, `T_k x = b` and
`μ (1 + rᵀ y) = b' − rᵀ ℰ_k x`, then `T_{k+1} (x + μ ℰ_k y, μ) = (b, b')`. No invertibility of
`T_k` is used. -/
theorem bordered_solve {r : ℕ → K} (hr : r 0 = 1) {y x b : Fin k → K} (b' : K)
    (hy : symmToeplitz k r *ᵥ y = fun i : Fin k => -r ((i : ℕ) + 1))
    (hx : symmToeplitz k r *ᵥ x = b) (μ : K)
    (hμ : μ * (1 + ∑ i : Fin k, r ((i : ℕ) + 1) * y i) = b' - ∑ i : Fin k, r (k - i) * x i) :
    symmToeplitz (k + 1) r *ᵥ Fin.snoc (α := fun _ => K) (x + μ • (exchange k *ᵥ y)) μ =
      Fin.snoc (α := fun _ => K) b b' := by
  have e1 : ∑ i : Fin k, r (-(((i : ℕ) : ℤ) + 1)).natAbs * y i =
      ∑ i : Fin k, r ((i : ℕ) + 1) * y i :=
    sum_congr rfl fun i _ => by congr 2
  have e2 : ∑ i : Fin k, r (((i : ℕ) : ℤ) - k).natAbs * x i = ∑ i : Fin k, r (k - i) * x i :=
    sum_congr rfl fun i _ => by have := i.isLt; congr 2; omega
  rw [symmToeplitz_eq_toeplitz] at hx ⊢
  refine toeplitz_bordered_solve (by simpa using hr) b' ?_ hx μ ?_
  · rw [← symmToeplitz_eq_toeplitz k r, (symmToeplitz_isSymm k r).eq, hy]
    funext l
    congr 2
  · rw [e1, e2]
    exact hμ

end Levinson

namespace Durbin

variable {K : Type*} [Field K]

/-- **Durbin's recurrence** ([golub2013matrix] (4.7.1)), `ℕ`-indexed: `sol r k` is the solution
`y^{(k)}` of the Yule–Walker system of order `k`, zero from index `k` on; `sol r 0 = 0` and
`y^{(k+1)} = (y^{(k)} + α_k ℰ_k y^{(k)}, α_k)` with `α_k = Durbin.alpha r k` and the denominator
`β_k = Durbin.beta r k`. -/
def sol (r : ℕ → K) : ℕ → ℕ → K
  | 0 => fun _ => 0
  | k + 1 =>
    let y := sol r k
    let α := -(r (k + 1) + ∑ i ∈ range k, r (k - i) * y i) /
      (1 + ∑ i ∈ range k, r (i + 1) * y i)
    fun i => if i < k then y i + α * y (k - 1 - i) else if i = k then α else 0

/-- The denominators `β_k = 1 + rᵀ y^{(k)}` of Durbin's recurrence. -/
def beta (r : ℕ → K) (k : ℕ) : K :=
  1 + ∑ i ∈ range k, r (i + 1) * sol r k i

/-- The reflection coefficients `α_k = −(r_{k+1} + rᵀ ℰ_k y^{(k)}) / β_k` of Durbin's
recurrence. -/
def alpha (r : ℕ → K) (k : ℕ) : K :=
  -(r (k + 1) + ∑ i ∈ range k, r (k - i) * sol r k i) / beta r k

variable (r : ℕ → K)

/-- The empty solution `y^{(0)} = 0`. -/
@[simp]
theorem sol_zero (i : ℕ) : sol r 0 i = 0 := rfl

/-- One step of Durbin's recurrence: `y^{(k+1)} = (y^{(k)} + α_k ℰ_k y^{(k)}, α_k)`. -/
theorem sol_succ (k i : ℕ) :
    sol r (k + 1) i =
      if i < k then sol r k i + alpha r k * sol r k (k - 1 - i) else if i = k then alpha r k
      else 0 := rfl

/-- `β₀ = 1`. -/
@[simp]
theorem beta_zero : beta r 0 = 1 := by simp [beta]

/-- `sol r k` vanishes from index `k` on. -/
theorem sol_of_le {k i : ℕ} (h : k ≤ i) : sol r k i = 0 := by
  cases k with
  | zero => rfl
  | succ k => rw [sol_succ, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The last entry of `y^{(k+1)}` is `α_k`. -/
theorem sol_succ_self (k : ℕ) : sol r (k + 1) k = alpha r k := by
  rw [sol_succ, ite_eq_right (lt_irrefl k), ite_eq_left rfl]

/-- The defining relation `α_k β_k = −(r_{k+1} + rᵀ ℰ_k y^{(k)})` when `β_k ≠ 0`. -/
theorem alpha_mul_beta {k : ℕ} (h : beta r k ≠ 0) :
    alpha r k * beta r k = -(r (k + 1) + ∑ i ∈ range k, r (k - i) * sol r k i) :=
  div_mul_cancel₀ _ h

variable {r}

/-- The Yule–Walker equations of every order, `ℕ`-indexed. -/
theorem sum_symmToeplitz_sol (hr : r 0 = 1) {k : ℕ} (hβ : ∀ j < k, beta r j ≠ 0) :
    ∀ i < k, ∑ j ∈ range k, r ((i : ℤ) - j).natAbs * sol r k j = -r (i + 1) := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    have ih' := ih fun j hj => hβ j (by omega)
    have hαβ := alpha_mul_beta r (hβ k (by omega))
    rw [beta] at hαβ
    have h := Levinson.bordered_sum (b := fun i => -r (i + 1)) hr ih' ih' (alpha r k)
      (by linear_combination hαβ)
    intro i hi
    rw [← h i hi]
    rfl

/-- **Correctness of Durbin's recurrence** ([golub2013matrix] (4.7.1)): if `r 0 = 1` and
`β_j ≠ 0` for `j < k`, then `T_k y^{(k)} = −(r₁, …, r_k)`. -/
theorem symmToeplitz_mulVec_sol (hr : r 0 = 1) {k : ℕ} (hβ : ∀ j < k, beta r j ≠ 0) :
    symmToeplitz k r *ᵥ (fun i : Fin k => sol r k i) = fun i : Fin k => -r ((i : ℕ) + 1) := by
  funext i
  rw [symmToeplitz_mulVec_apply]
  exact sum_symmToeplitz_sol hr hβ i i.isLt

/-- **`β_{k+1} = (1 − α_k²) β_k`** ([golub2013matrix] §4.7.3), pure algebra from the
recurrence. -/
theorem beta_succ {k : ℕ} (h : beta r k ≠ 0) :
    beta r (k + 1) = (1 - alpha r k ^ 2) * beta r k := by
  have hαβ := alpha_mul_beta r h
  have hs : ∑ i ∈ range (k + 1), r (i + 1) * sol r (k + 1) i =
      ∑ i ∈ range k, r (i + 1) * sol r k i +
        alpha r k * (∑ i ∈ range k, r (k - i) * sol r k i + r (k + 1)) := by
    rw [sum_range_succ, sol_succ_self]
    have : ∑ i ∈ range k, r (i + 1) * sol r (k + 1) i =
        ∑ i ∈ range k, r (i + 1) * sol r k i +
          alpha r k * ∑ i ∈ range k, r (i + 1) * sol r k (k - 1 - i) := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      rw [sol_succ, ite_eq_left (mem_range.mp hi)]
      ring
    rw [this, sum_range_mul_reflect (fun i => r (i + 1)) (sol r k)]
    have h2 : ∑ i ∈ range k, r (k - 1 - i + 1) * sol r k i =
        ∑ i ∈ range k, r (k - i) * sol r k i :=
      sum_congr rfl fun i hi => by
        rw [show k - 1 - i + 1 = k - i by have := mem_range.mp hi; omega]
    rw [h2]
    ring
  rw [beta, hs, beta]
  rw [beta] at hαβ
  linear_combination (alpha r k) * hαβ

/-- `β_k = ∏_{j<k} (1 − α_j²)` when no `β_j` vanishes. -/
theorem beta_eq_prod {k : ℕ} (hβ : ∀ j < k, beta r j ≠ 0) :
    beta r k = ∏ j ∈ range k, (1 - alpha r j ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [beta_succ (hβ k (by omega)), ih fun j hj => hβ j (by omega), prod_range_succ, mul_comm]

/-- The book's `(ℰ_k y^{(k)}, 1)`, `ℕ`-indexed: the `k`-th column of the unit upper triangular
factor `U` of `Uᵀ T U = diag(β)` (`Durbin.unitUpper`), and (scaled by `1 / β_k`) the last column
of `T_{k+1}⁻¹`. -/
def revSol (r : ℕ → K) (k : ℕ) (j : ℕ) : K :=
  if j < k then sol r k (k - 1 - j) else if j = k then 1 else 0

/-- `(ℰ_k y^{(k)}, 1)` vanishes beyond index `k`. -/
theorem revSol_of_lt {k j : ℕ} (h : k < j) : revSol r k j = 0 := by
  rw [revSol, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The entry `k` of `(ℰ_k y^{(k)}, 1)` is `1`. -/
@[simp]
theorem revSol_self (k : ℕ) : revSol r k k = 1 := by
  rw [revSol, ite_eq_right (lt_irrefl k), ite_eq_left rfl]

/-- A sum against `revSol r k` only sees the indices up to `k`. -/
theorem sum_mul_revSol {k m : ℕ} (h : k < m) (f : ℕ → K) :
    ∑ j ∈ range m, f j * revSol r k j = ∑ j ∈ range (k + 1), f j * revSol r k j := by
  refine (sum_subset (range_subset_range.mpr (by omega)) fun j hj hj' => ?_).symm
  rw [revSol_of_lt (by simp only [mem_range] at hj'; omega), mul_zero]

/-- **`T_{k+1} (ℰ_k y^{(k)}, 1) = β_k e_k`** ([golub2013matrix] §4.7.3–4.7.4). -/
theorem sum_symmToeplitz_revSol (hr : r 0 = 1) {k : ℕ} (hβ : ∀ j < k, beta r j ≠ 0) :
    ∀ i ≤ k, ∑ j ∈ range (k + 1), r ((i : ℤ) - j).natAbs * revSol r k j =
      if i = k then beta r k else 0 := by
  intro i hi
  have hy := sum_symmToeplitz_sol hr hβ
  rw [sum_range_succ]
  have hs : ∑ j ∈ range k, r ((i : ℤ) - j).natAbs * revSol r k j =
      ∑ j ∈ range k, r ((i : ℤ) - ((k - 1 - j : ℕ) : ℤ)).natAbs * sol r k j := by
    rw [← sum_range_mul_reflect (fun j => r ((i : ℤ) - j).natAbs) (sol r k)]
    exact sum_congr rfl fun j hj => by rw [revSol, ite_eq_left (mem_range.mp hj)]
  rw [hs, revSol_self, mul_one]
  rcases Nat.lt_or_eq_of_le hi with hi | rfl
  · rw [ite_eq_right hi.ne]
    have : ∑ j ∈ range k, r ((i : ℤ) - ((k - 1 - j : ℕ) : ℤ)).natAbs * sol r k j =
        -r (k - i) := by
      rw [← show k - 1 - i + 1 = k - i by omega, ← hy (k - 1 - i) (by omega)]
      refine sum_congr rfl fun j hj => ?_
      congr 2
      exact Int.natAbs_eq_natAbs_iff.mpr (Or.inr (by have := mem_range.mp hj; omega))
    rw [this, show ((i : ℤ) - k).natAbs = k - i by omega]
    ring
  · rw [ite_eq_left rfl, beta, sub_self, Int.natAbs_zero, hr, add_comm]
    congr 1
    exact sum_congr rfl fun j hj => by
      rw [show ((i : ℤ) - ((i - 1 - j : ℕ) : ℤ)).natAbs = j + 1 by have := mem_range.mp hj; omega]

/-- **`det T_{k+1} = β_k det T_k`** ([golub2013matrix] §4.7.3, the congruence
`[I ℰy; 0 1]ᵀ T_{k+1} [I ℰy; 0 1] = diag(T_k, β_k)`), when `r 0 = 1` and `β_j ≠ 0` for `j < k`. -/
theorem det_symmToeplitz_succ (hr : r 0 = 1) {k : ℕ} (hβ : ∀ j < k, beta r j ≠ 0) :
    det (symmToeplitz (k + 1) r) = beta r k * det (symmToeplitz k r) := by
  set T := symmToeplitz (k + 1) r
  let P : Matrix (Fin (k + 1)) (Fin (k + 1)) K :=
    of fun i j => if j = Fin.last k then revSol r k i else if i = j then 1 else 0
  have hP : det P = 1 := by
    rw [det_of_isUpperTriangular]
    · refine prod_eq_one fun i _ => ?_
      simp only [P, of_apply]
      split_ifs with h
      · rw [h, Fin.val_last, revSol_self]
      · rfl
    · intro i j hij
      simp only [P, of_apply]
      have hj : j ≠ Fin.last k := fun h => by
        rw [h] at hij; exact absurd hij (not_lt.mpr (Fin.le_last i))
      rw [ite_eq_right hj, ite_eq_right (fun h => by rw [h] at hij; exact lt_irrefl _ hij)]
  have hcol : ∀ i : Fin (k + 1), (T * P) i (Fin.last k) =
      if (i : ℕ) = k then beta r k else 0 := by
    intro i
    rw [← sum_symmToeplitz_revSol hr hβ i (Fin.is_le i), mul_apply]
    rw [← Fin.sum_univ_eq_sum_range (fun j => r ((i : ℤ) - j).natAbs * revSol r k j)]
    simp only [P, of_apply, ite_true, T, symmToeplitz_apply]
  have hsub : (T * P).submatrix Fin.castSucc Fin.castSucc = symmToeplitz k r := by
    ext i j
    simp only [submatrix_apply, mul_apply, P, of_apply, Fin.castSucc_ne_last, ite_false,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true, T, symmToeplitz_apply,
      Fin.val_castSucc]
  have hTP : det (T * P) = det T := by rw [det_mul, hP, mul_one]
  rw [← hTP, det_succ_column (T * P) (Fin.last k), sum_eq_single (Fin.last k)]
  · rw [hcol, Fin.val_last, ite_eq_left rfl, Fin.succAbove_last, hsub, ← two_mul, pow_mul]
    simp
  · intro i _ hi
    rw [hcol, ite_eq_right (fun h => hi (Fin.ext (by simpa using h))), mul_zero, zero_mul]
  · simp

/-- `det T_k = β₀ ⋯ β_{k−1}` when `r 0 = 1` and no `β_j` vanishes. -/
theorem det_symmToeplitz (hr : r 0 = 1) {k : ℕ} (hβ : ∀ j < k, beta r j ≠ 0) :
    det (symmToeplitz k r) = ∏ j ∈ range k, beta r j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [det_symmToeplitz_succ hr fun j hj => hβ j (by omega), ih fun j hj => hβ j (by omega),
      prod_range_succ, mul_comm]

/-- The unit upper triangular matrix `U` of [golub2013matrix] P4.7.2 whose `k`-th column is
`(ℰ_k y^{(k)}, 1, 0, …, 0)`. -/
def unitUpper (r : ℕ → K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  of fun i k => revSol r k i

/-- The columns of `T U`: entry `i ≤ k` of `T_n (ℰ_k y^{(k)}, 1, 0, …)` is `β_k δ_ik`. -/
private theorem symmToeplitz_mul_unitUpper_apply (hr : r 0 = 1) {n : ℕ}
    (hβ : ∀ j, j + 1 < n → beta r j ≠ 0) (i k : Fin n) (hik : (i : ℕ) ≤ k) :
    (symmToeplitz n r * unitUpper r n) i k = if (i : ℕ) = k then beta r k else 0 := by
  rw [mul_apply]
  simp only [unitUpper, of_apply, symmToeplitz_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => r ((i : ℤ) - j).natAbs * revSol r k j),
    sum_mul_revSol k.isLt]
  exact sum_symmToeplitz_revSol hr (fun j hj => hβ j (by omega)) i hik

/-- **`Uᵀ T U = diag(β)`** ([golub2013matrix] P4.7.2, cited for the bounds of §4.7.6): with `U` the
unit upper triangular matrix of the reversed Yule–Walker solutions (`Durbin.unitUpper`), under the
hypotheses of `Durbin.symmToeplitz_mulVec_sol`. Hence `T_n⁻¹ = U diag(β)⁻¹ Uᵀ`. -/
theorem transpose_mul_mul_eq_diagonal (hr : r 0 = 1) {n : ℕ}
    (hβ : ∀ j, j + 1 < n → beta r j ≠ 0) :
    (unitUpper r n)ᵀ * symmToeplitz n r * unitUpper r n = diagonal fun k : Fin n => beta r k := by
  have hle : ∀ l k : Fin n, (l : ℕ) ≤ k →
      ((unitUpper r n)ᵀ * symmToeplitz n r * unitUpper r n) l k =
        if l = k then beta r k else 0 := by
    intro l k hlk
    rw [Matrix.mul_assoc, mul_apply]
    have : ∀ i : Fin n, (unitUpper r n)ᵀ l i * (symmToeplitz n r * unitUpper r n) i k =
        revSol r l i * (if (i : ℕ) = k then beta r k else 0) := by
      intro i
      rw [transpose_apply]
      by_cases hi : (i : ℕ) ≤ l
      · rw [symmToeplitz_mul_unitUpper_apply hr hβ i k (by omega)]
        rfl
      · simp only [unitUpper, of_apply, revSol_of_lt (by omega : (l : ℕ) < i), zero_mul]
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp only [mul_ite, mul_zero, Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases h : l = k
    · subst h; simp
    · rw [ite_eq_right h, revSol_of_lt (by have := Fin.val_injective.ne h; omega), zero_mul]
  have hsymm : ((unitUpper r n)ᵀ * symmToeplitz n r * unitUpper r n)ᵀ =
      (unitUpper r n)ᵀ * symmToeplitz n r * unitUpper r n := by
    rw [transpose_mul, transpose_mul, transpose_transpose, (symmToeplitz_isSymm n r).eq,
      Matrix.mul_assoc]
  ext l k
  rw [diagonal_apply]
  rcases le_total (l : ℕ) k with h | h
  · rw [hle l k h]
    split_ifs with hlk
    · rw [hlk]
    · rfl
  · rw [← hsymm, transpose_apply, hle k l h]
    by_cases hkl : k = l
    · subst hkl; rfl
    · rw [ite_eq_right hkl, ite_eq_right (Ne.symm hkl)]

/-- **The sum of the Yule–Walker solution** ([golub2013matrix] §4.7.6):
`1 + ∑_i y^{(k)}_i = ∏_{j<k} (1 + α_j)`. Pure recurrence, no definiteness. -/
theorem sum_sol_add_one (k : ℕ) :
    1 + ∑ i ∈ range k, sol r k i = ∏ j ∈ range k, (1 + alpha r j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sol_succ_self, prod_range_succ, ← ih]
    have : ∑ i ∈ range k, sol r (k + 1) i =
        ∑ i ∈ range k, sol r k i + alpha r k * ∑ i ∈ range k, sol r k (k - 1 - i) := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun i hi => by rw [sol_succ, ite_eq_left (mem_range.mp hi)]
    rw [this, sum_range_reflect (sol r k) k]
    ring

end Durbin

namespace Durbin

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r : ℕ → K}

/-- The triangle-inequality companion of `Durbin.sum_sol_add_one`:
`1 + ∑_i |y^{(k)}_i| ≤ ∏_{j<k} (1 + |α_j|)`. -/
theorem one_add_sum_abs_sol_le (k : ℕ) :
    1 + ∑ i ∈ range k, |sol r k i| ≤ ∏ j ∈ range k, (1 + |alpha r j|) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sol_succ_self, prod_range_succ]
    have h1 : ∑ i ∈ range k, |sol r (k + 1) i| ≤
        ∑ i ∈ range k, |sol r k i| + |alpha r k| * ∑ i ∈ range k, |sol r k i| := by
      calc ∑ i ∈ range k, |sol r (k + 1) i|
          ≤ ∑ i ∈ range k, (|sol r k i| + |alpha r k| * |sol r k (k - 1 - i)|) :=
            sum_le_sum fun i hi => by
              rw [sol_succ, ite_eq_left (mem_range.mp hi), ← abs_mul]
              exact abs_add_le _ _
        _ = _ := by
            rw [sum_add_distrib, ← mul_sum, sum_range_reflect (fun i => |sol r k i|) k]
    have h0 : 0 ≤ ∑ i ∈ range k, |sol r k i| := sum_nonneg fun i _ => abs_nonneg _
    calc 1 + (∑ i ∈ range k, |sol r (k + 1) i| + |alpha r k|)
        ≤ (1 + ∑ i ∈ range k, |sol r k i|) * (1 + |alpha r k|) := by
          nlinarith [abs_nonneg (alpha r k)]
      _ ≤ (∏ j ∈ range k, (1 + |alpha r j|)) * (1 + |alpha r k|) :=
        mul_le_mul_of_nonneg_right ih (by positivity)

/-- **(4.7.7)** ([golub2013matrix] §4.7.6): if the reflection coefficients `α_0, …, α_{k−1}` are
nonnegative, then `∑_i |y^{(k)}_i| = ∏_{j<k} (1 + α_j) − 1`. -/
theorem sum_abs_sol_eq {k : ℕ} (h : ∀ j < k, 0 ≤ alpha r j) :
    ∑ i ∈ range k, |sol r k i| = ∏ j ∈ range k, (1 + alpha r j) - 1 := by
  have hnn : ∀ i, 0 ≤ sol r k i := by
    induction k with
    | zero => intro i; exact le_rfl
    | succ k ih =>
      have ih := ih fun j hj => h j (by omega)
      intro i
      rw [sol_succ]
      split_ifs
      · exact add_nonneg (ih i) (mul_nonneg (h k (by omega)) (ih _))
      · exact h k (by omega)
      · exact le_rfl
  rw [← sum_sol_add_one, add_sub_cancel_left]
  exact sum_congr rfl fun i _ => abs_of_nonneg (hnn i)

end Durbin

namespace Durbin

variable {K : Type*} [Field K] {r : ℕ → K}

/-- **The Yule–Walker bordering step** ([golub2013matrix] §4.7.3): if `T_k y = −(r₁, …, r_k)`,
`r 0 = 1` and `α (1 + rᵀ y) = −(r_{k+1} + rᵀ ℰ_k y)`, then
`T_{k+1} (y + α ℰ_k y, α) = −(r₁, …, r_{k+1})`. No invertibility of `T_k` is used. -/
theorem bordered_solve (hr : r 0 = 1) {k : ℕ} {y : Fin k → K}
    (hy : symmToeplitz k r *ᵥ y = fun i : Fin k => -r ((i : ℕ) + 1)) (α : K)
    (hα : α * (1 + ∑ i : Fin k, r ((i : ℕ) + 1) * y i) =
      -(r (k + 1) + ∑ i : Fin k, r (k - i) * y i)) :
    symmToeplitz (k + 1) r *ᵥ Fin.snoc (α := fun _ => K) (y + α • (exchange k *ᵥ y)) α =
      fun i : Fin (k + 1) => -r ((i : ℕ) + 1) := by
  rw [Levinson.bordered_solve hr (-r (k + 1)) hy hy α (by rw [hα]; ring)]
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

end Durbin

namespace Levinson

variable {K : Type*} [Field K]

/-- **Levinson's recurrence** ([golub2013matrix] (4.7.2)–(4.7.3), the specification of
Algorithm 4.7.2), `ℕ`-indexed like `Durbin.sol`: `sol r b k` solves `T_k x = (b₀, …, b_{k−1})`,
with `x^{(k+1)} = (x^{(k)} + μ_k ℰ_k y^{(k)}, μ_k)`, `μ_k = Levinson.mu r b k`. -/
def sol (r b : ℕ → K) : ℕ → ℕ → K
  | 0 => fun _ => 0
  | k + 1 =>
    let x := sol r b k
    let μ := (b k - ∑ i ∈ range k, r (k - i) * x i) / Durbin.beta r k
    fun i => if i < k then x i + μ * Durbin.sol r k (k - 1 - i) else if i = k then μ else 0

/-- The last entry `μ_k = (b_k − rᵀ ℰ_k x^{(k)}) / β_k` of Levinson's recurrence. -/
def mu (r b : ℕ → K) (k : ℕ) : K :=
  (b k - ∑ i ∈ range k, r (k - i) * sol r b k i) / Durbin.beta r k

/-- One step of Levinson's recurrence: `x^{(k+1)} = (x^{(k)} + μ_k ℰ_k y^{(k)}, μ_k)`. -/
theorem sol_succ (r b : ℕ → K) (k i : ℕ) :
    sol r b (k + 1) i =
      if i < k then sol r b k i + mu r b k * Durbin.sol r k (k - 1 - i) else if i = k then mu r b k
      else 0 := rfl

variable {r : ℕ → K}

/-- Levinson's recurrence solves the systems of every order, `ℕ`-indexed. -/
theorem sum_symmToeplitz_sol (hr : r 0 = 1) (b : ℕ → K) {k : ℕ}
    (hβ : ∀ j < k, Durbin.beta r j ≠ 0) :
    ∀ i < k, ∑ j ∈ range k, r ((i : ℤ) - j).natAbs * sol r b k j = b i := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    have h := bordered_sum hr (Durbin.sum_symmToeplitz_sol hr fun j hj => hβ j (by omega))
      (ih fun j hj => hβ j (by omega)) (mu r b k) (div_mul_cancel₀ _ (hβ k (by omega)))
    intro i hi
    rw [← h i hi]
    rfl

/-- **Correctness of Levinson's recurrence** ([golub2013matrix] §4.7.3): if `r 0 = 1` and
`β_j ≠ 0` for `j < k`, then `T_k x^{(k)} = (b₀, …, b_{k−1})`. -/
theorem symmToeplitz_mulVec_sol (hr : r 0 = 1) (b : ℕ → K) {k : ℕ}
    (hβ : ∀ j < k, Durbin.beta r j ≠ 0) :
    symmToeplitz k r *ᵥ (fun i : Fin k => sol r b k i) = fun i : Fin k => b i := by
  funext i
  rw [symmToeplitz_mulVec_apply]
  exact sum_symmToeplitz_sol hr b hβ i i.isLt

/-- **The unsymmetric bordering** ([golub2013matrix] (4.7.12)→(4.7.13); the book leaves the formulas
to P4.7.11). Let `T_{k+1} = toeplitz ρ` on `Fin (k + 1)` with `ρ 0 = 1`, `r_j = ρ j`,
`p_j = ρ (−j)`, so that `T_{k+1} = [T_k, ℰ r; pᵀ ℰ, 1]`. Given `T_kᵀ y = −r`, `T_k w = −p`,
`T_k x = b`: with `α (1 + rᵀ w) = −(r_{k+1} + rᵀ ℰ y)`, `ν (1 + pᵀ y) = −(p_{k+1} + pᵀ ℰ w)` and
`μ (1 + pᵀ y) = b_{k+1} − pᵀ ℰ x`,
`T_{k+1}ᵀ (y + α ℰ w, α) = −(r₁, …, r_{k+1})`, `T_{k+1} (w + ν ℰ y, ν) = −(p₁, …, p_{k+1})` and
`T_{k+1} (x + μ ℰ y, μ) = (b, b_{k+1})`. -/
theorem bordered_solve_toeplitz {ρ : ℤ → K} (hρ : ρ 0 = 1) {k : ℕ} {y w x b : Fin k → K}
    (b' : K)
    (hy : (toeplitz ρ : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ y = fun i : Fin k => -ρ (((i : ℕ) : ℤ) + 1))
    (hw : (toeplitz ρ : Matrix (Fin k) (Fin k) K) *ᵥ w =
      fun i : Fin k => -ρ (-(((i : ℕ) : ℤ) + 1)))
    (hx : (toeplitz ρ : Matrix (Fin k) (Fin k) K) *ᵥ x = b) (α ν μ : K)
    (hα : α * (1 + ∑ i : Fin k, ρ (((i : ℕ) : ℤ) + 1) * w i) =
      -(ρ ((k : ℤ) + 1) + ∑ i : Fin k, ρ ((k : ℤ) - (i : ℕ)) * y i))
    (hν : ν * (1 + ∑ i : Fin k, ρ (-(((i : ℕ) : ℤ) + 1)) * y i) =
      -(ρ (-((k : ℤ) + 1)) + ∑ i : Fin k, ρ (((i : ℕ) : ℤ) - k) * w i))
    (hμ : μ * (1 + ∑ i : Fin k, ρ (-(((i : ℕ) : ℤ) + 1)) * y i) =
      b' - ∑ i : Fin k, ρ (((i : ℕ) : ℤ) - k) * x i) :
    (toeplitz ρ : Matrix (Fin (k + 1)) (Fin (k + 1)) K)ᵀ *ᵥ
        Fin.snoc (α := fun _ => K) (y + α • (exchange k *ᵥ w)) α =
          (fun i : Fin (k + 1) => -ρ (((i : ℕ) : ℤ) + 1)) ∧
      (toeplitz ρ : Matrix (Fin (k + 1)) (Fin (k + 1)) K) *ᵥ
        Fin.snoc (α := fun _ => K) (w + ν • (exchange k *ᵥ y)) ν =
          (fun i : Fin (k + 1) => -ρ (-(((i : ℕ) : ℤ) + 1))) ∧
      (toeplitz ρ : Matrix (Fin (k + 1)) (Fin (k + 1)) K) *ᵥ
        Fin.snoc (α := fun _ => K) (x + μ • (exchange k *ᵥ y)) μ =
          Fin.snoc (α := fun _ => K) b b' := by
  have hsnoc : ∀ f : ℤ → K, Fin.snoc (α := fun _ => K) (fun i : Fin k => f (((i : ℕ) : ℤ) + 1))
      (f ((k : ℤ) + 1)) = fun i : Fin (k + 1) => f (((i : ℕ) : ℤ) + 1) := by
    intro f
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  refine ⟨?_, ?_, toeplitz_bordered_solve hρ b' hy hx μ hμ⟩
  · -- the transposed system is the bordering of the reflected Toeplitz matrix
    rw [transpose_toeplitz] at hy ⊢
    rw [← hsnoc fun d => -ρ d]
    refine toeplitz_bordered_solve (ρ := fun d => ρ (-d)) (by simpa using hρ) _ ?_ hy α ?_
    · simpa [transpose_toeplitz] using hw
    · simp only [neg_neg, neg_sub]
      rw [hα]
      ring
  · rw [← hsnoc fun d => -ρ (-d)]
    refine toeplitz_bordered_solve hρ _ hy hw ν ?_
    rw [hν]
    ring

end Levinson

namespace Durbin

variable {r : ℕ → ℝ}

/-- **The `β_k` of a positive definite Toeplitz matrix are positive** ([golub2013matrix] §4.7.3,
"the denominator is positive because `T_{k+1}` is positive definite"): `β_k` is the value of the
quadratic form of `T_n` at `(ℰ_k y^{(k)}, 1, 0, …, 0)`. -/
theorem beta_pos (hr : r 0 = 1) {n : ℕ} (hT : (symmToeplitz n r).PosDef) :
    ∀ k < n, 0 < beta r k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hβ : ∀ j < k, beta r j ≠ 0 := fun j hj => (ih j hj (by omega)).ne'
  set x : Fin n → ℝ := fun i => revSol r k i with hxdef
  have hx : x ≠ 0 := fun h => by
    have := congrFun h ⟨k, hk⟩
    simp [x] at this
  have hq : star x ⬝ᵥ (symmToeplitz n r *ᵥ x) = beta r k := by
    rw [star_trivial, dotProduct_comm, dotProduct]
    have h1 : ∀ i : Fin n, (symmToeplitz n r *ᵥ x) i * x i =
        (∑ j ∈ range n, r ((i : ℤ) - j).natAbs * revSol r k j) * revSol r k i :=
      fun i => by rw [symmToeplitz_mulVec_apply]
    rw [Finset.sum_congr rfl fun i _ => h1 i,
      Fin.sum_univ_eq_sum_range (fun i => (∑ j ∈ range n, r ((i : ℤ) - j).natAbs *
        revSol r k j) * revSol r k i) n, sum_mul_revSol hk]
    rw [Finset.sum_congr rfl fun i hi => by
      rw [sum_mul_revSol hk, sum_symmToeplitz_revSol hr hβ i
        (by have := mem_range.mp hi; omega)]]
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq' (range (k + 1)) k, ite_eq_left (self_mem_range_succ k), revSol_self, mul_one]
  rw [← hq]
  exact hT.dotProduct_mulVec_pos hx

/-- **The reflection coefficients of a positive definite Toeplitz matrix** ([golub2013matrix]
§4.7.6, "in exact arithmetic these scalars satisfy `|α_k| < 1`"): `|α_k| < 1` for `k + 1 < n`. -/
theorem abs_alpha_lt_one (hr : r 0 = 1) {n : ℕ} (hT : (symmToeplitz n r).PosDef) {k : ℕ}
    (hk : k + 1 < n) : |alpha r k| < 1 := by
  have h0 := beta_pos hr hT k (by omega)
  have h1 := beta_pos hr hT (k + 1) hk
  rw [beta_succ h0.ne'] at h1
  have : 0 < 1 - alpha r k ^ 2 := pos_of_mul_pos_left h1 h0.le
  rw [← sq_lt_one_iff_abs_lt_one]
  linarith

end Durbin

namespace Trench

open Durbin

variable {K : Type*} [Field K] {r : ℕ → K}

/-- The last entry `γ = 1 / β_m = 1 / (1 + rᵀ y^{(m)})` of `T_{m+1}⁻¹`
([golub2013matrix] (4.7.4)). -/
def gamma (r : ℕ → K) (m : ℕ) : K := 1 / beta r m

/-- The rest `v = γ ℰ_m y^{(m)}` of the last column of `T_{m+1}⁻¹` ([golub2013matrix] (4.7.4)). -/
def lastCol (r : ℕ → K) (m : ℕ) : Fin m → K :=
  gamma r m • (exchange m *ᵥ fun i : Fin m => sol r m i)

private theorem isUnit_det_symmToeplitz (hr : r 0 = 1) {k : ℕ} (hβ : ∀ j < k, beta r j ≠ 0) :
    IsUnit (symmToeplitz k r).det := by
  rw [det_symmToeplitz hr hβ]
  exact (prod_ne_zero_iff.mpr fun j hj => hβ j (mem_range.mp hj)).isUnit

/-- **The last column of `T_{m+1}⁻¹`** ([golub2013matrix] (4.7.4)): if `r 0 = 1` and no `β_j`,
`j ≤ m`, vanishes, the last column of `(symmToeplitz (m + 1) r)⁻¹` is `(v, γ)` with
`γ = 1 / β_m` and `v = γ ℰ_m y^{(m)}` (and so is its last row, by symmetry). -/
theorem inv_symmToeplitz_last (hr : r 0 = 1) {m : ℕ} (hβ : ∀ j < m + 1, beta r j ≠ 0) :
    (fun i => (symmToeplitz (m + 1) r)⁻¹ i (Fin.last m)) =
      Fin.snoc (α := fun _ => K) (lastCol r m) (gamma r m) := by
  have hdet := isUnit_det_symmToeplitz hr hβ
  have hw : Fin.snoc (α := fun _ => K) (lastCol r m) (gamma r m) =
      fun i : Fin (m + 1) => gamma r m * revSol r m i := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [Fin.snoc_castSucc, lastCol, Pi.smul_apply, exchange_mulVec_apply, smul_eq_mul,
        revSol, Fin.val_castSucc, i.isLt, ite_true, Fin.val_rev]
      congr 2
      omega
  have hTw : symmToeplitz (m + 1) r *ᵥ Fin.snoc (α := fun _ => K) (lastCol r m) (gamma r m) =
      Pi.single (Fin.last m) 1 := by
    funext i
    rw [hw, symmToeplitz_mulVec_apply (v := fun j => gamma r m * revSol r m j)]
    rw [show (∑ j ∈ range (m + 1), r ((i : ℤ) - j).natAbs * (gamma r m * revSol r m j)) =
        gamma r m * ∑ j ∈ range (m + 1), r ((i : ℤ) - j).natAbs * revSol r m j by
      rw [mul_sum]; exact sum_congr rfl fun j _ => mul_left_comm _ _ _]
    rw [sum_symmToeplitz_revSol hr (fun j hj => hβ j (by omega)) i (Fin.is_le i),
      Pi.single_apply]
    by_cases h : i = Fin.last m
    · rw [ite_eq_left (by rw [h, Fin.val_last]), ite_eq_left h, gamma, one_div,
        inv_mul_cancel₀ (hβ m (by omega))]
    · rw [ite_eq_right (fun h' => h (Fin.ext (by rw [Fin.val_last]; exact h'))), ite_eq_right h,
        mul_zero]
  calc (fun i => (symmToeplitz (m + 1) r)⁻¹ i (Fin.last m))
      = (symmToeplitz (m + 1) r)⁻¹ *ᵥ Pi.single (Fin.last m) 1 := by
        rw [mulVec_single_one]; rfl
    _ = (symmToeplitz (m + 1) r)⁻¹ *ᵥ (symmToeplitz (m + 1) r *ᵥ
          Fin.snoc (α := fun _ => K) (lastCol r m) (gamma r m)) := by rw [hTw]
    _ = _ := by rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- **Trench's formula for the leading block of `T_{m+1}⁻¹`** ([golub2013matrix] (4.7.4),
`B = A⁻¹ + v vᵀ / γ`): under the hypotheses of `Trench.inv_symmToeplitz_last`, the leading
`m × m` block of `(symmToeplitz (m + 1) r)⁻¹` is `(symmToeplitz m r)⁻¹ + γ⁻¹ v vᵀ`. -/
theorem inv_symmToeplitz_eq (hr : r 0 = 1) {m : ℕ} (hβ : ∀ j < m + 1, beta r j ≠ 0) :
    (symmToeplitz (m + 1) r)⁻¹.submatrix Fin.castSucc Fin.castSucc =
      (symmToeplitz m r)⁻¹ + (gamma r m)⁻¹ • vecMulVec (lastCol r m) (lastCol r m) := by
  have hdetT := isUnit_det_symmToeplitz hr hβ
  have hdetA := isUnit_det_symmToeplitz hr fun j (hj : j < m) => hβ j (by omega)
  have hγ : gamma r m ≠ 0 := one_div_ne_zero (hβ m (by omega))
  have hBsymm : ∀ i j, (symmToeplitz (m + 1) r)⁻¹ i j = (symmToeplitz (m + 1) r)⁻¹ j i := by
    intro i j
    have : ((symmToeplitz (m + 1) r)⁻¹)ᵀ = (symmToeplitz (m + 1) r)⁻¹ := by
      rw [transpose_nonsing_inv, (symmToeplitz_isSymm (m + 1) r).eq]
    exact congrFun (congrFun this j) i
  have hlast : ∀ j : Fin m,
      (symmToeplitz (m + 1) r)⁻¹ (Fin.last m) (Fin.castSucc j) = lastCol r m j := by
    intro j
    rw [hBsymm]
    simpa using congrFun (inv_symmToeplitz_last hr hβ) (Fin.castSucc j)
  have eT : ∀ a b : Fin m,
      symmToeplitz (m + 1) r (Fin.castSucc a) (Fin.castSucc b) = symmToeplitz m r a b :=
    fun _ _ => rfl
  -- `A B₁₁ = I − (ℰ r') vᵀ`, from the leading block of `T B = I`
  have hAB : symmToeplitz m r * (symmToeplitz (m + 1) r)⁻¹.submatrix Fin.castSucc Fin.castSucc =
      1 - vecMulVec (exchange m *ᵥ fun i : Fin m => r ((i : ℕ) + 1)) (lastCol r m) := by
    ext i j
    have hTB := congrFun (congrFun (mul_nonsing_inv _ hdetT) (Fin.castSucc i)) (Fin.castSucc j)
    have e2 : symmToeplitz (m + 1) r (Fin.castSucc i) (Fin.last m) = r ((Fin.rev i : ℕ) + 1) := by
      rw [symmToeplitz_apply, Fin.val_castSucc, Fin.val_last, Fin.val_rev]
      congr 1
      omega
    rw [mul_apply, Fin.sum_univ_castSucc, hlast, e2] at hTB
    simp only [Matrix.one_apply, Fin.castSucc_inj, eT] at hTB
    rw [Matrix.sub_apply, vecMulVec_apply, exchange_mulVec_apply, mul_apply, Matrix.one_apply,
      ← hTB]
    simp only [submatrix_apply]
    ring
  have hy : symmToeplitz m r *ᵥ (fun i : Fin m => sol r m i) =
      -(fun i : Fin m => r ((i : ℕ) + 1)) := by
    rw [symmToeplitz_mulVec_sol hr fun j hj => hβ j (by omega)]
    rfl
  have hEy : symmToeplitz m r *ᵥ (exchange m *ᵥ fun i : Fin m => sol r m i) =
      -(exchange m *ᵥ fun i : Fin m => r ((i : ℕ) + 1)) := by
    rw [mulVec_mulVec, ← (exchange_mul_symmToeplitz m r).1, ← mulVec_mulVec, hy, mulVec_neg]
  have hAinv : (symmToeplitz m r)⁻¹ *ᵥ (exchange m *ᵥ fun i : Fin m => r ((i : ℕ) + 1)) =
      -(exchange m *ᵥ fun i : Fin m => sol r m i) := by
    have : (exchange m *ᵥ fun i : Fin m => r ((i : ℕ) + 1)) =
        symmToeplitz m r *ᵥ (-(exchange m *ᵥ fun i : Fin m => sol r m i)) := by
      rw [mulVec_neg, hEy, neg_neg]
    rw [this, mulVec_mulVec, nonsing_inv_mul _ hdetA, one_mulVec]
  have hB11 : (symmToeplitz (m + 1) r)⁻¹.submatrix Fin.castSucc Fin.castSucc =
      (symmToeplitz m r)⁻¹ *
        (symmToeplitz m r * (symmToeplitz (m + 1) r)⁻¹.submatrix Fin.castSucc Fin.castSucc) := by
    rw [← Matrix.mul_assoc, nonsing_inv_mul _ hdetA, Matrix.one_mul]
  have hvm : ∀ u : Fin m → K, (symmToeplitz m r)⁻¹ * vecMulVec u (lastCol r m) =
      vecMulVec ((symmToeplitz m r)⁻¹ *ᵥ u) (lastCol r m) := by
    intro u
    ext i j
    simp only [mul_apply, vecMulVec_apply, mulVec, dotProduct, sum_mul, mul_assoc]
  have hv : (exchange m *ᵥ fun i : Fin m => sol r m i) = (gamma r m)⁻¹ • lastCol r m := by
    rw [lastCol, smul_smul, inv_mul_cancel₀ hγ, one_smul]
  rw [hB11, hAB, Matrix.mul_sub, Matrix.mul_one, hvm, hAinv, hv]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- **(4.7.5)** ([golub2013matrix] §4.7.4): the entries of `T_{m+1}⁻¹` above its last row are
determined by those further down its persymmetric image,
`b_ij = b_{rev j, rev i} + (v_i v_j − v_{rev j} v_{rev i}) / γ` (0-based: the book's
`b_{n−j, n−i}` is `B (rev j) (rev i)`). -/
theorem inv_symmToeplitz_apply_succ (hr : r 0 = 1) {m : ℕ} (hβ : ∀ j < m + 1, beta r j ≠ 0)
    (i j : Fin m) :
    (symmToeplitz (m + 1) r)⁻¹ (Fin.castSucc i) (Fin.castSucc j) =
      (symmToeplitz (m + 1) r)⁻¹ (Fin.castSucc (Fin.rev j)) (Fin.castSucc (Fin.rev i)) +
        (lastCol r m i * lastCol r m j - lastCol r m (Fin.rev j) * lastCol r m (Fin.rev i)) /
          gamma r m := by
  have h := inv_symmToeplitz_eq hr hβ
  have e : ∀ a b : Fin m, (symmToeplitz (m + 1) r)⁻¹ (Fin.castSucc a) (Fin.castSucc b) =
      (symmToeplitz m r)⁻¹ a b + (gamma r m)⁻¹ * (lastCol r m a * lastCol r m b) := by
    intro a b
    have := congrFun (congrFun h a) b
    simpa [vecMulVec_apply] using this
  rw [e, e, (symmToeplitz_isPersymmetric m r).inv i j, div_eq_mul_inv]
  ring

end Trench

namespace Durbin

open Trench

variable {r : ℕ → ℝ}

/-- **The lower bounds of (4.7.6)** ([golub2013matrix] §4.7.6): for a positive definite
`T_{m+1} = symmToeplitz (m + 1) r`, `r 0 = 1`, with reflection coefficients `α_j`,
`max (1 / ∏_{j<m} (1 − α_j²)) (1 / ∏_{j<m} (1 − α_j)) ≤ ‖T_{m+1}⁻¹‖₁`. The last column of
`T_{m+1}⁻¹` is `γ (ℰ y, 1)` with `γ = 1 / ∏ (1 − α_j²)`, and its absolute sum is at least `γ` and
at least `γ |1 + ∑ y_i| = γ ∏ (1 + α_j)`. The book prints both bounds with an extra factor
`1 / (n − 1)`; the statement here is stronger. -/
theorem inv_beta_le_lpOpNorm_one_inv (hr : r 0 = 1) {m : ℕ}
    (hT : (symmToeplitz (m + 1) r).PosDef) :
    max (1 / ∏ j ∈ range m, (1 - alpha r j ^ 2)) (1 / ∏ j ∈ range m, (1 - alpha r j)) ≤
      lpOpNorm 1 (symmToeplitz (m + 1) r)⁻¹ := by
  have hβpos := beta_pos hr hT
  have hβ : ∀ j < m + 1, beta r j ≠ 0 := fun j hj => (hβpos j hj).ne'
  have hα : ∀ j < m, |alpha r j| < 1 := fun j hj => abs_alpha_lt_one hr hT (by omega)
  have hcol := sum_norm_le_lpOpNorm_one (symmToeplitz (m + 1) r)⁻¹ (Fin.last m)
  rw [Fin.sum_univ_castSucc] at hcol
  have e : ∀ i, (symmToeplitz (m + 1) r)⁻¹ i (Fin.last m) =
      Fin.snoc (α := fun _ => ℝ) (lastCol r m) (gamma r m) i :=
    fun i => congrFun (inv_symmToeplitz_last hr hβ) i
  simp only [e, Fin.snoc_castSucc, Fin.snoc_last, Real.norm_eq_abs] at hcol
  have hγpos : 0 < gamma r m := one_div_pos.mpr (hβpos m (by omega))
  have hsum : ∑ i : Fin m, |lastCol r m i| = gamma r m * ∑ i ∈ range m, |sol r m i| := by
    simp only [lastCol, Pi.smul_apply, exchange_mulVec_apply, smul_eq_mul, abs_mul,
      abs_of_pos hγpos, ← mul_sum]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => |sol r m i|) m]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
  rw [hsum, abs_of_pos hγpos] at hcol
  have hSnn : 0 ≤ ∑ i ∈ range m, |sol r m i| := sum_nonneg fun i _ => abs_nonneg _
  have hγ : gamma r m = 1 / ∏ j ∈ range m, (1 - alpha r j ^ 2) := by
    rw [gamma, beta_eq_prod fun j hj => hβ j (by omega)]
  have hS : ∏ j ∈ range m, (1 + alpha r j) ≤ 1 + ∑ i ∈ range m, |sol r m i| := by
    rw [← sum_sol_add_one]
    exact (add_le_add_iff_left 1).mpr ((le_abs_self _).trans (abs_sum_le_sum_abs _ _))
  refine max_le ?_ ?_
  · rw [← hγ]
    nlinarith
  · have hQ : 0 < ∏ j ∈ range m, (1 + alpha r j) :=
      prod_pos fun j hj => by have := hα j (mem_range.mp hj); rw [abs_lt] at this; linarith
    have hP : 0 < ∏ j ∈ range m, (1 - alpha r j) :=
      prod_pos fun j hj => by have := hα j (mem_range.mp hj); rw [abs_lt] at this; linarith
    have hprod : ∏ j ∈ range m, (1 - alpha r j ^ 2) =
        (∏ j ∈ range m, (1 - alpha r j)) * ∏ j ∈ range m, (1 + alpha r j) := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun j _ => by ring
    have h1 : 1 / ∏ j ∈ range m, (1 - alpha r j) = gamma r m * ∏ j ∈ range m, (1 + alpha r j) := by
      rw [hγ, hprod]
      field_simp
    rw [h1]
    nlinarith

end Durbin

/-! ### Cybenko's upper bound -/

namespace Durbin

variable {K : Type*} [Field K] {r : ℕ → K}

/-- The coefficients `(1, y^{(k)}_0, …, y^{(k)}_{k−1})` of the Szegő polynomial `p_k`, of which
`Durbin.revSol r k` is the reversal `p_k^*`. -/
def fwdSol (r : ℕ → K) (k m : ℕ) : K := if m = 0 then 1 else sol r k (m - 1)

/-- **The Szegő recursion** `p_{k+1}^* = z p_k^* + α_k p_k`, coefficientwise. -/
theorem revSol_succ (k l : ℕ) :
    revSol r (k + 1) l = (if l = 0 then 0 else revSol r k (l - 1)) + alpha r k * fwdSol r k l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · rw [revSol, ite_eq_left (Nat.succ_pos k), show k + 1 - 1 - 0 = k by omega, sol_succ_self,
      fwdSol, ite_eq_left rfl, ite_eq_left rfl]
    ring
  rw [ite_eq_right hl.ne', fwdSol, ite_eq_right hl.ne']
  rcases lt_trichotomy l (k + 1) with h | rfl | h
  · rw [revSol, ite_eq_left h, sol_succ, ite_eq_left (by omega), revSol, ite_eq_left (by omega),
      show k - 1 - (k + 1 - 1 - l) = l - 1 by omega, show k + 1 - 1 - l = k - 1 - (l - 1) by omega]
  · rw [revSol_self, show k + 1 - 1 = k by omega, revSol_self, sol_of_le r le_rfl, mul_zero,
      add_zero]
  · rw [revSol_of_lt h, revSol_of_lt (by omega), sol_of_le r (by omega), mul_zero, add_zero]

/-- The coefficients of `p_k` vanish beyond degree `k`. -/
theorem fwdSol_of_lt {k m : ℕ} (h : k < m) : fwdSol r k m = 0 := by
  rw [fwdSol, ite_eq_right (by omega), sol_of_le r (by omega)]

end Durbin

namespace Durbin

variable {r : ℕ → ℝ}

/-- The `ℓ¹` norm of `p_k`: `∑_m |[z^m] p_k| = 1 + ∑_i |y^{(k)}_i|`, over any range containing the
degree. -/
theorem sum_abs_fwdSol_le (k l : ℕ) :
    ∑ m ∈ range (l + 1), |fwdSol r k m| ≤ ∏ j ∈ range k, (1 + |alpha r j|) := by
  calc ∑ m ∈ range (l + 1), |fwdSol r k m|
      ≤ ∑ m ∈ range (l + k + 1), |fwdSol r k m| :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun _ _ _ => abs_nonneg _
    _ = ∑ m ∈ range (k + 1), |fwdSol r k m| := by
        refine (sum_subset (range_subset_range.mpr (by omega)) fun m _ hm => ?_).symm
        rw [fwdSol_of_lt (by simp only [mem_range] at hm; omega), abs_zero]
    _ = 1 + ∑ i ∈ range k, |sol r k i| := by
        rw [sum_range_succ', fwdSol, ite_eq_left rfl, abs_one, add_comm]
        congr 1
    _ ≤ _ := one_add_sum_abs_sol_le k

/-- The row sums of the matrix of reversed solutions, in the form the induction needs. -/
private theorem sum_abs_revSol_le_aux (N l : ℕ) :
    ∑ k ∈ range (N + 1), |revSol r k l| ≤
      1 + ∑ j ∈ range N, |alpha r j| * ∑ m ∈ range (l + 1), |fwdSol r j m| := by
  induction N generalizing l with
  | zero =>
    rw [sum_range_one, range_zero, sum_empty, add_zero, revSol]
    split_ifs <;> simp
  | succ N ih =>
    rw [sum_range_succ']
    have hk : ∀ k, |revSol r (k + 1) l| ≤
        |if l = 0 then 0 else revSol r k (l - 1)| + |alpha r k| * |fwdSol r k l| := fun k => by
      rw [revSol_succ, ← abs_mul]
      exact abs_add_le _ _
    have hsum := sum_le_sum fun k (_ : k ∈ range (N + 1)) => hk k
    rw [sum_add_distrib] at hsum
    have hnn : ∀ j, 0 ≤ |alpha r j| * ∑ m ∈ range (l + 1), |fwdSol r j m| :=
      fun j => mul_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp only [ite_true, abs_zero, sum_const_zero, zero_add] at hsum
      rw [revSol_self]
      simp only [zero_add, sum_range_one, abs_one] at hsum ⊢
      linarith
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at hsum
      rw [revSol_of_lt (by omega), abs_zero, add_zero]
      have ih' := ih l'
      have hsplit : ∑ j ∈ range (N + 1), |alpha r j| * ∑ m ∈ range (l' + 1 + 1), |fwdSol r j m| =
          ∑ j ∈ range (N + 1), |alpha r j| * ∑ m ∈ range (l' + 1), |fwdSol r j m| +
            ∑ j ∈ range (N + 1), |alpha r j| * |fwdSol r j (l' + 1)| := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun j _ => by rw [sum_range_succ, mul_add]
      have hmono : ∑ j ∈ range N, |alpha r j| * ∑ m ∈ range (l' + 1), |fwdSol r j m| ≤
          ∑ j ∈ range (N + 1), |alpha r j| * ∑ m ∈ range (l' + 1), |fwdSol r j m| :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun j _ _ =>
          mul_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)
      rw [hsplit]
      linarith

/-- `1 + ∑_{j<N} |α_j| ∏_{i<j} (1 + |α_i|) = ∏_{j<N} (1 + |α_j|)`. -/
private theorem one_add_sum_mul_prod (a : ℕ → ℝ) (N : ℕ) :
    1 + ∑ j ∈ range N, a j * ∏ i ∈ range j, (1 + a i) = ∏ j ∈ range N, (1 + a j) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, prod_range_succ, ← add_assoc, ih]; ring

/-- **The row sums of `U`** (the key estimate behind Cybenko's bound): the entries `l` of the
reversed solutions `(ℰ_k y^{(k)}, 1)`, `k ≤ N`, have absolute sum at most `∏_{j<N} (1 + |α_j|)`. -/
theorem sum_abs_revSol_le (N l : ℕ) :
    ∑ k ∈ range (N + 1), |revSol r k l| ≤ ∏ j ∈ range N, (1 + |alpha r j|) := by
  refine (sum_abs_revSol_le_aux N l).trans ?_
  rw [← one_add_sum_mul_prod (fun j => |alpha r j|)]
  gcongr with j
  exact sum_abs_fwdSol_le j l

/-- The column sums of `U`: `1 + ∑_i |y^{(k)}_i| ≤ ∏_{j<k} (1 + |α_j|)`, read on `revSol`. -/
private theorem sum_abs_revSol_col_le {k n : ℕ} (hk : k < n) :
    ∑ i ∈ range n, |revSol r k i| ≤ ∏ j ∈ range k, (1 + |alpha r j|) := by
  have h1 : ∑ i ∈ range n, |revSol r k i| = ∑ i ∈ range (k + 1), |revSol r k i| := by
    refine (sum_subset (range_subset_range.mpr (by omega)) fun i _ hi => ?_).symm
    rw [revSol_of_lt (by simp only [mem_range] at hi; omega), abs_zero]
  rw [h1, sum_range_succ, revSol_self, abs_one]
  have h2 : ∑ i ∈ range k, |revSol r k i| = ∑ i ∈ range k, |sol r k i| := by
    rw [← sum_range_reflect (fun i => |sol r k i|) k]
    exact sum_congr rfl fun i hi => by rw [revSol, ite_eq_left (mem_range.mp hi)]
  rw [h2, add_comm]
  exact one_add_sum_abs_sol_le k

/-- A `1`-norm bound from a bound on every column sum. -/
private theorem lpOpNorm_one_le_of_forall_sum_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ c, ∑ k, ‖M k c‖ ≤ C) : lpOpNorm 1 M ≤ C := by
  rw [lpOpNorm_one_eq_sup_sum_norm]
  have hle : (univ.sup fun j => ∑ i, ‖M i j‖₊) ≤ ⟨C, hC⟩ := Finset.sup_le fun c _ =>
    NNReal.coe_le_coe.mp (show ((∑ i, ‖M i c‖₊ : NNReal) : ℝ) ≤ C by push_cast; exact h c)
  exact NNReal.coe_le_coe.mpr hle

/-- `U` is unit upper triangular, so `det U = 1`. -/
theorem det_unitUpper {K : Type*} [Field K] (r : ℕ → K) (n : ℕ) : (unitUpper r n).det = 1 := by
  rw [det_of_isUpperTriangular]
  · simp [unitUpper]
  · intro i k hik
    exact revSol_of_lt hik

/-- **`T_n⁻¹ = U diag(β)⁻¹ Uᵀ`** ([golub2013matrix] §4.7.6, P4.7.2), from
`Durbin.transpose_mul_mul_eq_diagonal`, over any field. -/
theorem inv_symmToeplitz_eq_mul {K : Type*} [Field K] {r : ℕ → K} (hr : r 0 = 1) {n : ℕ}
    (hβ : ∀ j < n, beta r j ≠ 0) :
    (symmToeplitz n r)⁻¹ =
      unitUpper r n * diagonal (fun k : Fin n => (beta r k)⁻¹) * (unitUpper r n)ᵀ := by
  have hUTU := transpose_mul_mul_eq_diagonal hr (n := n) fun j hj => hβ j (by omega)
  have hdetUt : IsUnit (unitUpper r n)ᵀ.det := by
    rw [det_transpose, det_unitUpper]; exact isUnit_one
  have hTU : symmToeplitz n r * unitUpper r n =
      ((unitUpper r n)ᵀ)⁻¹ * diagonal (fun k : Fin n => beta r k) := by
    rw [← hUTU]
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hdetUt, Matrix.one_mul]
  have hD : (diagonal fun k : Fin n => beta r k) *
      diagonal (fun k : Fin n => (beta r k)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hβ k k.isLt)
  refine inv_eq_right_inv ?_
  calc symmToeplitz n r * (unitUpper r n * diagonal (fun k : Fin n => (beta r k)⁻¹) *
        (unitUpper r n)ᵀ)
      = (symmToeplitz n r * unitUpper r n) * diagonal (fun k : Fin n => (beta r k)⁻¹) *
          (unitUpper r n)ᵀ := by simp only [Matrix.mul_assoc]
    _ = ((unitUpper r n)ᵀ)⁻¹ * ((diagonal fun k : Fin n => beta r k) *
          diagonal (fun k : Fin n => (beta r k)⁻¹)) * (unitUpper r n)ᵀ := by
        rw [hTU]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hD, Matrix.mul_one, nonsing_inv_mul _ hdetUt]

/-- **Cybenko's upper bound (4.7.6)** ([golub2013matrix] §4.7.6, quoted there without proof; Cybenko
1980): for a positive definite `T_{m+1} = symmToeplitz (m + 1) r`, `r 0 = 1`, with reflection
coefficients `α_j`, `‖T_{m+1}⁻¹‖₁ ≤ ∏_{j<m} (1 + |α_j|) / (1 − |α_j|)`. Through
`T⁻¹ = U diag(β)⁻¹ Uᵀ` (`Durbin.inv_symmToeplitz_eq_mul`): the columns of `U` have absolute
sums at most `∏_{j<k} (1 + |α_j|)` and its rows at most `∏_{j<m} (1 + |α_j|)`
(`Durbin.sum_abs_revSol_le`, from the Szegő recursion `Durbin.revSol_succ`), and
`∏_{j<k} (1 + |α_j|) / β_k ≤ ∏_{j<m} 1 / (1 − |α_j|)`. -/
theorem lpOpNorm_one_inv_le (hr : r 0 = 1) {m : ℕ} (hT : (symmToeplitz (m + 1) r).PosDef) :
    lpOpNorm 1 (symmToeplitz (m + 1) r)⁻¹ ≤
      ∏ j ∈ range m, (1 + |alpha r j|) / (1 - |alpha r j|) := by
  have hβpos := beta_pos hr hT
  have hβ : ∀ j < m + 1, beta r j ≠ 0 := fun j hj => (hβpos j hj).ne'
  have hα : ∀ j < m, |alpha r j| < 1 := fun j hj => abs_alpha_lt_one hr hT (by omega)
  have hpos : ∀ j < m, 0 < 1 - |alpha r j| := fun j hj => by linarith [hα j hj]
  have hinv := inv_symmToeplitz_eq_mul hr hβ
  -- the constants
  have hQk : ∀ k ≤ m, (∏ j ∈ range k, (1 + |alpha r j|)) * (beta r k)⁻¹ ≤
      ∏ j ∈ range m, (1 - |alpha r j|)⁻¹ := by
    intro k hk
    have hβk : beta r k =
        (∏ j ∈ range k, (1 - |alpha r j|)) * ∏ j ∈ range k, (1 + |alpha r j|) := by
      rw [beta_eq_prod fun j hj => hβ j (by omega), ← prod_mul_distrib]
      exact prod_congr rfl fun j _ => by rw [← sq_abs]; ring
    have hPk : 0 < ∏ j ∈ range k, (1 + |alpha r j|) := prod_pos fun j _ => by positivity
    have hPM : (∏ j ∈ range k, (1 + |alpha r j|)) *
        ((∏ j ∈ range k, (1 - |alpha r j|)) * ∏ j ∈ range k, (1 + |alpha r j|))⁻¹ =
          (∏ j ∈ range k, (1 - |alpha r j|))⁻¹ := by
      rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hPk.ne', mul_one]
    rw [hβk, hPM, ← prod_inv_distrib]
    refine prod_le_prod_of_subset_of_one_le₀ (range_subset_range.mpr hk)
      (fun j hj => (inv_pos.mpr (hpos j (by have := mem_range.mp hj; omega))).le)
      fun j hj _ => ?_
    have := hpos j (mem_range.mp hj)
    exact (one_le_inv₀ this).mpr (by linarith [abs_nonneg (alpha r j)])
  have hQ : 0 ≤ ∏ j ∈ range m, (1 - |alpha r j|)⁻¹ :=
    prod_nonneg fun j hj => (inv_pos.mpr (hpos j (mem_range.mp hj))).le
  have hfinal : (∏ j ∈ range m, (1 - |alpha r j|)⁻¹) * ∏ j ∈ range m, (1 + |alpha r j|) =
      ∏ j ∈ range m, (1 + |alpha r j|) / (1 - |alpha r j|) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun j _ => by rw [div_eq_mul_inv, mul_comm]
  rw [← hfinal]
  refine lpOpNorm_one_le_of_forall_sum_le (mul_nonneg hQ (prod_nonneg fun j _ => by positivity))
    fun l => ?_
  -- the column `l` of `T⁻¹`
  have hentry : ∀ i, ‖(symmToeplitz (m + 1) r)⁻¹ i l‖ ≤
      ∑ k : Fin (m + 1), |revSol r k i| * (beta r k)⁻¹ * |revSol r k l| := by
    intro i
    rw [hinv, mul_apply, Real.norm_eq_abs]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
    rw [mul_diagonal, transpose_apply, abs_mul, abs_mul, abs_inv, abs_of_pos (hβpos k k.isLt)]
    rfl
  calc ∑ i, ‖(symmToeplitz (m + 1) r)⁻¹ i l‖
      ≤ ∑ i : Fin (m + 1), ∑ k : Fin (m + 1), |revSol r k i| * (beta r k)⁻¹ * |revSol r k l| :=
        sum_le_sum fun i _ => hentry i
    _ = ∑ k : Fin (m + 1), (∑ i : Fin (m + 1), |revSol r k i|) * (beta r k)⁻¹ *
          |revSol r k l| := by
        rw [sum_comm]
        exact sum_congr rfl fun k _ => by rw [sum_mul, sum_mul]
    _ ≤ ∑ k : Fin (m + 1), (∏ j ∈ range m, (1 - |alpha r j|)⁻¹) * |revSol r k l| := by
        refine sum_le_sum fun k _ => ?_
        have hcol : ∑ i : Fin (m + 1), |revSol r k i| ≤ ∏ j ∈ range k, (1 + |alpha r j|) := by
          rw [Fin.sum_univ_eq_sum_range (fun i => |revSol r k i|) (m + 1)]
          exact sum_abs_revSol_col_le k.isLt
        have hβinv : 0 ≤ (beta r k)⁻¹ := (inv_pos.mpr (hβpos k k.isLt)).le
        calc (∑ i : Fin (m + 1), |revSol r k i|) * (beta r k)⁻¹ * |revSol r k l|
            ≤ (∏ j ∈ range k, (1 + |alpha r j|)) * (beta r k)⁻¹ * |revSol r k l| :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcol hβinv) (abs_nonneg _)
          _ ≤ (∏ j ∈ range m, (1 - |alpha r j|)⁻¹) * |revSol r k l| :=
              mul_le_mul_of_nonneg_right (hQk k (by have := k.isLt; omega)) (abs_nonneg _)
    _ = (∏ j ∈ range m, (1 - |alpha r j|)⁻¹) * ∑ k ∈ range (m + 1), |revSol r k l| := by
        rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun k => |revSol r k l|) (m + 1)]
    _ ≤ (∏ j ∈ range m, (1 - |alpha r j|)⁻¹) * ∏ j ∈ range m, (1 + |alpha r j|) :=
        mul_le_mul_of_nonneg_left (sum_abs_revSol_le m l) hQ

end Durbin

namespace Durbin

/-- **Positive definiteness of a symmetric Toeplitz matrix through Durbin's recurrence**
([golub2013matrix] §4.7.3 and §4.7.7): with `r 0 = 1`, `T_n` is positive definite iff
`β_k > 0` for every `k < n` — the congruence `Uᵀ T_n U = diag(β)` with `U` unit upper
triangular. -/
theorem posDef_symmToeplitz_iff {r : ℕ → ℝ} (hr : r 0 = 1) {n : ℕ} :
    (symmToeplitz n r).PosDef ↔ ∀ k < n, 0 < beta r k := by
  refine ⟨beta_pos hr, fun h => ?_⟩
  have hU : IsUnit (unitUpper r n) :=
    (isUnit_iff_isUnit_det _).mpr (by rw [det_unitUpper]; exact isUnit_one)
  rw [← Matrix.IsUnit.posDef_star_left_conjugate_iff hU, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial,
    transpose_mul_mul_eq_diagonal hr fun j hj => (h j (by omega)).ne', posDef_diagonal_iff]
  exact fun k => h k k.isLt

end Durbin
