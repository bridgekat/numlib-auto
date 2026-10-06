import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Int.Log
import Numlib.Analysis.Matrix.Function.Exp
import Numlib.Analysis.Matrix.Function.Pade
import Numlib.Analysis.Matrix.Function.Sign
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.Schur
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter03.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section09
import NumlibSurface.GolubVanLoan.Chapter09.Section02

/-!
# Golub–Van Loan §9.3: the matrix exponential

Surface file for [golub2013matrix] §9.3: the Padé approximants of the exponential and the
remainder (9.3.1), the Moler–Van Loan backward error of scaling and squaring, Algorithm 9.3.1
(scaling and squaring, `scalingSquaring` with exponent offset `1`) with its exact semantics and the
book's backward-error claim, the corrected variant `algorithm_9_3_1_corrected` (offset `2`) whose
backward-error claim holds unconditionally, the even/odd
evaluation of `N_qq`, `D_qq`; the ODE characterization and the perturbation theory of `e^{At}`
(the variation-of-constants identity, (9.3.2) with the spectral abscissa (9.3.3), the relative
bound, Van Loan's condition number `ν(A, t)`), normal matrices ((9.3.4)), the `2 × 2` example
(9.3.5), the pseudospectral lower bound (9.3.6), and the normal case of §9.3.4.

## Conventions

`e^{At}` is Mathlib's `NormedSpace.exp (t • A)`, which needs no norm on matrices. `A` is real,
`Matrix (Fin n) (Fin n) ℝ`, where the book is real (§9.3.1, the start of §9.3.2), and complex where
the book uses the Schur decomposition `Qᴴ A Q = diag(λ_i) + N` (`Q ∈ unitaryGroup`, `star Q = Qᴴ`).
The `∞`-norm of §9.3.1 is the scoped `Matrix.Norms.Operator`, the `2`-norm of §9.3.2–§9.3.4 the
scoped `Matrix.Norms.L2Operator`; integrals of matrix-valued functions are taken in whichever of
them is open (all norms give the same integral). The Padé functions are the backbone's
`Pade.expNum ℝ p q = N_pq`, `Pade.expDen ℝ p q = D_pq` and `Pade.expApprox ℝ p q A = R_pq(A)`;
`ε(p, q)` is `Pade.errorBound p q`; Van Loan's `ν(A, t)` is `NormedSpace.expCondNumber A t`, the
operator norm of the Fréchet derivative `E ↦ ∫₀ᵗ e^{A(t-s)} E e^{As} ds` times `‖A‖₂/‖e^{At}‖₂`,
which is the book's `max_{‖E‖₂ ≤ 1}`.

## Sources

`Numlib/Analysis/Matrix/Function/{Pade,Exp}`, `Numlib/Analysis/Normed/Algebra/Exponential`
(`NormedSpace.exp_smul_add_sub_exp_smul`, `NormedSpace.eq_exp_smul_of_hasDerivAt`,
`NormedSpace.expCondNumber`, `norm_resolvent_le_of_norm_exp_smul_le`),
`Numlib/Analysis/Normed/Algebra/SpectralRadius` (`spectralAbscissa`),
`Numlib/LinearAlgebra/Matrix/Schur` (`Matrix.isStarNormal_iff_strictUpper_eq_zero`); chapter 1's
Algorithm 1.1.5 and chapter 3's solve after Gaussian elimination with partial pivoting
(`GolubVanLoan.Chapter03.solveMultipleRHS`, (3.4.12)) inside Algorithm 9.3.1, which follows the
algorithm conventions of `NumlibSurface.GolubVanLoan`; chapter 7's pseudospectra
(`GolubVanLoan.Chapter07.pseudospectrum`, `pseudospectralAbscissa`, (7.9.6)) for (9.3.6).

## Not formalized

The flop counts, Figure 9.3.1 and `α_{.01}(A)/.01 ≈ 216`, and the heuristic claims of §9.3.2 ("a
matrix `E` for which … `≈`") and §9.3.4 (the rounding estimate `γ`, "numerical experiments
suggest").

## Errata

(9.3.2) prints `e^{α(A) t M_S(t)}` for `e^{α(A) t} M_S(t)`; §9.3.2's "equality holding for all
nonnegative `t` if and only if the matrix `A` is normal" is false in the "only if" direction
(`expCondNumber_eq_iff_counterexample`); (9.3.6) cites "(7.8.8)" for (7.9.8); Algorithm 9.3.1's
`j = max{0, 1 + ⌊log₂ ‖A‖_∞⌋}` only guarantees `‖A/2^j‖_∞ < 1`, not the `≤ 1/2` that the
Moler–Van Loan bound needs (`2 + ⌊log₂ ‖A‖_∞⌋` does: `algorithm_9_3_1_corrected`).
-/

open Polynomial Finset NormedSpace
open scoped Nat

namespace GolubVanLoan.Chapter09

variable {n : ℕ}

/-! ### §9.3.1 A Padé approximation method -/

/-- **The Padé functions** of §9.3.1: `R_pq(z) = D_pq(z)⁻¹ N_pq(z)` with
`N_pq(z) = ∑_{k=0}^{p} (p+q-k)! p! / ((p+q)! k! (p-k)!) zᵏ` and
`D_pq(z) = ∑_{k=0}^{q} (p+q-k)! q! / ((p+q)! k! (q-k)!) (-z)ᵏ`; and
`R_p0(z) = 1 + z + ⋯ + z^p/p!` is the order-`p` Taylor polynomial. -/
theorem pade_def (p q : ℕ) :
    (∀ k, (Pade.expNum ℝ p q).coeff k = if k ≤ p then
      (((p + q - k)! * p ! : ℕ) / ((p + q)! * k ! * (p - k)! : ℕ) : ℝ) else 0) ∧
    (∀ k, (Pade.expDen ℝ p q).coeff k = if k ≤ q then
      (-1) ^ k * (((p + q - k)! * q ! : ℕ) / ((p + q)! * k ! * (q - k)! : ℕ) : ℝ) else 0) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, Pade.expApprox ℝ p q A =
      (aeval A (Pade.expDen ℝ p q))⁻¹ * aeval A (Pade.expNum ℝ p q)) ∧
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      Pade.expApprox ℝ p 0 A = ∑ k ∈ range (p + 1), ((k ! : ℝ)⁻¹) • A ^ k := by
  refine ⟨Pade.coeff_expNum p q, Pade.coeff_expDen p q, fun A => ?_, fun A => ?_⟩
  · rw [Pade.expApprox, Matrix.nonsing_inv_eq_ringInverse]
  · rw [Pade.expApprox, Pade.expDen_zero_right, Pade.expNum_zero_right, map_one,
      Ring.inverse_one, one_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]

section Infinity

open scoped Matrix.Norms.Operator

/-- **(9.3.1)**: if `D_pq(A)` is nonsingular, then
`e^A = R_pq(A) + (-1)^q/(p+q)! A^{p+q+1} D_pq(A)⁻¹ ∫₀¹ u^p (1-u)^q e^{A(1-u)} du`. -/
theorem equation_9_3_1 (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : IsUnit (aeval A (Pade.expDen ℝ p q))) :
    exp A = Pade.expApprox ℝ p q A + ((-1) ^ q / (p + q)! : ℝ) • (A ^ (p + q + 1) *
      (aeval A (Pade.expDen ℝ p q))⁻¹ *
        ∫ u in (0 : ℝ)..1, (u ^ p * (1 - u) ^ q) • exp ((1 - u) • A)) := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact Pade.exp_eq_expApprox_add p q A hD

/-- **The Moler–Van Loan bound** quoted in §9.3.1: if `‖A‖_∞/2^j ≤ 1/2`, then
`F_pq = (R_pq(A/2^j))^{2^j} = e^{A+E}` for some `E` with `AE = EA` and
`‖E‖_∞ ≤ ε(p, q) ‖A‖_∞`, `ε(p, q) = 2^{3-(p+q)} p! q!/((p+q)! (p+q+1)!)`; and consequently
`‖e^A - F_pq‖_∞ / ‖e^A‖_∞ ≤ ε(p, q) ‖A‖_∞ e^{ε(p, q) ‖A‖_∞}`. -/
theorem moler_van_loan [NeZero n] (p q j : ℕ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ‖A‖ / 2 ^ j ≤ 1 / 2) :
    (∃ E : Matrix (Fin n) (Fin n) ℝ,
      Pade.expApprox ℝ p q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j = exp (A + E) ∧ A * E = E * A ∧
        ‖E‖ ≤ Pade.errorBound p q * ‖A‖) ∧
    ‖exp A - Pade.expApprox ℝ p q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j‖ / ‖exp A‖ ≤
      Pade.errorBound p q * ‖A‖ * Real.exp (Pade.errorBound p q * ‖A‖) := by
  have hA' : ‖A‖ ≤ 2 ^ j / 2 := by
    rw [div_le_iff₀ (by positivity)] at hA
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hc, hE, h⟩ := Pade.exists_exp_add_eq_expApprox_pow p q j hA'
    exact ⟨E, h, hc.eq, hE⟩
  · have hpos : 0 < ‖exp A‖ := norm_pos_iff.mpr (Matrix.isUnit_exp A).ne_zero
    rw [div_le_iff₀ hpos]
    exact Pade.norm_exp_sub_expApprox_pow_le p q j hA'

end Infinity

/-- Splitting a sum over `range (2m)` into its even and odd terms. -/
private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ k ∈ range m, f (2 * k) + ∑ k ∈ range m, f (2 * k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    abel

/-- §9.3.1's cheaper evaluation of the diagonal approximants: with `c_k` the coefficients of
`N_qq`, `U = ∑_k c_{2k} A^{2k}` and `V = ∑_k c_{2k+1} A^{2k}`, `N_qq(A) = U + A V` and
`D_qq(A) = U - A V` (for `q = 8` the book's explicit `U`, `V`, evaluated by Horner in `A²`). -/
theorem pade_even_odd (q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    let c := fun k => (Pade.expNum ℝ q q).coeff k
    let U := ∑ k ∈ range (q + 1), c (2 * k) • A ^ (2 * k)
    let V := ∑ k ∈ range (q + 1), c (2 * k + 1) • A ^ (2 * k)
    aeval A (Pade.expNum ℝ q q) = U + A * V ∧ aeval A (Pade.expDen ℝ q q) = U - A * V := by
  intro c U V
  have hden : ∀ k, (Pade.expDen ℝ q q).coeff k = (-1) ^ k * c k := fun k => by
    simp only [c, Pade.coeff_expDen, Pade.coeff_expNum]
    split_ifs <;> simp
  have hdeg : ∀ P : ℝ[X], (∀ k, q < k → P.coeff k = 0) → P.natDegree < 2 * (q + 1) :=
    fun P hP => lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => hP k
      (by exact_mod_cast hk)) (by omega)
  have hNz : ∀ k, q < k → (Pade.expNum ℝ q q).coeff k = 0 := fun k hk => by
    rw [Pade.coeff_expNum, ite_eq_right (by omega)]
  have hDz : ∀ k, q < k → (Pade.expDen ℝ q q).coeff k = 0 := fun k hk => by
    rw [Pade.coeff_expDen, ite_eq_right (by omega)]
  have hodd : ∀ (d : ℝ) (k : ℕ), d • A ^ (2 * k + 1) = A * (d • A ^ (2 * k)) := fun d k => by
    rw [mul_smul_comm, ← pow_succ']
  constructor
  · rw [aeval_eq_sum_range' (hdeg _ hNz), sum_range_two_mul]
    simp only [U, V, c, Finset.mul_sum, hodd]
  · rw [aeval_eq_sum_range' (hdeg _ hDz), sum_range_two_mul, sub_eq_add_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hden, pow_mul (-1 : ℝ) 2 k, neg_one_sq, one_pow, one_mul]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hden, pow_succ (-1 : ℝ) (2 * k), pow_mul (-1 : ℝ) 2 k, neg_one_sq, one_pow, one_mul,
        neg_one_mul, neg_smul, hodd]

/-! ### Algorithm 9.3.1: scaling and squaring -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- A matrix overwritten entry by entry, `c_il ← g(i, l, c_il)`, row by row and left to right: the
entrywise updates `A = A/2^j`, `N = N + c X`, `D = D + (-1)^k c X` of Algorithm 9.3.1. -/
def updateEntriesM (g : Fin n → Fin n → ℝ → M ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun C i => do
    let r ← (List.finRange n).foldlM (fun (r : Fin n → ℝ) l => do
      let b ← g i l (r l)
      pure (Function.update r l b)) (C i)
    pure (C.updateRow i r)) C

/-- **Scaling and squaring with exponent offset `o`**: the loop of Algorithm 9.3.1 with
`j = max{0, o + ⌊log₂ ‖A‖_∞⌋}`. The book prints `o = 1` (`algorithm_9_3_1`); `o = 2` is the
corrected choice (`algorithm_9_3_1_corrected`), for which the claimed backward error holds. -/
noncomputable def scalingSquaring (o : ℤ) (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let s ← (List.finRange n).foldlM (fun (s : Fin n → ℝ) i => do
    let t ← (List.finRange n).foldlM (fun c l => rnd (c + |A i l|)) 0
    pure (Function.update s i t)) 0
  let j : ℕ := (o + Int.log 2 (⨆ i, s i)).toNat
  let B ← updateEntriesM (fun i l _ => rnd (A i l / 2 ^ j)) A
  let q : ℕ := sInf {q : ℕ | Pade.errorBound q q ≤ δ}
  let st ← (List.range q).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Matrix (Fin n) (Fin n) ℝ × ℝ) k₀ => do
    let t ← rnd (st.2.2.2 * ((q - (k₀ + 1) + 1 : ℕ) : ℝ))
    let c ← rnd (t / (((2 * q - (k₀ + 1) + 1) * (k₀ + 1) : ℕ) : ℝ))
    let X ← Chapter01.algorithm_1_1_5 rnd B st.2.2.1 0
    let N ← updateEntriesM (fun i l x => do let p ← rnd (c * X i l); rnd (x + p)) st.2.1
    let D ← updateEntriesM (fun i l x => do
      let p ← rnd ((-1) ^ (k₀ + 1) * c * X i l); rnd (x + p)) st.1
    pure (D, N, X, c)) (1, 1, 1, 1)
  let F ← Chapter03.solveMultipleRHS rnd st.1 st.2.1
  (List.range j).foldlM (fun F _ => Chapter01.algorithm_1_1_5 rnd F F 0) F

/-- **Algorithm 9.3.1 (Scaling and Squaring).** "Given `δ > 0` and `A ∈ ℝ^{n×n}`, the following
algorithm computes `F = e^{A+E}` where `‖E‖_∞ ≤ δ ‖A‖_∞`":
```
j = max{0, 1 + floor(log₂(‖A‖_∞))}
A = A/2^j
Let q be the smallest nonnegative integer such that ε(q, q) ≤ δ
D = I, N = I, X = I, c = 1
for k = 1:q
    c = c · (q - k + 1)/((2q - k + 1) k)
    X = AX, N = N + c · X, D = D + (-1)^k c · X
end
Solve DF = N for F using Gaussian elimination
for k = 1:j
    F = F²
end
```
`‖A‖_∞ = max_i ∑_l |a_il|` is computed with rounded additions (`|·|` and `max` exact); `j` and `q`
are exact discrete choices on computed values (`q = sInf {q | ε(q, q) ≤ δ}`, `0` if there is
none); the integer factors of
the `c` update are exact; `X = AX` and `F = F²` are Algorithm 1.1.5 from `C = 0`; the solve is
chapter 3's Gaussian elimination with partial pivoting for the multiple right-hand side `N`
(`GolubVanLoan.Chapter03.solveMultipleRHS`). It is `scalingSquaring` with the printed offset `1`. -/
noncomputable def algorithm_9_3_1 (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  scalingSquaring rnd 1 δ A

/-- **Algorithm 9.3.1 with the corrected scaling exponent** `j = max{0, 2 + ⌊log₂ ‖A‖_∞⌋}`, which
guarantees `‖A‖_∞/2^j < 1/2` (erratum to the printed `1 + ⌊log₂ ‖A‖_∞⌋`). -/
noncomputable def algorithm_9_3_1_corrected (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  scalingSquaring rnd 2 δ A

end Programs

/-- The entrywise update in exact arithmetic. -/
private theorem updateEntriesM_id (h : Fin n → Fin n → ℝ → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (updateEntriesM (M := Id) (fun i l x => pure (h i l x)) C) =
      Matrix.of fun i l => h i l (C i l) := by
  ext i l
  have h1 := Matrix.idRun_foldlM_updateRow_apply (fun i (row : Fin n → ℝ) =>
    (List.finRange n).foldlM (fun (r : Fin n → ℝ) l => do
      let b ← (pure (h i l (r l)) : Id ℝ)
      pure (Function.update r l b)) row) (List.finRange n) (List.nodup_finRange n) C i
  have h2 := List.idRun_foldlM_update_apply (fun l (x : ℝ) => (pure (h i l x) : Id ℝ))
    (List.finRange n) (List.nodup_finRange n) (C i) l
  rw [ite_eq_left (List.mem_finRange i)] at h1
  rw [ite_eq_left (List.mem_finRange l)] at h2
  simp only [updateEntriesM, Matrix.of_apply]
  rw [h1, h2]
  rfl

/-- The recurrence of the Padé coefficients used by Algorithm 9.3.1:
`c_k = c_{k-1} (q - k + 1)/((2q - k + 1) k)` for `c_k` the `k`-th coefficient of `N_qq`,
`1 ≤ k ≤ q`. -/
private theorem coeff_expNum_succ {q k : ℕ} (hk : k + 1 ≤ q) :
    (Pade.expNum ℝ q q).coeff (k + 1) = (Pade.expNum ℝ q q).coeff k *
      ((q - (k + 1) + 1 : ℕ) : ℝ) / (((2 * q - (k + 1) + 1) * (k + 1) : ℕ) : ℝ) := by
  obtain ⟨b, rfl⟩ : ∃ b, q = k + 1 + b := ⟨q - (k + 1), by omega⟩
  rw [Pade.coeff_expNum, Pade.coeff_expNum, ite_eq_left hk, ite_eq_left (by omega)]
  have e1 : k + 1 + b + (k + 1 + b) - (k + 1) = k + 1 + 2 * b := by omega
  have e2 : k + 1 + b + (k + 1 + b) - k = (k + 1 + 2 * b) + 1 := by omega
  have e3 : k + 1 + b - (k + 1) = b := by omega
  have e4 : k + 1 + b - k = b + 1 := by omega
  have e5 : 2 * (k + 1 + b) - (k + 1) + 1 = (k + 1 + 2 * b) + 1 := by omega
  rw [e1, e2, e3, e4, e5, Nat.factorial_succ (k + 1 + 2 * b), Nat.factorial_succ b,
    Nat.factorial_succ k]
  have h1 := Nat.factorial_pos (k + 1 + 2 * b)
  have h2 := Nat.factorial_pos b
  have h3 := Nat.factorial_pos k
  have h4 := Nat.factorial_pos (k + 1 + b + (k + 1 + b))
  push_cast
  field_simp

/-- The state of Algorithm 9.3.1's `k` loop after `m ≤ q` steps, in exact arithmetic:
`D = ∑_{k ≤ m} (-1)^k c_k B^k`, `N = ∑_{k ≤ m} c_k B^k`, `X = B^m`, `c = c_m`. -/
private theorem padeLoop_id (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) :
    ∀ m ≤ q, Id.run ((List.range m).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × ℝ) k₀ => do
      let t ← (pure (st.2.2.2 * ((q - (k₀ + 1) + 1 : ℕ) : ℝ)) : Id ℝ)
      let c ← (pure (t / (((2 * q - (k₀ + 1) + 1) * (k₀ + 1) : ℕ) : ℝ)) : Id ℝ)
      let X ← Chapter01.algorithm_1_1_5 pure B st.2.2.1 0
      let N ← updateEntriesM (M := Id) (fun i l x => do
        let p ← (pure (c * X i l) : Id ℝ); pure (x + p)) st.2.1
      let D ← updateEntriesM (M := Id) (fun i l x => do
        let p ← (pure ((-1) ^ (k₀ + 1) * c * X i l) : Id ℝ); pure (x + p)) st.1
      pure (D, N, X, c)) (1, 1, 1, 1)) =
      (∑ k ∈ range (m + 1), ((-1) ^ k * (Pade.expNum ℝ q q).coeff k) • B ^ k,
        ∑ k ∈ range (m + 1), (Pade.expNum ℝ q q).coeff k • B ^ k, B ^ m,
        (Pade.expNum ℝ q q).coeff m) := by
  intro m hm
  rw [List.idRun_foldlM]
  induction m with
  | zero =>
    have h0 : (Pade.expNum ℝ q q).coeff 0 = 1 := by
      rw [Pade.coeff_expNum, ite_eq_left (Nat.zero_le q)]
      simp only [Nat.sub_zero, Nat.factorial_zero, mul_one]
      exact div_self (by positivity)
    simp [h0]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    simp only [pure_bind, Id.run_pure, Id.run_bind]
    rw [Chapter01.algorithm_1_1_5_spec, zero_add, updateEntriesM_id, updateEntriesM_id,
      ← coeff_expNum_succ hm, pow_succ' B m]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · ext i l
      simp only [Finset.sum_range_succ, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
        pow_succ', Matrix.of_apply]
    · ext i l
      simp only [Finset.sum_range_succ, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
        pow_succ', Matrix.of_apply]

/-- The squaring loop in exact arithmetic: `F ← F²`, `j` times, is `F^{2^j}`. -/
private theorem squaring_id (F : Matrix (Fin n) (Fin n) ℝ) (j : ℕ) :
    Id.run ((List.range j).foldlM (fun F _ => Chapter01.algorithm_1_1_5 pure F F 0) F) =
      F ^ 2 ^ j := by
  rw [List.idRun_foldlM]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Chapter01.algorithm_1_1_5_spec, zero_add, pow_succ, pow_mul, sq]

/-- The Padé polynomials `N_qq`, `D_qq` at a matrix, as the sums the loop of Algorithm 9.3.1
accumulates. -/
private theorem aeval_padeNum_denom (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) :
    aeval B (Pade.expNum ℝ q q) = ∑ k ∈ range (q + 1), (Pade.expNum ℝ q q).coeff k • B ^ k ∧
      aeval B (Pade.expDen ℝ q q) =
        ∑ k ∈ range (q + 1), ((-1) ^ k * (Pade.expNum ℝ q q).coeff k) • B ^ k := by
  have hdeg : ∀ P : ℝ[X], (∀ k, q < k → P.coeff k = 0) → P.natDegree < q + 1 :=
    fun P hP => Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => hP k
      (by exact_mod_cast hk))
  have hN := hdeg (Pade.expNum ℝ q q) fun k hk => by
    rw [Pade.coeff_expNum, ite_eq_right (by omega)]
  have hD := hdeg (Pade.expDen ℝ q q) fun k hk => by
    rw [Pade.coeff_expDen, ite_eq_right (by omega)]
  refine ⟨aeval_eq_sum_range' hN B, ?_⟩
  rw [aeval_eq_sum_range' hD B]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Pade.coeff_expDen, Pade.coeff_expNum, ite_eq_left hkq, ite_eq_left hkq]

/-- **Exact semantics of scaling and squaring** with exponent offset `o`: with
`ν = max_i ∑_l |a_il|` (`= ‖A‖_∞`), `j = max{0, o + ⌊log₂ ν⌋}` and `q` the smallest integer with
`ε(q, q) ≤ δ`, as the program computes them: if `D_qq(A/2^j)` is nonsingular, it returns
`R_qq(A/2^j)^{2^j}`. The loop computes `c_k = (2q-k)! q!/((2q)! k! (q-k)!)` (the recurrence
`c_k = c_{k-1} (q-k+1)/((2q-k+1)k)`), so `N = N_qq(A/2^j)` and `D = D_qq(A/2^j)` (`pade_def`);
the solve returns `D⁻¹ N` (chapter 3's (3.4.12)); the squarings give the `2^j`-th power. -/
theorem scalingSquaring_spec (o : ℤ) (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) {j q : ℕ}
    (hj : j = (o + Int.log 2 (⨆ i, ∑ l, |A i l|)).toNat)
    (hq : q = sInf {q : ℕ | Pade.errorBound q q ≤ δ})
    (hD : IsUnit (aeval ((2⁻¹ : ℝ) ^ j • A) (Pade.expDen ℝ q q))) :
    Id.run (scalingSquaring pure o δ A) = Pade.expApprox ℝ q q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j := by
  have hs : Id.run ((List.finRange n).foldlM (fun (s : Fin n → ℝ) i => do
      let t ← (List.finRange n).foldlM (fun c l => (pure (c + |A i l|) : Id ℝ)) 0
      pure (Function.update s i t)) 0) = fun i => ∑ l, |A i l| := by
    funext i
    have h := List.idRun_foldlM_update_apply (fun i (_ : ℝ) =>
      (List.finRange n).foldlM (fun c l => (pure (c + |A i l|) : Id ℝ)) 0) (List.finRange n)
      (List.nodup_finRange n) 0 i
    rw [ite_eq_left (List.mem_finRange i)] at h
    rw [h, List.foldlM_pure, Id.run_pure, List.foldl_add_eq_add_sum_map, zero_add,
      ← Fin.sum_univ_def]
  set B : Matrix (Fin n) (Fin n) ℝ := (2⁻¹ : ℝ) ^ j • A with hBdef
  have hB : Id.run (updateEntriesM (M := Id) (fun i l _ => pure (A i l / 2 ^ j)) A) = B := by
    rw [updateEntriesM_id]
    ext i l
    simp [hBdef, div_eq_mul_inv, mul_comm]
  obtain ⟨hNum, hDen⟩ := aeval_padeNum_denom B q
  have hloop := padeLoop_id B q q le_rfl
  have hDd : IsUnit (aeval B (Pade.expDen ℝ q q)).det := (Matrix.isUnit_iff_isUnit_det _).1 hD
  have hsolve : Id.run (Chapter03.solveMultipleRHS pure (aeval B (Pade.expDen ℝ q q))
      (aeval B (Pade.expNum ℝ q q))) = Pade.expApprox ℝ q q B := by
    have h := (Chapter03.equation_3_4_12 hD (aeval B (Pade.expNum ℝ q q))).1
    set X := Id.run (Chapter03.solveMultipleRHS pure (aeval B (Pade.expDen ℝ q q))
      (aeval B (Pade.expNum ℝ q q))) with hX
    rw [(pade_def q q).2.2.1 B, ← h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDd,
      Matrix.one_mul]
  rw [scalingSquaring, Id.run_bind, hs]
  dsimp only
  rw [← hj, Id.run_bind, hB]
  rw [← hq, Id.run_bind, hloop]
  rw [← hNum, ← hDen, Id.run_bind, hsolve, squaring_id]

/-- **Exact semantics of Algorithm 9.3.1.** With `ν = max_i ∑_l |a_il|` (`= ‖A‖_∞`),
`j = max{0, 1 + ⌊log₂ ν⌋}` (for `A = 0` the program's `Int.log` gives `j = 1`, which does not
change the result) and `q` the smallest integer with `ε(q, q) ≤ δ`, as the algorithm computes
them: if `D_qq(A/2^j)` is nonsingular, the algorithm returns `R_qq(A/2^j)^{2^j}`
(`scalingSquaring_spec`). -/
theorem algorithm_9_3_1_spec (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) {j q : ℕ}
    (hj : j = (1 + Int.log 2 (⨆ i, ∑ l, |A i l|)).toNat)
    (hq : q = sInf {q : ℕ | Pade.errorBound q q ≤ δ})
    (hD : IsUnit (aeval ((2⁻¹ : ℝ) ^ j • A) (Pade.expDen ℝ q q))) :
    Id.run (algorithm_9_3_1 pure δ A) = Pade.expApprox ℝ q q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j :=
  scalingSquaring_spec 1 δ A hj hq hD

section Infinity

open scoped Matrix.Norms.Operator

/-- **The backward error of scaling and squaring** with exponent offset `o`, in exact arithmetic,
whenever the scaling achieves `‖A‖_∞/2^j ≤ 1/2`: then `D_qq(A/2^j)` is nonsingular
(`‖A/2^j‖_∞ < log 2`, `Pade.isUnit_aeval_expDen`), and the Moler–Van Loan bound with
`ε(q, q) ≤ δ` gives `F = e^{A+E}` with `AE = EA` and `‖E‖_∞ ≤ δ ‖A‖_∞`. -/
theorem scalingSquaring_spec_backward [NeZero n] (o : ℤ) {δ : ℝ}
    (hδ : ∃ q, Pade.errorBound q q ≤ δ) (A : Matrix (Fin n) (Fin n) ℝ) {j q : ℕ}
    (hj : j = (o + Int.log 2 (⨆ i, ∑ l, |A i l|)).toNat)
    (hq : q = sInf {q : ℕ | Pade.errorBound q q ≤ δ}) (hA : ‖A‖ / 2 ^ j ≤ 1 / 2) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ,
      Id.run (scalingSquaring pure o δ A) = exp (A + E) ∧ A * E = E * A ∧ ‖E‖ ≤ δ * ‖A‖ := by
  have hsmall : ‖(2⁻¹ : ℝ) ^ j • A‖ < Real.log 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_pow, ← div_eq_inv_mul]
    linarith [Real.log_two_gt_d9]
  have hD := (Pade.isUnit_aeval_expDen (𝕂 := ℝ) q q hsmall).1
  obtain ⟨⟨E, hE, hc, hEn⟩, -⟩ := moler_van_loan q q j hA
  have hqδ : Pade.errorBound q q ≤ δ := hq ▸ Nat.sInf_mem hδ
  refine ⟨E, (scalingSquaring_spec o δ A hj hq hD).trans hE, hc, hEn.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hqδ (norm_nonneg A)

/-- **Algorithm 9.3.1's claim**, "computes `F = e^{A+E}` where `‖E‖_∞ ≤ δ ‖A‖_∞`", in exact
arithmetic, under the hypothesis `‖A‖_∞/2^j ≤ 1/2` that the printed scaling does not deliver.
With `ν = ‖A‖_∞` and the printed `j = max{0, 1 + ⌊log₂ ν⌋}` the hypothesis is narrow: for
`ν ≤ 1/2` it holds with `j = 0`, i.e. when no scaling happens at all; for `ν ∈ (1/2, 1)` it
fails (`j = 0`, ratio `ν`); for `ν ≥ 1` the ratio `ν/2^j` lies in `[1/2, 1)` and equals `1/2`
only when `ν` is a power of two (`ν = 3`: `j = 2`, ratio `3/4`). So where scaling actually
happens the bound is (almost) never delivered; the corrected exponent
`j = max{0, 2 + ⌊log₂ ν⌋}` always delivers it (`algorithm_9_3_1_corrected_spec_backward`, erratum).
`q` exists for every `δ > 0`; the hypothesis `hδ` says so directly. -/
theorem algorithm_9_3_1_spec_backward [NeZero n] {δ : ℝ} (hδ : ∃ q, Pade.errorBound q q ≤ δ)
    (A : Matrix (Fin n) (Fin n) ℝ) {j q : ℕ}
    (hj : j = (1 + Int.log 2 (⨆ i, ∑ l, |A i l|)).toNat)
    (hq : q = sInf {q : ℕ | Pade.errorBound q q ≤ δ}) (hA : ‖A‖ / 2 ^ j ≤ 1 / 2) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ,
      Id.run (algorithm_9_3_1 pure δ A) = exp (A + E) ∧ A * E = E * A ∧ ‖E‖ ≤ δ * ‖A‖ :=
  scalingSquaring_spec_backward 1 hδ A hj hq hA

/-- `‖A‖_∞` is the largest absolute row sum. -/
private theorem norm_eq_iSup_sum_abs [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖ = ⨆ i, ∑ l, |A i l| := by
  rw [Matrix.linfty_opNorm_def, Finset.sup_univ_eq_ciSup, NNReal.coe_iSup]
  simp [Real.norm_eq_abs]

/-- The corrected exponent `j = max{0, 2 + ⌊log₂ ν⌋}` scales any `ν ≥ 0` below `1/2`. -/
private theorem div_two_pow_corrected_le {ν : ℝ} (hν : 0 ≤ ν) :
    ν / 2 ^ (2 + Int.log 2 ν).toNat ≤ 1 / 2 := by
  rcases hν.eq_or_lt with rfl | hν
  · simp
  have hlt : ν < (2 : ℝ) ^ (Int.log 2 ν + 1) := Int.lt_zpow_succ_log_self (by norm_num) ν
  have hpos : (0 : ℝ) < 2 ^ (2 + Int.log 2 ν).toNat := by positivity
  rw [div_le_iff₀ hpos]
  have hcast : ((2 : ℝ) ^ (2 + Int.log 2 ν).toNat) = (2 : ℝ) ^ ((2 + Int.log 2 ν).toNat : ℤ) :=
    (zpow_natCast _ _).symm
  rw [hcast]
  have hmono : (2 : ℝ) ^ (2 + Int.log 2 ν) ≤ 2 ^ ((2 + Int.log 2 ν).toNat : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (Int.self_le_toNat _)
  have heq : (2 : ℝ) ^ (2 + Int.log 2 ν) = 2 * 2 ^ (Int.log 2 ν + 1) := by
    rw [show 2 + Int.log 2 ν = 1 + (Int.log 2 ν + 1) by ring, zpow_add₀ (by norm_num), zpow_one]
  nlinarith

/-- **Algorithm 9.3.1 with the corrected exponent delivers its claim**: in exact arithmetic,
`algorithm_9_3_1_corrected` (`j = max{0, 2 + ⌊log₂ ‖A‖_∞⌋}`) computes `F = e^{A+E}` with `AE = EA`
and `‖E‖_∞ ≤ δ ‖A‖_∞`, with no hypothesis on `A`. -/
theorem algorithm_9_3_1_corrected_spec_backward [NeZero n] {δ : ℝ}
    (hδ : ∃ q, Pade.errorBound q q ≤ δ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ,
      Id.run (algorithm_9_3_1_corrected pure δ A) = exp (A + E) ∧ A * E = E * A ∧
        ‖E‖ ≤ δ * ‖A‖ := by
  refine scalingSquaring_spec_backward 2 hδ A rfl rfl ?_
  rw [norm_eq_iSup_sum_abs]
  exact div_two_pow_corrected_le
    (Real.iSup_nonneg fun i => Finset.sum_nonneg fun l _ => abs_nonneg _)

end Infinity

/-! ### §9.3.2 Perturbation theory -/

section Two

open scoped Matrix.Norms.L2Operator

/-- §9.3.2: `X(t) = e^{At}` solves `Ẋ(t) = A X(t)`, `X(0) = I`, and is its unique solution. -/
theorem exp_unique_ode (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => exp (s • A)) (A * exp (t • A)) t) ∧
    exp ((0 : ℝ) • A) = 1 ∧
    ∀ X : ℝ → Matrix (Fin n) (Fin n) ℝ, (∀ t, HasDerivAt X (A * X t) t) → X 0 = 1 →
      ∀ t, X t = exp (t • A) :=
  ⟨fun t => hasDerivAt_exp_smul_const' A t, by rw [zero_smul, exp_zero],
    fun _ hX h0 t => eq_exp_smul_of_hasDerivAt hX h0 t⟩

/-- §9.3.2: `e^{(A+E)t} - e^{At} = ∫₀ᵗ e^{A(t-s)} E e^{(A+E)s} ds`, and for `t ≥ 0`
`‖e^{(A+E)t} - e^{At}‖₂ / ‖e^{At}‖₂ ≤ (‖E‖₂ / ‖e^{At}‖₂) ∫₀ᵗ ‖e^{A(t-s)}‖₂ ‖e^{(A+E)s}‖₂ ds`. -/
theorem exp_perturbation_integral (A E : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    exp (t • (A + E)) - exp (t • A) =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • A) * E * exp (s • (A + E)) ∧
    (0 ≤ t → ‖exp (t • (A + E)) - exp (t • A)‖ / ‖exp (t • A)‖ ≤
      ‖E‖ / ‖exp (t • A)‖ * ∫ s in (0 : ℝ)..t, ‖exp ((t - s) • A)‖ * ‖exp (s • (A + E))‖) := by
  refine ⟨exp_smul_add_sub_exp_smul A E t, fun ht => ?_⟩
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (norm_exp_smul_add_sub_exp_smul_le A E ht) (norm_nonneg _)

/-- **(9.3.3), the spectral abscissa** `α(A) = max {Re λ : λ ∈ λ(A)}`: it is attained by an
eigenvalue and bounds the real part of every eigenvalue. -/
theorem equation_9_3_3 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ μ ∈ spectrum ℂ A, μ.re = spectralAbscissa A) ∧
    ∀ μ ∈ spectrum ℂ A, μ.re ≤ spectralAbscissa A :=
  ⟨exists_mem_spectrum_re_eq_spectralAbscissa (Matrix.finite_spectrum A).isCompact
      (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A),
    fun _ hμ => re_le_spectralAbscissa (Matrix.finite_spectrum A).isBounded hμ⟩

/-- **(9.3.2)**, corrected: if `Qᴴ A Q = diag(λ_i) + N` is a Schur decomposition, then for `t ≥ 0`
`‖e^{At}‖₂ ≤ e^{α(A) t} M_S(t)`, `M_S(t) = ∑_{k=0}^{n-1} ‖N t‖₂ᵏ / k!`. The book prints
`e^{α(A) t M_S(t)}`, which fails for `α(A) < 0` and `N ≠ 0`. -/
theorem equation_9_3_2 [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖exp (t • A)‖ ≤ Real.exp (spectralAbscissa A * t) * ∑ k ∈ range n,
      ‖t • (star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k ! := by
  simpa only [Matrix.schurExpFactor, Fintype.card_fin] using
    Matrix.l2_opNorm_exp_smul_le_of_schur hQ hT ht

/-- §9.3.2, "with a little manipulation": for `t ≥ 0`,
`‖e^{(A+E)t} - e^{At}‖₂ / ‖e^{At}‖₂ ≤ t ‖E‖₂ M_S(t)² exp(t M_S(t) ‖E‖₂)`. -/
theorem exp_perturbation_schur [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular)
    (E : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    let N := star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i
    let MS : ℝ → ℝ := fun s => (∑ k ∈ range n, ‖s • N‖ ^ k / k !)
    ‖exp (t • (A + E)) - exp (t • A)‖ / ‖exp (t • A)‖ ≤
      t * ‖E‖ * MS t ^ 2 * Real.exp (t * MS t * ‖E‖) := by
  have h := Matrix.l2_opNorm_exp_smul_add_sub_le hQ hT E ht
  simp only [Matrix.schurExpFactor, Fintype.card_fin] at h
  exact h

/-- §9.3.2: `M_S(t) = 1` for all `t > 0` if and only if `A` is normal (its Schur form is then
diagonal, `N = 0`). -/
theorem schurDeparture_eq_one_iff [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular) :
    (∀ t : ℝ, 0 < t → ∑ k ∈ range n,
      ‖t • (star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k ! = 1) ↔
      IsStarNormal A := by
  rw [Matrix.isStarNormal_iff_strictUpper_eq_zero hQ hT, ← sub_eq_zero]
  set N := star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  constructor
  · intro h
    have h1 := h 1 one_pos
    rw [Finset.sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      add_eq_right] at h1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by positivity).mp h1
    rcases m with _ | m
    · ext i j
      obtain rfl : i = j := Fin.ext (by have := i.2; have := j.2; omega)
      simp [N]
    · have h0 := hz 0 (Finset.mem_range.mpr (Nat.succ_pos m))
      simpa [one_smul] using h0
  · intro hN t _
    rw [hN, Finset.sum_range_succ']
    simp

/-- §9.3.2: Van Loan's condition number satisfies `ν(A, t) ≥ t ‖A‖₂` for `t ≥ 0`. -/
theorem expCondNumber_ge [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    t * ‖A‖ ≤ expCondNumber A t :=
  mul_norm_le_expCondNumber A ht

/-- **(9.3.4)**: if `A` is normal, then `‖e^{At}‖₂ = e^{α(A) t}` for `t ≥ 0`. -/
theorem equation_9_3_4 [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) {t : ℝ}
    (ht : 0 ≤ t) : ‖exp (t • A)‖ = Real.exp (spectralAbscissa A * t) :=
  Matrix.l2_opNorm_exp_smul_of_isStarNormal hA ht

/-- §9.3.2, the true half of "equality holding for all nonnegative `t` if and only if the matrix
`A` is normal": for normal `A`, `ν(A, t) = t ‖A‖₂` for every `t ≥ 0`. -/
theorem expCondNumber_eq_of_isStarNormal [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsStarNormal A) {t : ℝ} (ht : 0 ≤ t) : expCondNumber A t = t * ‖A‖ :=
  Matrix.expCondNumber_eq_of_isStarNormal hA ht

end Two

/-- **(9.3.5)**: for `A = [-1 1000; 0 -1]`, `e^{At} = e^{-t} [1 1000t; 0 1]`. -/
theorem equation_9_3_5 (t : ℝ) :
    exp (t • !![-1, 1000; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) =
      Real.exp (-t) • !![1, 1000 * t; 0, 1] := by
  set N : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1000 * t; 0, 0]
  have hsplit : (t • !![-1, 1000; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal (fun _ => -t) + N := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, mul_comm]
  have hN2 : N ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hc : Commute (Matrix.diagonal fun _ : Fin 2 => -t) N := by
    rw [← Matrix.smul_one_eq_diagonal]
    exact (Commute.one_left N).smul_left _
  have hexpN : exp N = 1 + N := NormedSpace.exp_eq_one_add_of_sq_eq_zero hN2
  rw [hsplit, Matrix.exp_add_of_commute _ _ hc, Matrix.exp_diagonal, hexpN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Pi.exp_def, ← Real.exp_eq_exp_ℝ]

section Counterexample

open scoped Matrix.Norms.L2Operator

/-- The exponential of the counterexample matrix `[1] ⊕ [0 1; 0 0]`. -/
private theorem exp_smul_cex (s : ℝ) :
    exp (s • (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ)) =
      !![(Real.exp s : ℂ), 0, 0; 0, 1, (s : ℂ); 0, 0, 1] := by
  set N : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, (s : ℂ); 0, 0, 0]
  have hsplit : (s • !![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) =
      Matrix.diagonal ![(s : ℂ), 0, 0] + N := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N]
  have hN2 : N ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hc : Commute (Matrix.diagonal ![(s : ℂ), 0, 0]) N := by
    unfold Commute SemiconjBy
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_three]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hc, Matrix.exp_diagonal,
    NormedSpace.exp_eq_one_add_of_sq_eq_zero hN2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_three, Pi.exp_def, ← Complex.exp_eq_exp_ℂ,
      Complex.ofReal_exp]

/-- The spectral norm of `e^{sA}` for the counterexample matrix is `e^s`, `s ≥ 0`: the block
`[1 s; 0 1]` has norm at most `1 + s ≤ e^s`. -/
private theorem norm_exp_smul_cex {s : ℝ} (hs : 0 ≤ s) :
    ‖exp (s • (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ))‖ = Real.exp s := by
  rw [exp_smul_cex]
  set M : Matrix (Fin 3) (Fin 3) ℂ := !![(Real.exp s : ℂ), 0, 0; 0, 1, (s : ℂ); 0, 0, 1]
  set E := Real.exp s
  have hE : 0 < E := Real.exp_pos s
  have hv : ∀ x : EuclideanSpace ℂ (Fin 3),
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 0 = (E : ℂ) * x 0 ∧
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 1 = x 1 + (s : ℂ) * x 2 ∧
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 2 = x 2 := fun x => by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [M, E, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hsq : ∀ x : EuclideanSpace ℂ (Fin 3),
      ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ ^ 2 =
        ‖(E : ℂ) * x 0‖ ^ 2 + ‖x 1 + (s : ℂ) * x 2‖ ^ 2 + ‖x 2‖ ^ 2 := fun x => by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, (hv x).1, (hv x).2.1, (hv x).2.2]
  have hEn : ‖(E : ℂ)‖ = E := by rw [Complex.norm_real, Real.norm_of_nonneg hE.le]
  apply le_antisymm
  · rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ hE.le fun x => ?_
    have h1 : 1 + s ≤ E := by linarith [Real.add_one_le_exp s]
    set a := ‖x 1‖
    set b := ‖x 2‖
    set c := ‖x 0‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hab : ‖x 1 + (s : ℂ) * x 2‖ ≤ a + s * b := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    have hx : ‖x‖ ^ 2 = c ^ 2 + a ^ 2 + b ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), hsq, mul_pow, hx, norm_mul, hEn]
    have h2 : ‖x 1 + (s : ℂ) * x 2‖ ^ 2 ≤ (a + s * b) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hab 2
    have h3 : (a + s * b) ^ 2 + b ^ 2 ≤ (1 + s) ^ 2 * (a ^ 2 + b ^ 2) := by
      nlinarith [mul_nonneg hs (sq_nonneg (a - b)), sq_nonneg (s * a),
        mul_nonneg hs (add_nonneg (sq_nonneg a) (sq_nonneg b))]
    have h4 : (1 + s) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith [mul_le_mul_of_nonneg_right h4 (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  · rw [Matrix.cstar_norm_def]
    set x : EuclideanSpace ℂ (Fin 3) := EuclideanSpace.single 0 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hMx : ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ = E := by
      rw [← sq_eq_sq₀ (norm_nonneg _) hE.le, hsq]
      simp [x]
    calc E = ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ := hMx.symm
      _ ≤ ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [hx, mul_one]

/-- **§9.3.2's "only if" is false**: `A = [1] ⊕ [0 1; 0 0]` is not normal, and yet
`ν(A, t) = t ‖A‖₂` for every `t ≥ 0`, because `‖e^{sA}‖₂ = e^s` for `s ≥ 0` (the book: "equality
holding for all nonnegative `t` if and only if the matrix `A` is normal"). -/
theorem expCondNumber_eq_iff_counterexample :
    ¬ IsStarNormal (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) ∧
    ∀ t : ℝ, 0 ≤ t → expCondNumber (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) t =
      t * ‖(!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ)‖ := by
  refine ⟨fun h => ?_, fun t ht => expCondNumber_eq_of_norm_exp_smul_eq _ ht fun s hs => by
    rw [one_mul]
    exact norm_exp_smul_cex hs.1⟩
  have := congrFun (congrFun h.star_comm_self 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_eq_conjTranspose] at this

end Counterexample

/-! ### §9.3.3 Pseudospectra and transient growth -/

section Pseudospectra

open scoped Matrix.Norms.L2Operator
open Filter Topology

/-- **(9.3.6)**: for every `ε > 0`, `sup_{t > 0} ‖e^{At}‖₂ ≥ α_ε(A)/ε`, with chapter 7's
`ε`-pseudospectral abscissa `α_ε(A) = sup_{z ∈ Λ_ε(A)} Re z` ((7.9.8), which the book cites as
"(7.8.8)"), for `A ∈ ℂ^{n×n}`, `n ≥ 1`. Stated without the `sup`: every bound `M` of `‖e^{At}‖₂`
over `t > 0` has `α_ε(A) ≤ ε M`. The abscissa is attained at some `z ∈ Λ_ε(A)`; if `Re z > 0`
then `z ∉ λ(A)` and `1/ε ≤ ‖(zI - A)⁻¹‖₂ ≤ M / Re z` ((7.9.6) and the Laplace-transform bound
`norm_resolvent_le_of_norm_exp_smul_le`, which needs the bound at `t = 0` too, by continuity). -/
theorem equation_9_3_6 [NeZero n] {ε : ℝ} (hε : 0 < ε) (A : Matrix (Fin n) (Fin n) ℂ) {M : ℝ}
    (hM : ∀ t : ℝ, 0 < t → ‖exp (t • A)‖ ≤ M) :
    Chapter07.pseudospectralAbscissa ε A ≤ ε * M := by
  have hM0 : ∀ t : ℝ, 0 ≤ t → ‖exp (t • A)‖ ≤ M := by
    intro t ht
    rcases ht.eq_or_lt with rfl | ht
    · have hsm : Continuous fun t : ℝ => t • A := continuous_id.smul continuous_const
      have hc : ContinuousAt (fun t : ℝ => ‖exp (t • A)‖) 0 :=
        (((NormedSpace.exp_analytic (𝕂 := ℂ) ((0 : ℝ) • A)).continuousAt).comp
          (f := fun t : ℝ => t • A) hsm.continuousAt).norm
      exact le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall (s := Set.Ioi 0) fun t ht => hM t ht)
    · exact hM t ht
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM0 0 le_rfl)
  obtain ⟨z, hz, hre⟩ := (Chapter07.pseudospectralAbscissa_spec hε.le A).2.2.1
  rw [← hre]
  rcases le_or_gt z.re 0 with hz0 | hz0
  · exact hz0.trans (mul_nonneg hε.le hMnn)
  · obtain ⟨hns, hres⟩ := norm_resolvent_le_of_norm_exp_smul_le hM0 hz0
    have h1 := ((Chapter07.equation_7_9_6 hε A z).1 hz).resolve_left hns
    rw [Algebra.algebraMap_eq_smul_one, ← Matrix.nonsing_inv_eq_ringInverse] at hres
    have h2 : 1 / ε ≤ M / z.re := h1.trans hres
    rw [div_le_div_iff₀ hε hz0] at h2
    linarith

end Pseudospectra

/-! ### §9.3.4 Some stability issues -/

section Two

open scoped Matrix.Norms.L2Operator

/-- §9.3.4: if `A` is normal, then so is `G = R_qq(A/2^j)`, and `‖G^m‖₂ = ‖G‖₂^m` for every
`m`. -/
theorem normal_squaring [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (q j : ℕ) :
    IsStarNormal (Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A)) ∧
    ∀ m : ℕ, ‖Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A) ^ m‖ =
      ‖Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A)‖ ^ m := by
  set B := (2⁻¹ : ℂ) ^ j • A
  have hB : IsStarNormal B := ⟨by
    rw [star_smul]
    exact (hA.star_comm_self.smul_left _).smul_right _⟩
  obtain ⟨r, hr⟩ := Matrix.IsStarNormal.exists_aeval_eq_conjTranspose hB
  have hsB : star B = aeval B r := by rw [Matrix.star_eq_conjTranspose, hr]
  set Dm := aeval B (Pade.expDen ℂ q q)
  set Nm := aeval B (Pade.expNum ℂ q q)
  have hG : Pade.expApprox ℂ q q B = Dm⁻¹ * Nm := by
    rw [Pade.expApprox, Matrix.nonsing_inv_eq_ringInverse]
  -- anything commuting with `B` commutes with `G`
  have hcomm : ∀ X : Matrix (Fin n) (Fin n) ℂ, Commute X B → Commute X (Dm⁻¹ * Nm) :=
    fun X hX => (Matrix.commute_nonsing_inv_right (hX.aeval_right _)).mul_right
      (hX.aeval_right _)
  have hGB : Commute (Dm⁻¹ * Nm) B := (hcomm B (Commute.refl B)).symm
  have hGsB : Commute (Dm⁻¹ * Nm) (star B) := by
    rw [hsB]
    exact hGB.aeval_right r
  have hsGB : Commute (star (Dm⁻¹ * Nm)) B := by
    simpa only [star_star] using hGsB.star_star
  have hN : IsStarNormal (Pade.expApprox ℂ q q B) := by
    rw [hG]
    exact ⟨hcomm _ hsGB⟩
  refine ⟨hN, fun m => ?_⟩
  have hNm : IsStarNormal (Pade.expApprox ℂ q q B ^ m) := IsStarNormal.pow m
  have h1 := Matrix.l2_opNorm_eq_spectralRadius_of_isStarNormal (Pade.expApprox ℂ q q B ^ m)
  rw [spectralRadius_pow, ← Matrix.l2_opNorm_eq_spectralRadius_of_isStarNormal] at h1
  have h2 : ‖Pade.expApprox ℂ q q B ^ m‖₊ = ‖Pade.expApprox ℂ q q B‖₊ ^ m := by
    exact_mod_cast h1
  rw [← coe_nnnorm, h2, NNReal.coe_pow, coe_nnnorm]

end Two

end GolubVanLoan.Chapter09
