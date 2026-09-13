import Mathlib.Analysis.Complex.Polynomial.Basic
import Numlib.Algebra.LinearRecurrence

/-!
# Quarteroni–Sacco–Saleri §11.4: difference equations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §11.4. The book's linear difference equation of order `k` with constant
coefficients, `u_{n+k} + α_{k-1} u_{n+k-1} + … + α_0 u_n = φ_{n+k}` (11.28), is Mathlib's
`LinearRecurrence` with `coeffs i = -α_i`, and its theory — the characteristic polynomial, the
fundamental solutions `r_j^n` and `n^s r_j^n`, the Kronecker fundamental solutions `ψ_j` and the
discrete Duhamel formula — is the backbone `Numlib/Algebra/LinearRecurrence`, read here over a
field `K` (the book names none; its coefficients are real and its roots complex), with the
statements that need every root over `ℂ`.

## The equation and its characteristic polynomial

* `equation_11_28 α` — the recurrence (11.28) with coefficients `α : Fin k → K`; a sequence `u`
  solves it with right-hand side `φ` iff `(equation_11_28 α).IsSolutionWith φ u`
  (`equation_11_28_iff`), and the homogeneous equation (11.29) is `IsSolution`
  (`equation_11_29_iff`).
* `equation_11_30 α` — the characteristic polynomial `Π(r) = r^k + α_{k-1} r^{k-1} + … + α_0`,
  equal to the backbone's `charPoly` (`equation_11_30_eq`).
* `equation_11_31` — `r^n` solves (11.29) iff `r` is a root of `Π`; `equation_11_32` — every
  combination `∑_j γ_j r_j^n` of such solutions is a solution, and when the `k` roots are simple
  every solution has this form for a unique `γ` (`equation_11_32_existsUnique`).
* `equation_11_33_isSolution` — a root `r` of multiplicity `m` contributes the solutions
  `n^s r^n`, `s < m`; `equation_11_33` — over `ℂ`, with the book's standing assumption `α_0 ≠ 0`,
  every solution is `∑_j (∑_{s < m_j} γ_{sj} n^s) r_j^n`, stated with the polynomials
  `p_j = ∑_s γ_{sj} X^s` of degree `< m_j`.

## The Kronecker fundamental solutions

* `equation_11_34 α j` — the fundamental solution `ψ_j` with `ψ_j^{(i)} = δ_ij` (11.34);
  `equation_11_35` — every solution of (11.29) is `u_n = ∑_j u_j ψ_j^{(n)}`.
* `equation_11_36`, `equation_11_37` — for simple roots, `ψ_j^{(n)} = ∑_m β_{j,m} r_m^n` (11.36),
  the coefficients solving the linear system `R b_j = e_j` (11.37) with the matrix
  `R = (r_m^i)`, `equation_11_37_matrix r`, which is the transpose of Mathlib's Vandermonde
  matrix and is nonsingular for distinct roots (`equation_11_37_det_ne_zero`, Exercise 5).
* `equation_11_42` — the discrete Duhamel formula for the inhomogeneous equation (11.28),
  `u_n = ∑_j u_j ψ_j^{(n)} + ∑_{l=k}^{n} φ_l ψ_{k-1}^{(n-l+k-1)}`.

## The Examples

`example_11_3` and `example_11_4` are the closed forms of the solutions of `u_{n+2} - u_n = 0` and
of `u_{n+3} - 2u_{n+2} - 7u_{n+1} - 4u_n = 0` in terms of the initial values, with the
characteristic polynomials `r² - 1` and `(r + 1)²(r - 4)`; `example_11_5` gives the three `ψ_j` of
the latter and the matrix `R` of (11.37) for its fundamental system `(-1)^n, n(-1)^n, 4^n`;
`example_11_6` is the solution `u_n = ((-1)^n + 3^n)/n!` of the variable-coefficient equation
(11.41) with `u_0 = u_1 = 2`, verified directly (the generating-function derivation of
(11.38)–(11.40) is a technique, not a stated result, and is not formalized); `example_11_7` is the
particular solution `2^n (n²/5 - 36n/25 + 358/125)` of `u_{n+3} - u_{n+2} + u_{n+1} - u_n = 2^n n²`.

## Readings

In Example 11.5 the book writes `r_2` for the root `4` that Example 11.4 called `r_1`; the matrix
is the one printed. The general solution (11.33) needs the book's standing assumption `α_0 ≠ 0`
(for `α_0 = 0` the sequence `n^s 0^n` vanishes for `s ≥ 1`), which the backbone's fundamental
system `n.choose s * r^(n-s)` does not; the surface states the book's form.
-/

open Finset LinearRecurrence Polynomial

namespace QuarteroniSaccoSaleri.Chapter11

variable {K : Type*} [Field K] {k : ℕ}

/-! ### (11.28)–(11.30): the equation and its characteristic polynomial -/

/-- **(11.28).** The linear difference equation of order `k` with constant coefficients
`α_0, …, α_{k-1}`, `u_{n+k} + α_{k-1} u_{n+k-1} + … + α_0 u_n = φ_{n+k}`, as Mathlib's
`LinearRecurrence` with `coeffs i = -α_i`: a sequence `u` solves it iff
`(equation_11_28 α).IsSolutionWith φ u` (`equation_11_28_iff`), and the homogeneous equation
(11.29) iff `(equation_11_28 α).IsSolution u` (`equation_11_29_iff`). The book's variable
coefficients (11.38) are not formalized beyond Example 11.6. -/
def equation_11_28 (α : Fin k → K) : LinearRecurrence K :=
  ⟨k, fun i => -α i⟩

/-- The order of (11.28) is `k`. -/
@[simp]
theorem equation_11_28_order (α : Fin k → K) : (equation_11_28 α).order = k := rfl

/-- The coefficients of (11.28) in Mathlib's convention are `-α_i`. -/
@[simp]
theorem equation_11_28_coeffs (α : Fin k → K) (i : Fin k) : (equation_11_28 α).coeffs i = -α i :=
  rfl

/-- The book's phrasing of (11.28): `u` is a solution with right-hand side `φ` iff
`u_{n+k} + ∑_i α_i u_{n+i} = φ_{n+k}` for every `n`. -/
theorem equation_11_28_iff (α : Fin k → K) (φ u : ℕ → K) :
    (equation_11_28 α).IsSolutionWith φ u ↔
      ∀ n, u (n + k) + ∑ i : Fin k, α i * u (n + i) = φ (n + k) := by
  change (∀ n, u (n + k) = ∑ i : Fin k, -α i * u (n + i) + φ (n + k)) ↔ _
  simp only [neg_mul, sum_neg_distrib, ← sub_eq_neg_add, eq_sub_iff_add_eq]

/-- **(11.29).** The homogeneous equation: `u` solves it iff `u_{n+k} + ∑_i α_i u_{n+i} = 0` for
every `n`. -/
theorem equation_11_29_iff (α : Fin k → K) (u : ℕ → K) :
    (equation_11_28 α).IsSolution u ↔ ∀ n, u (n + k) + ∑ i : Fin k, α i * u (n + i) = 0 := by
  rw [← isSolutionWith_zero_iff, equation_11_28_iff]
  rfl

/-- **(11.30).** The characteristic polynomial `Π(r) = r^k + α_{k-1} r^{k-1} + … + α_1 r + α_0`
of the equation (11.28); it is the backbone's `charPoly` (`equation_11_30_eq`). -/
noncomputable def equation_11_30 (α : Fin k → K) : K[X] :=
  X ^ k + ∑ i : Fin k, C (α i) * X ^ (i : ℕ)

/-- The characteristic polynomial (11.30) is `LinearRecurrence.charPoly`. -/
theorem equation_11_30_eq (α : Fin k → K) : equation_11_30 α = (equation_11_28 α).charPoly := by
  change _ = monomial k 1 - ∑ i : Fin k, monomial (i : ℕ) (-α i)
  simp only [equation_11_30, ← C_mul_X_pow_eq_monomial, C_1, one_mul, C_neg, neg_mul,
    sum_neg_distrib, sub_neg_eq_add]

/-- The characteristic polynomial has degree `k`. -/
theorem equation_11_30_degree (α : Fin k → K) : (equation_11_30 α).degree = k := by
  rw [equation_11_30_eq, charPoly_degree_eq_order, equation_11_28_order]

/-- The constant term of the characteristic polynomial is `α_0` (for `k ≥ 1`), so the book's
standing assumption `α_0 ≠ 0` says that `0` is not a root. -/
theorem equation_11_30_eval_zero (α : Fin k → K) (hk : 0 < k) :
    (equation_11_30 α).eval 0 = α ⟨0, hk⟩ := by
  simp only [equation_11_30, eval_add, eval_pow, eval_X, zero_pow hk.ne', eval_finsetSum, eval_mul,
    eval_C, zero_add]
  rw [sum_eq_single ⟨0, hk⟩ (fun i _ hi => ?_) (by simp)]
  · simp
  · rw [zero_pow (by simpa [Fin.ext_iff] using hi), mul_zero]

/-! ### (11.31)–(11.33): the fundamental solutions -/

/-- **(11.31).** The geometric sequence `r^n` is a solution of the homogeneous equation (11.29)
iff `r` is a root of the characteristic polynomial `Π`. -/
theorem equation_11_31 (α : Fin k → K) (r : K) :
    ((equation_11_28 α).IsSolution fun n => r ^ n) ↔ (equation_11_30 α).IsRoot r := by
  rw [equation_11_30_eq, geom_sol_iff_root_charPoly]

/-- **(11.32).** Every combination `u_n = ∑_j γ_j r_j^n` of the fundamental solutions attached to
roots `r_j` of `Π` is a solution of (11.29), "since it is a linear equation". -/
theorem equation_11_32 (α : Fin k → K) {r : Fin k → K}
    (hroot : ∀ j, (equation_11_30 α).IsRoot (r j)) (γ : Fin k → K) :
    (equation_11_28 α).IsSolution fun n => ∑ j, γ j * r j ^ n := by
  have : (fun n => ∑ j, γ j * r j ^ n) = ∑ j, γ j • fun n => r j ^ n := by
    ext n; simp [Finset.sum_apply]
  rw [this, is_sol_iff_mem_solSpace]
  exact (equation_11_28 α).solSpace.sum_mem fun j _ =>
    (equation_11_28 α).solSpace.smul_mem _ ((equation_11_31 α (r j)).2 (hroot j))

/-- **(11.32), the converse** (Exercise 4 of chapter 11): if all the roots `r_0, …, r_{k-1}` of `Π`
are simple — that is, if `r : Fin k → K` enumerates `k` distinct roots — then every solution of
(11.29) has the form (11.32), `u_n = ∑_j γ_j r_j^n`, for a unique `γ`, determined by the initial
values `u_0, …, u_{k-1}` through the Vandermonde system (11.37). -/
theorem equation_11_32_existsUnique (α : Fin k → K) {r : Fin k → K} (hr : Function.Injective r)
    (hroot : ∀ j, (equation_11_30 α).IsRoot (r j)) {u : ℕ → K}
    (hu : (equation_11_28 α).IsSolution u) :
    ∃! γ : Fin k → K, ∀ n, u n = ∑ j, γ j * r j ^ n := by
  have h := (equation_11_28 α).eq_sum_smul_pow_of_injective_roots hr
    (fun j => (equation_11_30_eq α) ▸ hroot j) hu
  simp only [smul_eq_mul] at h
  exact h

/-- **(11.33), the multiple-root fundamental solutions.** If `r_j` is a root of `Π` of multiplicity
`m ≥ 1`, the `m` sequences `r_j^n, n r_j^n, …, n^{m-1} r_j^n` are solutions of (11.29). -/
theorem equation_11_33_isSolution (α : Fin k → K) {r : K} {s : ℕ}
    (hs : s < (equation_11_30 α).rootMultiplicity r) :
    (equation_11_28 α).IsSolution fun n => (n : K) ^ s * r ^ n :=
  (equation_11_28 α).isSolution_pow_mul_pow (equation_11_30_eq α ▸ hs)

/-- **(11.33).** Over `ℂ`, with the book's standing assumption `α_0 ≠ 0`, every solution of the
homogeneous equation (11.29) is `u_n = ∑_j (∑_{s < m_j} γ_{sj} n^s) r_j^n`, the sum over the
distinct roots `r_j` of `Π` with multiplicities `m_j`: here as `u_n = ∑_j p_j(n) r_j^n` with
polynomials `p_j` of degree `< m_j`, `γ_{sj}` being the coefficient of `X^s` in `p_j`. -/
theorem equation_11_33 (α : Fin k → ℂ) (hk : 0 < k) (h0 : α ⟨0, hk⟩ ≠ 0) {u : ℕ → ℂ}
    (hu : (equation_11_28 α).IsSolution u) :
    ∃ p : ℂ → ℂ[X], (∀ r, (p r).degree < ((equation_11_30 α).rootMultiplicity r : WithBot ℕ)) ∧
      ∀ n, u n = ∑ r ∈ (equation_11_30 α).roots.toFinset, (p r).eval (n : ℂ) * r ^ n := by
  rw [equation_11_30_eq]
  refine (equation_11_28 α).exists_eq_sum_eval_mul_pow_of_splits (IsAlgClosed.splits _) ?_ hu
  rw [IsRoot.def, ← equation_11_30_eq, equation_11_30_eval_zero α hk]
  exact h0

/-! ### Examples 11.3 and 11.4 -/

/-- **Example 11.3, the characteristic polynomial.** For `u_{n+2} - u_n = 0`, `Π(r) = r² - 1`,
with roots `r_0 = -1` and `r_1 = 1`. -/
theorem example_11_3_charPoly : equation_11_30 (K := ℝ) ![-1, 0] = X ^ 2 - 1 := by
  simp [equation_11_30, Fin.sum_univ_two]
  ring

/-- **Example 11.3.** The solution of `u_{n+2} - u_n = 0` with initial values `u_0, u_1` is
`u_n = γ_00 (-1)^n + γ_01` with `γ_00 = (u_0 - u_1)/2` and `γ_01 = (u_0 + u_1)/2`. -/
theorem example_11_3 {u : ℕ → ℝ} (hu : (equation_11_28 ![-1, 0]).IsSolution u) (n : ℕ) :
    u n = (u 0 - u 1) / 2 * (-1) ^ n + (u 0 + u 1) / 2 := by
  have hv : (equation_11_28 ![-1, 0]).IsSolution
      fun n => (u 0 - u 1) / 2 * (-1 : ℝ) ^ n + (u 0 + u 1) / 2 := by
    rw [equation_11_29_iff]
    intro n
    simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero]
    ring
  refine congrFun (((equation_11_28 _).eq_iff_eqOn_range_order u _ hu hv).2 fun i hi => ?_) n
  rw [coe_range, Set.mem_Iio, equation_11_28_order] at hi
  interval_cases i <;> simp <;> ring

/-- **Example 11.4, the characteristic polynomial.** For `u_{n+3} - 2u_{n+2} - 7u_{n+1} - 4u_n = 0`,
`Π(r) = r³ - 2r² - 7r - 4 = (r + 1)²(r - 4)`: the roots are `r_0 = -1` with multiplicity `2` and
`r_1 = 4`. -/
theorem example_11_4_charPoly :
    equation_11_30 (K := ℝ) ![-4, -7, -2] = X ^ 3 - 2 * X ^ 2 - 7 * X - 4 ∧
      equation_11_30 (K := ℝ) ![-4, -7, -2] = (X + 1) ^ 2 * (X - 4) := by
  have : equation_11_30 (K := ℝ) ![-4, -7, -2] = X ^ 3 - 2 * X ^ 2 - 7 * X - 4 := by
    simp [equation_11_30, Fin.sum_univ_three, map_ofNat]
    ring
  exact ⟨this, this.trans (by ring)⟩

/-- **Example 11.4.** The solution of `u_{n+3} - 2u_{n+2} - 7u_{n+1} - 4u_n = 0` with initial
values `u_0, u_1, u_2` is `u_n = (γ_00 + n γ_10)(-1)^n + γ_01 4^n` with
`γ_00 = (24u_0 - 2u_1 - u_2)/25`, `γ_10 = (u_2 - 3u_1 - 4u_0)/5` and
`γ_01 = (2u_1 + u_0 + u_2)/25`, the solution of the linear system of the initial conditions. -/
theorem example_11_4 {u : ℕ → ℝ} (hu : (equation_11_28 ![-4, -7, -2]).IsSolution u) (n : ℕ) :
    u n = ((24 * u 0 - 2 * u 1 - u 2) / 25 + n * ((u 2 - 3 * u 1 - 4 * u 0) / 5)) * (-1) ^ n +
      (2 * u 1 + u 0 + u 2) / 25 * 4 ^ n := by
  have hv : (equation_11_28 ![-4, -7, -2]).IsSolution fun n : ℕ =>
      ((24 * u 0 - 2 * u 1 - u 2) / 25 + n * ((u 2 - 3 * u 1 - 4 * u 0) / 5)) * (-1 : ℝ) ^ n +
        (2 * u 1 + u 0 + u 2) / 25 * 4 ^ n := by
    rw [equation_11_29_iff]
    intro n
    simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
      Fin.val_two, add_zero]
    push_cast
    ring
  refine congrFun (((equation_11_28 _).eq_iff_eqOn_range_order u _ hu hv).2 fun i hi => ?_) n
  rw [coe_range, Set.mem_Iio, equation_11_28_order] at hi
  interval_cases i <;> simp <;> ring

/-! ### (11.34)–(11.37): the Kronecker fundamental solutions -/

/-- **(11.34).** The fundamental solutions `ψ_j`, `j = 0, …, k-1`, of the homogeneous equation
(11.29) with the Kronecker initial data `ψ_j^{(i)} = δ_ij`, `i, j = 0, …, k-1`: the backbone's
`LinearRecurrence.kroneckerSol`. -/
noncomputable def equation_11_34 (α : Fin k → K) (j : Fin k) : ℕ → K :=
  (equation_11_28 α).kroneckerSol j

/-- The `ψ_j` are solutions of (11.29). -/
theorem equation_11_34_isSolution (α : Fin k → K) (j : Fin k) :
    (equation_11_28 α).IsSolution (equation_11_34 α j) :=
  (equation_11_28 α).isSolution_kroneckerSol j

/-- The Kronecker initial data (11.34): `ψ_j^{(i)} = δ_ij` for `i, j < k`. -/
theorem equation_11_34_apply_of_lt (α : Fin k → K) (j : Fin k) {i : ℕ} (hi : i < k) :
    equation_11_34 α j i = if i = j then 1 else 0 :=
  (equation_11_28 α).kroneckerSol_apply_of_lt j hi

/-- The Kronecker initial data (11.34): `ψ_j^{(i)} = δ_ij` for `i, j < k`. -/
theorem equation_11_34_apply (α : Fin k → K) (i j : Fin k) :
    equation_11_34 α j i = if i = j then 1 else 0 := by
  rw [equation_11_34_apply_of_lt α j i.is_lt]
  simp [Fin.ext_iff]

/-- **(11.35).** The solution of (11.29) with initial values `u_0, …, u_{k-1}` is
`u_n = ∑_{j=0}^{k-1} u_j ψ_j^{(n)}`. -/
theorem equation_11_35 (α : Fin k → K) {u : ℕ → K} (hu : (equation_11_28 α).IsSolution u) (n : ℕ) :
    u n = ∑ j : Fin k, u j * equation_11_34 α j n :=
  (equation_11_28 α).eq_sum_kroneckerSol hu n

/-- **(11.37), the matrix.** `R = (r_{im}) = (r_m^i)`, `i, m = 0, …, k-1`: the transpose of
Mathlib's Vandermonde matrix `(r_i^m)`. -/
def equation_11_37_matrix (r : Fin k → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i m => r m ^ (i : ℕ)

/-- The matrix `R` of (11.37) is the transpose of Mathlib's `Matrix.vandermonde r`. -/
theorem equation_11_37_matrix_eq (r : Fin k → K) :
    equation_11_37_matrix r = (Matrix.vandermonde r).transpose := rfl

/-- **Exercise 5 of chapter 11.** If the `r_m` are distinct — all the roots of `Π` are simple —
the matrix `R` is nonsingular. -/
theorem equation_11_37_det_ne_zero {r : Fin k → K} (hr : Function.Injective r) :
    (equation_11_37_matrix r).det ≠ 0 :=
  det_vandermonde_transpose_ne_zero hr

/-- **(11.36).** For simple roots `r_0, …, r_{k-1}` of `Π`, each Kronecker fundamental solution is
a combination of the geometric ones: `ψ_j^{(n)} = ∑_{m=0}^{k-1} β_{j,m} r_m^n` for a unique row
`b_j = (β_{j,0}, …, β_{j,k-1})`. -/
theorem equation_11_36 (α : Fin k → K) {r : Fin k → K} (hr : Function.Injective r)
    (hroot : ∀ j, (equation_11_30 α).IsRoot (r j)) (j : Fin k) :
    ∃! β : Fin k → K, ∀ n, equation_11_34 α j n = ∑ m, β m * r m ^ n :=
  equation_11_32_existsUnique α hr hroot (equation_11_34_isSolution α j)

/-- **(11.37).** The coefficients `b_j` of (11.36) are characterized by the Kronecker initial data
(11.34): they solve the `k` linear systems `R b_j = e_j`, `j = 0, …, k-1`, with `R = (r_m^i)`
and `e_j` the `j`-th unit vector. -/
theorem equation_11_37 (α : Fin k → K) (r : Fin k → K) (j : Fin k) (β : Fin k → K)
    (hβ : ∀ n, equation_11_34 α j n = ∑ m, β m * r m ^ n) :
    (equation_11_37_matrix r).mulVec β = Pi.single j 1 := by
  ext i
  have := hβ i
  rw [equation_11_34_apply] at this
  simp only [equation_11_37_matrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.single_apply]
  rw [this]
  exact sum_congr rfl fun m _ => mul_comm _ _

/-! ### Example 11.5 -/

/-- **Example 11.5, the matrix.** For the equation of Example 11.4, whose fundamental system is
`(-1)^n, n(-1)^n, 4^n`, the matrix `R` of (11.37) becomes
`R = [[r_0^0, 0, r_2^0], [r_0^1, r_0^1, r_2^1], [r_0^2, 2 r_0^2, r_2^2]]`, that is,
`[[1, 0, 1], [-1, -1, 4], [1, 2, 16]]` (the book writes `r_2` for the root `4`). -/
theorem example_11_5_matrix :
    (Matrix.of fun i m : Fin 3 => ![(-1 : ℝ) ^ (i : ℕ), i * (-1) ^ (i : ℕ), 4 ^ (i : ℕ)] m) =
      !![1, 0, 1; -1, -1, 4; 1, 2, 16] := by
  ext i m
  fin_cases i <;> fin_cases m <;> norm_num

/-- **Example 11.5.** For the equation `u_{n+3} - 2u_{n+2} - 7u_{n+1} - 4u_n = 0` of Example 11.4,
solving the three systems (11.37) yields the fundamental solutions
`ψ_0^{(n)} = (24/25)(-1)^n - (4/5) n (-1)^n + (1/25) 4^n`,
`ψ_1^{(n)} = -(2/25)(-1)^n - (3/5) n (-1)^n + (2/25) 4^n` and
`ψ_2^{(n)} = -(1/25)(-1)^n + (1/5) n (-1)^n + (1/25) 4^n`, from which `u_n = ∑_j u_j ψ_j^{(n)}`
(`equation_11_35`) is the solution found in Example 11.4 (`example_11_4`). -/
theorem example_11_5 (n : ℕ) :
    equation_11_34 (K := ℝ) ![-4, -7, -2] 0 n =
        24 / 25 * (-1) ^ n - 4 / 5 * n * (-1) ^ n + 1 / 25 * 4 ^ n ∧
      equation_11_34 (K := ℝ) ![-4, -7, -2] 1 n =
        -(2 / 25) * (-1) ^ n - 3 / 5 * n * (-1) ^ n + 2 / 25 * 4 ^ n ∧
      equation_11_34 (K := ℝ) ![-4, -7, -2] 2 n =
        -(1 / 25) * (-1) ^ n + 1 / 5 * n * (-1) ^ n + 1 / 25 * 4 ^ n := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [example_11_4 (equation_11_34_isSolution _ _) n,
      equation_11_34_apply_of_lt _ _ (by norm_num : (0 : ℕ) < 3),
      equation_11_34_apply_of_lt _ _ (by norm_num : (1 : ℕ) < 3),
      equation_11_34_apply_of_lt _ _ (by norm_num : (2 : ℕ) < 3)]
    norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring

/-! ### Example 11.6: a variable-coefficient equation -/

/-- **Example 11.6.** The difference equation (11.41),
`(n+2)(n+1) u_{n+2} - 2(n+1) u_{n+1} - 3 u_n = 0`, with the initial conditions `u_0 = u_1 = 2`
has the solution `u_n = ((-1)^n + 3^n)/n!` — the coefficients of the generating function
`F(t) = e^{3t} + e^{-t}`, which solves `F'' - 2F' - 3F = 0` with `F(0) = F'(0) = 2`. Verified
directly: the closed form satisfies the recurrence and the initial conditions, and the recurrence
determines `u_{n+2}` since its leading coefficient `(n+2)(n+1)` is nonzero. -/
theorem example_11_6 {u : ℕ → ℝ}
    (hu : ∀ n : ℕ, ((n : ℝ) + 2) * (n + 1) * u (n + 2) - 2 * (n + 1) * u (n + 1) - 3 * u n = 0)
    (h0 : u 0 = 2) (h1 : u 1 = 2) (n : ℕ) : u n = ((-1) ^ n + 3 ^ n) / n.factorial := by
  set v : ℕ → ℝ := fun n => ((-1) ^ n + 3 ^ n) / n.factorial with hv
  have hstep : ∀ n : ℕ, u n = v n → u (n + 1) = v (n + 1) → u (n + 2) = v (n + 2) := by
    intro n hn hn1
    have h := hu n
    rw [hn, hn1] at h
    have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    have hpos : ((n : ℝ) + 2) * (n + 1) ≠ 0 := by positivity
    simp only [hv, Nat.factorial_succ] at h ⊢
    push_cast at h ⊢
    field_simp at h ⊢
    linear_combination h
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by norm_num [hv, h0], by norm_num [hv, h1]⟩
    | succ n ih => exact ⟨ih.2, hstep n ih.1 ih.2⟩
  exact (key n).1

/-! ### Example 11.7: the method of undetermined coefficients -/

/-- **Example 11.7.** `u_n = 2^n (b_2 n² + b_1 n + b_0)` with `b_2 = 1/5`, `b_1 = -36/25` and
`b_0 = 358/125` is a particular solution of `u_{n+3} - u_{n+2} + u_{n+1} - u_n = 2^n n²`:
substituting the ansatz gives `5b_2 n² + (36b_2 + 5b_1) n + (58b_2 + 18b_1 + 5b_0) = n²`, and the
principle of identity for polynomials determines the coefficients. -/
theorem example_11_7 (n : ℕ) :
    let u : ℕ → ℝ := fun n => 2 ^ n * ((n : ℝ) ^ 2 / 5 - 36 * n / 25 + 358 / 125)
    u (n + 3) - u (n + 2) + u (n + 1) - u n = 2 ^ n * (n : ℝ) ^ 2 := by
  intro u
  simp only [u]
  push_cast
  ring

/-- Example 11.7 in the form (11.28): the particular solution solves the equation with
`α = (-1, 1, -1)` and right-hand side `φ_{n+3} = 2^n n²`. -/
theorem example_11_7_isSolutionWith :
    (equation_11_28 ![-1, 1, -1]).IsSolutionWith
      (fun m => 2 ^ (m - 3) * ((m : ℝ) - 3) ^ 2)
      (fun n => 2 ^ n * ((n : ℝ) ^ 2 / 5 - 36 * n / 25 + 358 / 125)) := by
  rw [equation_11_28_iff]
  intro n
  simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two,
    add_zero, Nat.add_sub_cancel]
  push_cast
  ring

/-! ### (11.42): the inhomogeneous equation -/

/-- **(11.42).** The solution of the inhomogeneous equation (11.28) of order `k ≥ 1` is
`u_n = ∑_{j=0}^{k-1} u_j ψ_j^{(n)} + ∑_{l=k}^{n} φ_l ψ_{k-1}^{(n-l+k-1)}`, where `ψ_{k-1}^{(i)} = 0`
for `i < 0` and `φ_j = 0` for `j < k`: the second sum runs over `l ≤ n` only, so that its index is
a natural number, and the values `φ_j`, `j < k`, are never read. -/
theorem equation_11_42 (α : Fin k → K) (hk : 0 < k) {φ u : ℕ → K}
    (hu : (equation_11_28 α).IsSolutionWith φ u) (n : ℕ) :
    u n = (∑ j : Fin k, u j * equation_11_34 α j n) +
      ∑ l ∈ Icc k n, φ l * equation_11_34 α ⟨k - 1, by omega⟩ (n - l + (k - 1)) :=
  eq_sum_kroneckerSol_add_sum hk hu n

end QuarteroniSaccoSaleri.Chapter11
