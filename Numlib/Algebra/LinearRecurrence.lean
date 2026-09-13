import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Closed forms for linear recurrences with constant coefficients

Upstreaming candidate; natural home: `Mathlib.Algebra.LinearRecurrence`.

Mathlib's `LinearRecurrence R` is the relation `u (n + k) = ∑ i : Fin k, coeffs i * u (n + i)` with
its solution space `solSpace` (a submodule of `ℕ → R` of rank `k`, `solSpace_rank`), the solution
`mkSol init` with prescribed initial data, and the characteristic polynomial
`charPoly = X ^ k - ∑ i, coeffs i * X ^ i` with `geom_sol_iff_root_charPoly`: the geometric sequence
`q ^ n` is a solution iff `q` is a root. Its header says that closed forms are "currently not
implemented"; this module implements the part that the theory of linear difference equations
needs, [quarteroni2000numerical] §11.4 being the account followed.

## Contents

* **The inhomogeneous recurrence.** `IsSolutionWith φ u` is
  `u (n + k) = ∑ i, coeffs i * u (n + i) + φ (n + k)`, the book's (11.28) with source `φ` indexed
  at `n + k`; `mkSolWith φ init` is its solution with initial data `init`, unique
  (`eq_mkSolWith_of_isSolutionWith_of_eq_init`), and the solutions with a given source form a coset
  of `solSpace` (`isSolutionWith_sub`, `isSolutionWith_add`).
* **The Kronecker fundamental solutions** `kroneckerSol j = mkSol (Pi.single j 1)`, with
  `ψ_j (i) = δ_ij` for `i < k` (the book's (11.34)); every solution is
  `u n = ∑ j, u j * ψ_j n` (`eq_sum_kroneckerSol`, (11.35)), and every solution of the
  inhomogeneous recurrence is that plus the discrete convolution
  `∑_{l = k}^{n} φ l * ψ_{k-1} (n - l + (k - 1))` of the source with the last fundamental solution
  (`eq_sum_kroneckerSol_add_sum`, the discrete Duhamel formula (11.42)).
* **The solutions attached to a root of multiplicity `m`.** Two families are provided, both valid
  over every commutative ring. The book's sequences `n ^ s * q ^ n`, `s < m`, are solutions
  (`isSolution_pow_mul_pow`; `isSolution_mul_pow_of_one_lt_rootMultiplicity` is the case `s = 1`).
  The *binomial* sequences `chooseMulPow q s = n ↦ n.choose s * q ^ (n - s)`, the `s`-th Hasse
  derivative of `q ↦ q ^ n`, are solutions as well (`isSolution_chooseMulPow`), and they are the
  family used for the basis, because they behave uniformly at the root `q = 0` — where
  `chooseMulPow 0 s` is the Kronecker sequence `δ_{n s}` while `n ^ s * 0 ^ n` is the zero sequence
  for `s ≥ 1` — and because the shift `S u = u (· + 1)` lowers them, `(S - q) e_s = e_{s-1}`,
  which is what makes their independence a triangular computation.
* **The fundamental system (11.33).** Over a field, `RootIndex` is the set of pairs `(r, s)` with
  `r` a root of the characteristic polynomial and `s < rootMultiplicity r`, and
  `fundamentalSol (r, s) = chooseMulPow r s`. The family is linearly independent
  (`linearIndependent_fundamentalSol`: the pieces at distinct roots lie in distinct generalized
  eigenspaces of the shift, `Module.End.independent_genEigenspace`) and, when the characteristic
  polynomial splits, it spans `solSpace` (`span_fundamentalSol_eq_solSpace`: a dimension count,
  `card RootIndex = ∑ mult = card roots = order`). Neither statement needs `CharZero` or a nonzero
  constant coefficient. The book's form of the general solution, `∑_j p_j (n) r_j ^ n` with
  `deg p_j < m_j`, is `exists_eq_sum_eval_mul_pow_of_splits`, which needs both (the binomial
  coefficient is a polynomial in `n` only in characteristic zero, and `n ^ s * 0 ^ n` vanishes).
* **Simple roots (11.32), (11.37).** The matrix `R = (r_m ^ i)` of the book is the transpose of
  Mathlib's `Matrix.vandermonde`, nonsingular for distinct `r_m`
  (`det_vandermonde_transpose_ne_zero`); when the `k` distinct roots `r_j` are given, every solution
  is `∑ j, γ j • r j ^ n` for a unique `γ`, the solution of the Vandermonde system
  (`eq_sum_smul_pow_of_injective_roots`).

## Conventions

Mathlib's: `IsSolution u ↔ ∀ n, u (n + k) = ∑ i : Fin k, coeffs i * u (n + i)`, so the book's
`u_{n+k} + α_{k-1} u_{n+k-1} + … + α_0 u_n = 0` has `coeffs i = -α_i`, and `charPoly` is the book's
`Π`. The sequences are indexed by `ℕ`; the book's `ψ_{k-1}^{(i)} = 0` for `i < 0` in (11.42) is
encoded by summing over `l ∈ Icc k n` only, where `n - l + (k - 1)` is an honest natural number.

The polynomial lemmas at the top (`Polynomial.eulerOp`, the vanishing of Hasse derivatives and of
iterated Euler operators at a multiple root) are Mathlib-shaped and independent of recurrences.
-/

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- If `(X - C a) ^ m ∣ p`, the Hasse derivatives of `p` of order `< m` vanish at `a`: the Taylor
expansion of `p` at `a` starts at order `m`. -/
theorem eval_hasseDeriv_eq_zero_of_pow_sub_dvd {p : R[X]} {a : R} {m s : ℕ}
    (h : (X - C a) ^ m ∣ p) (hs : s < m) : (hasseDeriv s p).eval a = 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [← taylor_coeff, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right,
    coeff_X_pow_mul']
  simp [not_le.mpr hs]

/-- The Hasse derivatives of order `< rootMultiplicity a p` vanish at `a`. -/
theorem eval_hasseDeriv_eq_zero_of_lt_rootMultiplicity {p : R[X]} {a : R} {s : ℕ}
    (hs : s < p.rootMultiplicity a) : (hasseDeriv s p).eval a = 0 :=
  eval_hasseDeriv_eq_zero_of_pow_sub_dvd (p.pow_rootMultiplicity_dvd a) hs

/-- The Euler operator `θ p = X * p'`, as a linear map. It multiplies the monomial `X ^ n` by `n`,
so `θ ^ s` multiplies it by `n ^ s`: it is the operator behind the sequences `n ^ s * q ^ n`. -/
noncomputable def eulerOp : R[X] →ₗ[R] R[X] :=
  (LinearMap.mulLeft R (X : R[X])).comp derivative

/-- The Euler operator is `X` times the derivative. -/
theorem eulerOp_apply (p : R[X]) : eulerOp p = X * derivative p := rfl

/-- The Euler operator multiplies the monomial `X ^ n` by `n`. -/
@[simp]
theorem eulerOp_monomial (n : ℕ) (a : R) : eulerOp (monomial n a) = monomial n (n * a) := by
  rw [eulerOp_apply, derivative_monomial]
  rcases n with _ | n
  · simp
  · rw [X_mul_monomial, Nat.add_sub_cancel, mul_comm]

/-- The `s`-th iterate of the Euler operator multiplies the monomial `X ^ n` by `n ^ s`. -/
theorem iterate_eulerOp_monomial (s n : ℕ) (a : R) :
    (⇑eulerOp)^[s] (monomial n a) = monomial n ((n : R) ^ s * a) := by
  induction s generalizing a with
  | zero => simp
  | succ s ih => rw [Function.iterate_succ_apply, eulerOp_monomial, ih, pow_succ]; ring_nf

/-- The Euler operator lowers the multiplicity of a factor by at most one. -/
theorem pow_sub_one_dvd_eulerOp_of_pow_dvd {p q : R[X]} {n : ℕ} (h : q ^ n ∣ p) :
    q ^ (n - 1) ∣ eulerOp p :=
  (pow_sub_one_dvd_derivative_of_pow_dvd h).mul_left _

/-- The `s`-th iterate of the Euler operator lowers the multiplicity of a factor by at most `s`. -/
theorem pow_sub_dvd_iterate_eulerOp_of_pow_dvd {p q : R[X]} {n : ℕ} (s : ℕ) (h : q ^ n ∣ p) :
    q ^ (n - s) ∣ (⇑eulerOp)^[s] p := by
  induction s generalizing p with
  | zero => simpa
  | succ s ih =>
    rw [Function.iterate_succ_apply', Nat.sub_succ']
    exact pow_sub_one_dvd_eulerOp_of_pow_dvd (ih h)

/-- If `(X - C a) ^ m ∣ p`, the iterated Euler operators `θ ^ s p`, `s < m`, vanish at `a`. -/
theorem eval_iterate_eulerOp_eq_zero_of_pow_sub_dvd {p : R[X]} {a : R} {m s : ℕ}
    (h : (X - C a) ^ m ∣ p) (hs : s < m) : ((⇑eulerOp)^[s] p).eval a = 0 := by
  have := pow_sub_dvd_iterate_eulerOp_of_pow_dvd s h
  exact dvd_iff_isRoot.mp ((dvd_pow_self _ (Nat.sub_ne_zero_of_lt hs)).trans this)

end Polynomial

namespace LinearRecurrence

/-! ### The inhomogeneous recurrence -/

section CommSemiring

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

/-- `u` solves the inhomogeneous recurrence with source `φ`:
`u (n + k) = ∑ i, coeffs i * u (n + i) + φ (n + k)` for every `n`, where `k` is the order. This is
the linear difference equation `u_{n+k} + α_{k-1} u_{n+k-1} + … + α_0 u_n = φ_{n+k}` of
[quarteroni2000numerical] (11.28), with `coeffs i = -α_i`; the source is indexed at `n + k` as in
the book, so that `φ 0, …, φ (k - 1)` are never read. -/
def IsSolutionWith (φ u : ℕ → R) : Prop :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i) + φ (n + E.order)

/-- The inhomogeneous recurrence with source `0` is the homogeneous one. -/
@[simp]
theorem isSolutionWith_zero_iff (u : ℕ → R) : E.IsSolutionWith 0 u ↔ E.IsSolution u := by
  simp [IsSolutionWith, IsSolution]

/-- The solution of the inhomogeneous recurrence with source `φ` and initial values `init`,
computed by the recursion `u (n + k) = ∑ i, coeffs i * u (n + i) + φ (n + k)`; the unique such
solution (`eq_mkSolWith_of_isSolutionWith_of_eq_init'`). -/
def mkSolWith (φ : ℕ → R) (init : Fin E.order → R) : ℕ → R
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      (∑ k : Fin E.order,
        have _ : n - E.order + k < n := by omega
        E.coeffs k * mkSolWith φ init (n - E.order + k)) + φ n

/-- `mkSolWith φ init` solves the inhomogeneous recurrence with source `φ`. -/
theorem isSolutionWith_mkSolWith (φ : ℕ → R) (init : Fin E.order → R) :
    E.IsSolutionWith φ (E.mkSolWith φ init) := by
  intro n
  rw [mkSolWith]
  simp

/-- The first `E.order` values of `mkSolWith φ init` are `init`. -/
theorem mkSolWith_eq_init (φ : ℕ → R) (init : Fin E.order → R) (n : Fin E.order) :
    E.mkSolWith φ init n = init n := by
  rw [mkSolWith]
  simp only [n.is_lt, dite_eq_left, Fin.mk_val]

/-- Uniqueness for the inhomogeneous recurrence, pointwise: a solution with source `φ` whose first
`E.order` values are `init` is `mkSolWith φ init` at every `n`. -/
theorem eq_mkSolWith_of_isSolutionWith_of_eq_init {φ u : ℕ → R} {init : Fin E.order → R}
    (h : E.IsSolutionWith φ u) (heq : ∀ n : Fin E.order, u n = init n) :
    ∀ n, u n = E.mkSolWith φ init n := by
  intro n
  rw [mkSolWith]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  · dsimp only
    rw [← tsub_add_cancel_of_le (le_of_not_gt h'), h (n - E.order)]
    congr 1
    congr with k
    rw [eq_mkSolWith_of_isSolutionWith_of_eq_init h heq (n - E.order + k)]
    simp

/-- Uniqueness for the inhomogeneous recurrence: a solution with source `φ` whose first `E.order`
values are `init` is `mkSolWith φ init`. -/
theorem eq_mkSolWith_of_isSolutionWith_of_eq_init' {φ u : ℕ → R} {init : Fin E.order → R}
    (h : E.IsSolutionWith φ u) (heq : ∀ n : Fin E.order, u n = init n) :
    u = E.mkSolWith φ init :=
  funext (E.eq_mkSolWith_of_isSolutionWith_of_eq_init h heq)

variable {E} in
/-- Two solutions with the same source and the same first `E.order` values are equal. -/
theorem IsSolutionWith.eq_of_eqOn_range_order {φ u v : ℕ → R} (hu : E.IsSolutionWith φ u)
    (hv : E.IsSolutionWith φ v) (h : ∀ n : Fin E.order, u n = v n) : u = v :=
  (E.eq_mkSolWith_of_isSolutionWith_of_eq_init' hu (init := fun n => v n) h).trans
    (E.eq_mkSolWith_of_isSolutionWith_of_eq_init' hv fun _ => rfl).symm

/-- Adding a solution of the homogeneous recurrence to a solution with source `φ` gives a solution
with source `φ`. -/
theorem isSolutionWith_add {φ u w : ℕ → R} (hu : E.IsSolutionWith φ u) (hw : E.IsSolution w) :
    E.IsSolutionWith φ (u + w) := by
  intro n
  simp only [Pi.add_apply, hu n, hw n, mul_add, sum_add_distrib]
  ring

/-! ### The Kronecker fundamental solutions -/

/-- The fundamental solution `ψ_j` with Kronecker initial data `ψ_j (i) = δ_ij`, `i, j < k`
([quarteroni2000numerical] (11.34)). -/
noncomputable def kroneckerSol (j : Fin E.order) : ℕ → R :=
  E.mkSol (Pi.single j 1)

/-- The Kronecker fundamental solutions are solutions. -/
theorem isSolution_kroneckerSol (j : Fin E.order) : E.IsSolution (E.kroneckerSol j) :=
  E.is_sol_mkSol _

/-- The Kronecker initial data (11.34): `ψ_j (i) = δ_ij` for `i < k`. -/
theorem kroneckerSol_apply_of_lt (j : Fin E.order) {i : ℕ} (hi : i < E.order) :
    E.kroneckerSol j i = if i = j then 1 else 0 := by
  have := E.mkSol_eq_init (Pi.single j 1) ⟨i, hi⟩
  rw [kroneckerSol, this, Pi.single_apply]
  simp only [Fin.ext_iff]

/-- `ψ_j (j) = 1`. -/
@[simp]
theorem kroneckerSol_apply_self (j : Fin E.order) : E.kroneckerSol j j = 1 := by
  simp [E.kroneckerSol_apply_of_lt j j.is_lt]

/-- `ψ_j (i) = 0` for `i < k`, `i ≠ j`. -/
theorem kroneckerSol_apply_of_ne (j : Fin E.order) {i : ℕ} (hi : i < E.order) (hij : i ≠ j) :
    E.kroneckerSol j i = 0 := by
  simp [E.kroneckerSol_apply_of_lt j hi, hij]

/-- A combination of the Kronecker fundamental solutions has the coefficients as its first
`E.order` values. -/
theorem sum_mul_kroneckerSol_apply_of_lt (c : Fin E.order → R) {i : ℕ} (hi : i < E.order) :
    ∑ j : Fin E.order, c j * E.kroneckerSol j i = c ⟨i, hi⟩ := by
  rw [sum_eq_single ⟨i, hi⟩ (fun j _ hj => ?_) (by simp)]
  · rw [E.kroneckerSol_apply_of_lt _ hi]
    simp
  · rw [E.kroneckerSol_apply_of_ne j hi fun h => hj (Fin.ext h.symm), mul_zero]

/-- A combination of the Kronecker fundamental solutions is a solution. -/
theorem isSolution_sum_mul_kroneckerSol (c : Fin E.order → R) :
    E.IsSolution fun n => ∑ j : Fin E.order, c j * E.kroneckerSol j n := by
  have : (fun n => ∑ j : Fin E.order, c j * E.kroneckerSol j n) =
      ∑ j : Fin E.order, c j • E.kroneckerSol j := by
    ext n; simp [Finset.sum_apply]
  rw [this, is_sol_iff_mem_solSpace]
  exact E.solSpace.sum_mem fun j _ => E.solSpace.smul_mem (c j) (E.isSolution_kroneckerSol j)

/-- Every solution is the combination of the Kronecker fundamental solutions weighted by its
initial values: `u n = ∑ j, u j * ψ_j n` ([quarteroni2000numerical] (11.35)). -/
theorem eq_sum_kroneckerSol {u : ℕ → R} (hu : E.IsSolution u) (n : ℕ) :
    u n = ∑ j : Fin E.order, u j * E.kroneckerSol j n := by
  refine congrFun ((E.eq_iff_eqOn_range_order u _ hu
    (E.isSolution_sum_mul_kroneckerSol fun j => u j)).2 fun i hi => ?_) n
  rw [coe_range, Set.mem_Iio] at hi
  dsimp only
  rw [E.sum_mul_kroneckerSol_apply_of_lt _ hi]

/-! ### The discrete Duhamel formula -/

section Duhamel

variable {E} {φ : ℕ → R} (hk : 0 < E.order)
include hk

/-- The convolution part of the Duhamel formula, in the form `n + (k - 1) - l` of the index that
makes the extension by zero transparent. -/
private theorem duhamel_conv_succ (m : ℕ) :
    ∑ l ∈ Icc E.order (m + E.order),
        φ l * E.kroneckerSol ⟨E.order - 1, by omega⟩ (m + E.order + (E.order - 1) - l) =
      ∑ i : Fin E.order, E.coeffs i * ∑ l ∈ Icc E.order (m + i),
        φ l * E.kroneckerSol ⟨E.order - 1, by omega⟩ (m + i + (E.order - 1) - l) +
      φ (m + E.order) := by
  set ψ := E.kroneckerSol ⟨E.order - 1, by omega⟩ with hψ
  have hψ1 : ψ (E.order - 1) = 1 := E.kroneckerSol_apply_self _
  have hψ0 : ∀ i, i < E.order - 1 → ψ i = 0 := fun i hi =>
    E.kroneckerSol_apply_of_ne _ (by omega) (by simp; omega)
  have hsol : E.IsSolution ψ := E.isSolution_kroneckerSol _
  rw [show m + E.order = m + (E.order - 1) + 1 by omega, sum_Icc_succ_top (by omega),
    show m + (E.order - 1) + 1 + (E.order - 1) - (m + (E.order - 1) + 1) = E.order - 1 by omega,
    hψ1, mul_one]
  congr 1
  calc ∑ l ∈ Icc E.order (m + (E.order - 1)), φ l * ψ (m + (E.order - 1) + 1 + (E.order - 1) - l)
      = ∑ l ∈ Icc E.order (m + (E.order - 1)),
          ∑ i : Fin E.order, E.coeffs i * (φ l * ψ (m + i + (E.order - 1) - l)) := by
        refine sum_congr rfl fun l hl => ?_
        rw [mem_Icc] at hl
        rw [show m + (E.order - 1) + 1 + (E.order - 1) - l = m + (E.order - 1) - l + E.order by
          omega, hsol, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [show m + (E.order - 1) - l + i = m + i + (E.order - 1) - l by omega]
        ring
    _ = ∑ i : Fin E.order, E.coeffs i * ∑ l ∈ Icc E.order (m + i),
          φ l * ψ (m + i + (E.order - 1) - l) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [← mul_sum]
        congr 1
        refine (sum_subset (Icc_subset_Icc_right (by omega)) fun l hl hl' => ?_).symm
        rw [mem_Icc] at hl
        rw [mem_Icc, not_and, not_le] at hl'
        rw [hψ0 _ (by have := hl' hl.1; omega), mul_zero]

/-- The discrete Duhamel formula: the solution of the inhomogeneous recurrence of order `k ≥ 1`
with source `φ` is the homogeneous solution with the same initial data plus the convolution of the
source with the last Kronecker fundamental solution,
`u n = ∑ j, u j * ψ_j n + ∑_{l = k}^{n} φ l * ψ_{k-1} (n - l + (k - 1))`
([quarteroni2000numerical] (11.42), where `ψ_{k-1}^{(i)} = 0` for `i < 0` — here the sum runs over
`l ≤ n` only, so the index `n - l + (k - 1)` is an honest natural number). -/
theorem eq_sum_kroneckerSol_add_sum {u : ℕ → R} (hu : E.IsSolutionWith φ u) (n : ℕ) :
    u n = (∑ j : Fin E.order, u j * E.kroneckerSol j n) +
      ∑ l ∈ Icc E.order n,
        φ l * E.kroneckerSol ⟨E.order - 1, by omega⟩ (n - l + (E.order - 1)) := by
  set ψ := E.kroneckerSol ⟨E.order - 1, by omega⟩ with hψ
  set I : ℕ → R := fun n => ∑ l ∈ Icc E.order n, φ l * ψ (n + (E.order - 1) - l) with hI
  have hv : E.IsSolutionWith φ fun n => (∑ j : Fin E.order, u j * E.kroneckerSol j n) + I n := by
    intro m
    simp only [hI]
    rw [duhamel_conv_succ hk, ← add_assoc]
    congr 1
    simp only [mul_add, sum_add_distrib]
    congr 1
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [E.isSolution_kroneckerSol j m, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  have := congrFun (hu.eq_of_eqOn_range_order hv fun i => ?_) n
  · rw [this]
    congr 1
    refine sum_congr rfl fun l hl => ?_
    rw [mem_Icc] at hl
    rw [show n + (E.order - 1) - l = n - l + (E.order - 1) by omega]
  · simp only [hI]
    rw [Icc_eq_empty (by simp), sum_empty, add_zero,
      E.sum_mul_kroneckerSol_apply_of_lt (fun j => u j) i.is_lt]

end Duhamel

/-! ### The shift operator and the binomial sequences -/

variable (R) in
/-- The shift operator `S u = u (· + 1)` on sequences, as an endomorphism of `ℕ → R`. A sequence
solves `E` iff `E.charPoly (S) u = 0`; the fundamental solutions are organized by its generalized
eigenspaces. -/
def shift : Module.End R (ℕ → R) where
  toFun u n := u (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The shift operator evaluated: `(S u) n = u (n + 1)`. -/
@[simp]
theorem shift_apply (u : ℕ → R) (n : ℕ) : shift R u n = u (n + 1) := rfl

/-- The binomial sequence `n ↦ n.choose s * r ^ (n - s)` attached to `r` and `s`: the `s`-th Hasse
derivative of `r ↦ r ^ n`, the coefficient of `X ^ s` in `(X + r) ^ n`. For `s = 0` it is the
geometric sequence `r ^ n`, for `r = 0` the Kronecker sequence `δ_{n s}`, and for `r ≠ 0` in
characteristic zero it spans, together with the lower `s`, the same space as `n ^ s * r ^ n`. It
is a solution of every recurrence whose characteristic polynomial has `r` as a root of multiplicity
`> s` (`isSolution_chooseMulPow`). -/
def chooseMulPow (r : R) (s : ℕ) : ℕ → R := fun n => (n.choose s : R) * r ^ (n - s)

/-- The binomial sequence evaluated. -/
theorem chooseMulPow_apply (r : R) (s n : ℕ) :
    chooseMulPow r s n = (n.choose s : R) * r ^ (n - s) := rfl

/-- The binomial sequence with `s = 0` is the geometric sequence `r ^ n`. -/
@[simp]
theorem chooseMulPow_zero (r : R) : chooseMulPow r 0 = fun n => r ^ n := by
  ext n; simp [chooseMulPow]

/-- The binomial sequence with index `s` takes the value `1` at `n = s`. -/
@[simp]
theorem chooseMulPow_apply_self (r : R) (s : ℕ) : chooseMulPow r s s = 1 := by
  simp [chooseMulPow]

/-- The binomial sequence with index `s` vanishes at `n < s`. -/
theorem chooseMulPow_apply_of_lt (r : R) {s n : ℕ} (h : n < s) : chooseMulPow r s n = 0 := by
  simp [chooseMulPow, Nat.choose_eq_zero_of_lt h]

/-- The binomial sequence with index `s` beyond `s`: `(n + s).choose s * r ^ n`. -/
theorem chooseMulPow_apply_add (r : R) (s n : ℕ) :
    chooseMulPow r s (n + s) = ((n + s).choose s : R) * r ^ n := by
  simp [chooseMulPow]

/-- The binomial sequences at `r = 0` are the Kronecker sequences. -/
theorem chooseMulPow_zero_left (s : ℕ) : chooseMulPow (0 : R) s = Pi.single s 1 := by
  ext n
  rcases lt_trichotomy n s with h | rfl | h
  · rw [chooseMulPow_apply_of_lt _ h, Pi.single_eq_of_ne h.ne]
  · simp
  · rw [Pi.single_eq_of_ne h.ne', chooseMulPow_apply, zero_pow (by omega), mul_zero]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

/-- The difference of two solutions with the same source solves the homogeneous recurrence: the
solutions with source `φ` form a coset of `solSpace`. -/
theorem isSolutionWith_sub {φ u v : ℕ → R} (hu : E.IsSolutionWith φ u)
    (hv : E.IsSolutionWith φ v) : E.IsSolution (u - v) := by
  intro n
  simp only [Pi.sub_apply, hu n, hv n, mul_sub, sum_sub_distrib]
  ring

/-- `X ^ n * charPoly` as a combination of monomials. -/
theorem X_pow_mul_charPoly (n : ℕ) :
    X ^ n * E.charPoly =
      monomial (n + E.order) 1 - ∑ i : Fin E.order, monomial (n + i) (E.coeffs i) := by
  simp only [charPoly, mul_sub, mul_sum, X_pow_mul_monomial, add_comm]

/-- The binomial sequences of a multiple root are solutions: if `s < rootMultiplicity r`, then
`n ↦ n.choose s * r ^ (n - s)` solves `E`. Over any commutative ring; the identity is the
vanishing at `r` of the `s`-th Hasse derivative of `X ^ n * charPoly`. -/
theorem isSolution_chooseMulPow {r : R} {s : ℕ} (hs : s < E.charPoly.rootMultiplicity r) :
    E.IsSolution (chooseMulPow r s) := by
  intro n
  have h := eval_hasseDeriv_eq_zero_of_pow_sub_dvd
    ((E.charPoly.pow_rootMultiplicity_dvd r).mul_left (X ^ n)) hs
  rw [X_pow_mul_charPoly, map_sub, map_sum, eval_sub, eval_finsetSum, sub_eq_zero] at h
  simpa [hasseDeriv_monomial, eval_monomial, chooseMulPow, mul_assoc, mul_left_comm] using h

/-- The multiple-root fundamental solutions of [quarteroni2000numerical] §11.4: if
`s < rootMultiplicity q`, then `n ↦ n ^ s * q ^ n` solves `E`. Over any commutative ring; the
identity is the vanishing at `q` of `θ ^ s (X ^ n * charPoly)`, `θ = X d/dX` the Euler operator. -/
theorem isSolution_pow_mul_pow {q : R} {s : ℕ} (hs : s < E.charPoly.rootMultiplicity q) :
    E.IsSolution fun n => (n : R) ^ s * q ^ n := by
  intro n
  have h := eval_iterate_eulerOp_eq_zero_of_pow_sub_dvd
    ((E.charPoly.pow_rootMultiplicity_dvd q).mul_left (X ^ n)) hs
  rw [X_pow_mul_charPoly, ← Module.End.pow_apply, map_sub, map_sum, Module.End.pow_apply,
    eval_sub, eval_finsetSum, sub_eq_zero] at h
  simp only [Module.End.pow_apply, iterate_eulerOp_monomial, eval_monomial] at h
  simpa [mul_assoc, mul_left_comm] using h

/-- The case `s = 1`: if `q` is a root of multiplicity at least `2` of the characteristic polynomial
(equivalently, `Π (q) = Π' (q) = 0`, `Polynomial.one_lt_rootMultiplicity_iff_isRoot`), then
`n ↦ n * q ^ n` solves `E`. -/
theorem isSolution_mul_pow_of_one_lt_rootMultiplicity {q : R}
    (hq : 1 < E.charPoly.rootMultiplicity q) : E.IsSolution fun n => (n : R) * q ^ n := by
  simpa using E.isSolution_pow_mul_pow hq

/-- The shift minus `r` lowers the binomial sequences: `(S - r) e_{s+1} = e_s`, Pascal's rule. -/
theorem shift_sub_smul_chooseMulPow_succ (r : R) (s : ℕ) :
    (shift R - r • 1) (chooseMulPow r (s + 1)) = chooseMulPow r s := by
  ext n
  simp only [LinearMap.sub_apply, shift_apply, LinearMap.smul_apply, Module.End.one_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, chooseMulPow]
  rcases lt_or_ge n (s + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_succ_succ']
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp
    · simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.choose_succ_succ', Nat.add_sub_cancel_left, show s + 1 + m - s = m + 1 by omega,
      show s + 1 + m + 1 - (s + 1) = m + 1 by omega, pow_succ]
    push_cast
    ring

/-- The geometric sequence `r ^ n` is killed by `S - r`. -/
theorem shift_sub_smul_chooseMulPow_zero (r : R) :
    (shift R - r • 1) (chooseMulPow r 0) = 0 := by
  ext n; simp [pow_succ, mul_comm]

/-- Iterated lowering: `(S - r) ^ j e_s = e_{s - j}` for `j ≤ s`, and `0` for `j > s`. -/
theorem shift_sub_smul_pow_chooseMulPow (r : R) (j s : ℕ) :
    ((shift R - r • 1) ^ j) (chooseMulPow r s) =
      if j ≤ s then chooseMulPow r (s - j) else 0 := by
  induction j generalizing s with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply]
    rcases s with _ | s
    · rw [shift_sub_smul_chooseMulPow_zero, map_zero]; simp
    · rw [shift_sub_smul_chooseMulPow_succ, ih]
      simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- The functionals `u ↦ ((S - r) ^ j u) 0` form a dual family to the binomial sequences. -/
theorem shift_sub_smul_pow_chooseMulPow_apply_zero (r : R) (j s : ℕ) :
    ((shift R - r • 1) ^ j) (chooseMulPow r s) 0 = if j = s then 1 else 0 := by
  rw [shift_sub_smul_pow_chooseMulPow]
  split_ifs with h1 h2 h2
  · subst h2; simp
  · rw [chooseMulPow_apply_of_lt _ (by omega)]
  · omega
  · rfl

/-- The binomial sequences at `r` lie in the generalized eigenspace of the shift for the
eigenvalue `r`. -/
theorem chooseMulPow_mem_genEigenspace (r : R) (s : ℕ) :
    chooseMulPow r s ∈ (shift R).genEigenspace r ⊤ := by
  rw [Module.End.mem_genEigenspace_top]
  refine ⟨s + 1, ?_⟩
  rw [LinearMap.mem_ker, shift_sub_smul_pow_chooseMulPow]
  simp

/-- For a fixed `r`, the binomial sequences `chooseMulPow r s`, `s < m`, are linearly independent
(over any nontrivial commutative ring): the dual family
`shift_sub_smul_pow_chooseMulPow_apply_zero`. -/
theorem linearIndependent_chooseMulPow [Nontrivial R] (r : R) (m : ℕ) :
    LinearIndependent R fun s : Fin m => chooseMulPow r s := by
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have := congrFun (congrArg (⇑((shift R - r • 1) ^ (s : ℕ))) hg) 0
  rw [map_sum, map_zero, Pi.zero_apply, Finset.sum_apply] at this
  rw [sum_eq_single s] at this
  · simpa [shift_sub_smul_pow_chooseMulPow_apply_zero] using this
  · intro t _ hts
    simp [shift_sub_smul_pow_chooseMulPow_apply_zero, Fin.val_eq_val, Ne.symm hts]
  · simp

/-! ### Change of coefficients -/

/-- The recurrence with the same order and the coefficients pushed forward along a ring
homomorphism: the bridge from a real recurrence to the complex one whose roots are discussed. -/
def map {S : Type*} [CommRing S] (f : R →+* S) : LinearRecurrence S :=
  ⟨E.order, fun i => f (E.coeffs i)⟩

/-- The pushed-forward recurrence has the same order. -/
@[simp]
theorem map_order {S : Type*} [CommRing S] (f : R →+* S) : (E.map f).order = E.order := rfl

/-- The coefficients of the pushed-forward recurrence. -/
@[simp]
theorem map_coeffs {S : Type*} [CommRing S] (f : R →+* S) (i : Fin (E.map f).order) :
    (E.map f).coeffs i = f (E.coeffs i) := rfl

/-- The characteristic polynomial of the pushed-forward recurrence is the image of the
characteristic polynomial. -/
theorem charPoly_map {S : Type*} [CommRing S] (f : R →+* S) :
    (E.map f).charPoly = E.charPoly.map f := by
  simp only [charPoly, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_monomial, map_one]
  rfl

/-- The image of a solution under a ring homomorphism solves the pushed-forward recurrence. -/
theorem isSolution_map {S : Type*} [CommRing S] (f : R →+* S) {u : ℕ → R} (hu : E.IsSolution u) :
    (E.map f).IsSolution (f ∘ u) := by
  intro n
  simp only [Function.comp_apply, map_order, hu n, map_sum, map_mul]
  rfl

/-- The image of a solution of the inhomogeneous recurrence under a ring homomorphism solves the
pushed-forward recurrence with the pushed-forward source. -/
theorem isSolutionWith_map {S : Type*} [CommRing S] (f : R →+* S) {φ u : ℕ → R}
    (hu : E.IsSolutionWith φ u) : (E.map f).IsSolutionWith (f ∘ φ) (f ∘ u) := by
  intro n
  simp only [Function.comp_apply, map_order, hu n, map_add, map_sum, map_mul]
  rfl

end CommRing

/-! ### The fundamental system -/

section Field

variable {K : Type*} [Field K] (E : LinearRecurrence K)

/-- The solution space is finite-dimensional: it has the basis `E.basis` indexed by `Fin order`. -/
instance : FiniteDimensional K E.solSpace := Module.Finite.of_basis E.basis

/-- The solution space of a recurrence of order `k` over a field has dimension `k`
(Mathlib's `solSpace_rank`, as a `finrank`). -/
theorem finrank_solSpace : Module.finrank K E.solSpace = E.order := by
  rw [Module.finrank_eq_card_basis E.basis, Fintype.card_fin]

/-! ### Simple roots -/

/-- The matrix `R = (r_m ^ i)_{i m}` of [quarteroni2000numerical] (11.37) — the transpose of
Mathlib's `Matrix.vandermonde r` — is nonsingular when the `r_m` are distinct (Exercise 5 of
chapter 11). -/
theorem det_vandermonde_transpose_ne_zero {n : ℕ} {r : Fin n → K} (hr : Function.Injective r) :
    (Matrix.vandermonde r).transpose.det ≠ 0 := by
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.2 hr

/-- The closed form for simple roots ([quarteroni2000numerical] (11.32), Exercise 4 of
chapter 11): if `r : Fin k → K` enumerates `k` distinct roots of the characteristic polynomial of a
recurrence of order `k`, every solution is `u n = ∑ j, γ j • r j ^ n` for a unique `γ`, the
solution of the Vandermonde system `∑ j, γ j * r j ^ i = u i`, `i < k`. (The hypotheses force the
characteristic polynomial to split with simple roots.) -/
theorem eq_sum_smul_pow_of_injective_roots {r : Fin E.order → K}
    (hr : Function.Injective r) (hroot : ∀ j, E.charPoly.IsRoot (r j)) {u : ℕ → K}
    (hu : E.IsSolution u) : ∃! γ : Fin E.order → K, ∀ n, u n = ∑ j, γ j • r j ^ n := by
  simp only [smul_eq_mul]
  set V := (Matrix.vandermonde r).transpose with hV
  have hVu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).2
    (isUnit_iff_ne_zero.2 (det_vandermonde_transpose_ne_zero hr))
  have hmul : ∀ γ : Fin E.order → K,
      V.mulVec γ = fun i : Fin E.order => ∑ j, γ j * r j ^ (i : ℕ) := by
    intro γ
    ext i
    simp [hV, Matrix.mulVec, dotProduct, Matrix.vandermonde, mul_comm]
  have hsol : ∀ γ : Fin E.order → K, E.IsSolution fun n => ∑ j, γ j * r j ^ n := by
    intro γ
    have : (fun n => ∑ j, γ j * r j ^ n) = ∑ j, γ j • fun n => r j ^ n := by
      ext n; simp [Finset.sum_apply]
    rw [this, is_sol_iff_mem_solSpace]
    exact E.solSpace.sum_mem fun j _ =>
      E.solSpace.smul_mem _ ((E.geom_sol_iff_root_charPoly _).2 (hroot j))
  obtain ⟨γ, hγ⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hVu fun i : Fin E.order => u i
  refine ⟨γ, fun n => ?_, fun γ' hγ' => ?_⟩
  · refine congrFun ((E.eq_iff_eqOn_range_order u _ hu (hsol γ)).2 fun i hi => ?_) n
    rw [coe_range, Set.mem_Iio] at hi
    have := congrFun hγ ⟨i, hi⟩
    rw [hmul] at this
    exact this.symm
  · apply Matrix.mulVec_injective_iff_isUnit.2 hVu
    rw [hγ, hmul]
    ext i
    exact (hγ' i).symm

/-! ### The book's form of the general solution -/

/-- For `r ≠ 0` in characteristic zero, the binomial sequence is a polynomial in `n` of degree `s`
times `r ^ n`: `n.choose s * r ^ (n - s) = q (n) * r ^ n` with
`q = C (1 / (s! * r ^ s)) * descPochhammer K s`. -/
theorem chooseMulPow_eq_eval_mul_pow [CharZero K] {r : K} (hr : r ≠ 0) (s n : ℕ) :
    chooseMulPow r s n =
      (C (1 / (s.factorial * r ^ s)) * descPochhammer K s).eval (n : K) * r ^ n := by
  rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial, chooseMulPow_apply]
  rcases lt_or_ge n s with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.descFactorial_eq_zero_iff_lt.2 h]; simp
  · have hf : (s.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 s.factorial_ne_zero
    rw [Nat.descFactorial_eq_factorial_mul_choose, ← pow_sub_mul_pow r h]
    push_cast
    field_simp

section RootIndex

variable [DecidableEq K]

/-- The index set of the fundamental system: the pairs `(r, s)` with `r` a root of the
characteristic polynomial and `s < rootMultiplicity r`. When the characteristic polynomial splits
it has `order` elements (`card_rootIndex`). -/
abbrev RootIndex (E : LinearRecurrence K) : Type _ :=
  Σ r : E.charPoly.roots.toFinset, Fin (E.charPoly.rootMultiplicity (r : K))

/-- The fundamental solution attached to the root index `(r, s)`: the binomial sequence
`n ↦ n.choose s * r ^ (n - s)` (`chooseMulPow`). -/
noncomputable def fundamentalSol (E : LinearRecurrence K) (p : E.RootIndex) : ℕ → K :=
  chooseMulPow (p.1 : K) p.2

/-- The fundamental solution evaluated. -/
theorem fundamentalSol_apply (p : E.RootIndex) (n : ℕ) :
    E.fundamentalSol p n = (n.choose p.2 : K) * (p.1 : K) ^ (n - p.2) := rfl

/-- The fundamental solutions are solutions (`isSolution_chooseMulPow`). -/
theorem isSolution_fundamentalSol (p : E.RootIndex) : E.IsSolution (E.fundamentalSol p) :=
  E.isSolution_chooseMulPow p.2.is_lt

/-- The fundamental system is linearly independent, over any field: within a root by the dual
family of `linearIndependent_chooseMulPow`, across roots because the pieces lie in the generalized
eigenspaces of the shift for distinct eigenvalues, which are independent
(`Module.End.independent_genEigenspace`). -/
theorem linearIndependent_fundamentalSol : LinearIndependent K E.fundamentalSol := by
  refine linearIndependent_iUnion_finite (ιs := fun r : E.charPoly.roots.toFinset =>
    Fin (E.charPoly.rootMultiplicity (r : K)))
    (f := fun r s => chooseMulPow (r : K) s) (fun r => linearIndependent_chooseMulPow _ _) ?_
  intro r t _ hrt
  have hind : iSupIndep fun r : E.charPoly.roots.toFinset => (shift K).genEigenspace (r : K) ⊤ :=
    ((shift K).independent_genEigenspace ⊤).comp Subtype.val_injective
  refine (hind.disjoint_biSup hrt).mono ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact chooseMulPow_mem_genEigenspace _ _
  · refine iSup₂_mono fun r' _ => ?_
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact chooseMulPow_mem_genEigenspace _ _

/-- When the characteristic polynomial splits, the fundamental system has `order` elements:
`∑_r mult r = card roots = natDegree = order`. -/
theorem card_rootIndex (hs : E.charPoly.Splits) : Fintype.card E.RootIndex = E.order := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_coe_sort _ (fun r => E.charPoly.rootMultiplicity r)]
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq, splits_iff_card_roots.mp hs,
    natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order]

/-- The general solution of a linear recurrence whose characteristic polynomial splits
([quarteroni2000numerical] (11.33)): the fundamental system spans the solution space. -/
theorem span_fundamentalSol_eq_solSpace (hs : E.charPoly.Splits) :
    Submodule.span K (Set.range E.fundamentalSol) = E.solSpace := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact E.isSolution_fundamentalSol p
  · rw [finrank_span_eq_card E.linearIndependent_fundamentalSol, E.card_rootIndex hs,
      E.finrank_solSpace]

/-- Every solution of a recurrence whose characteristic polynomial splits is a finite combination
of the fundamental solutions. -/
theorem exists_eq_sum_smul_fundamentalSol (hs : E.charPoly.Splits) {u : ℕ → K}
    (hu : E.IsSolution u) : ∃ c : E.RootIndex → K, u = ∑ p, c p • E.fundamentalSol p := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
    ((E.span_fundamentalSol_eq_solSpace hs).symm ▸ (E.is_sol_iff_mem_solSpace u).1 hu)
  exact ⟨c, hc.symm⟩

/-- The general solution in the form of [quarteroni2000numerical] (11.33): in characteristic zero,
when the characteristic polynomial splits and `0` is not a root (the book's `α_0 ≠ 0`), every
solution is `u n = ∑_j p_j (n) * r_j ^ n` over the distinct roots `r_j`, with polynomials `p_j`
of degree less than the multiplicity `m_j` — the book's `p_j (n) = ∑_{s < m_j} γ_{s j} n ^ s`.
Without `α_0 ≠ 0` the statement fails (`n ^ s * 0 ^ n = 0` for `s ≥ 1`), and without
characteristic zero the binomial coefficient is not a polynomial in `n`; the fundamental system
`fundamentalSol` needs neither. -/
theorem exists_eq_sum_eval_mul_pow_of_splits [CharZero K] (hs : E.charPoly.Splits)
    (h0 : ¬ E.charPoly.IsRoot 0) {u : ℕ → K} (hu : E.IsSolution u) :
    ∃ p : K → K[X], (∀ r, (p r).degree < (E.charPoly.rootMultiplicity r : WithBot ℕ)) ∧
      ∀ n, u n = ∑ r ∈ E.charPoly.roots.toFinset, (p r).eval (n : K) * r ^ n := by
  obtain ⟨c, hc⟩ := E.exists_eq_sum_smul_fundamentalSol hs hu
  have hne : ∀ r ∈ E.charPoly.roots.toFinset, r ≠ 0 := fun r hr h => h0 <| by
    rw [Multiset.mem_toFinset, mem_roots E.charPoly_monic.ne_zero] at hr
    exact h ▸ hr
  let q : K → ℕ → K[X] := fun r s => C (1 / (s.factorial * r ^ s)) * descPochhammer K s
  have hq : ∀ r s, (q r s).degree ≤ s := fun r s => by
    refine (degree_mul_le _ _).trans ?_
    rw [degree_eq_natDegree (monic_descPochhammer K s).ne_zero, descPochhammer_natDegree]
    calc (C (1 / (s.factorial * r ^ s))).degree + s ≤ 0 + s := by gcongr; exact degree_C_le
      _ = s := zero_add _
  refine ⟨fun r => if hr : r ∈ E.charPoly.roots.toFinset then
    ∑ s : Fin (E.charPoly.rootMultiplicity r), c ⟨⟨r, hr⟩, s⟩ • q r s else 0, fun r => ?_,
    fun n => ?_⟩
  · dsimp only
    split_ifs with hr
    · refine (degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro s _
      refine (degree_smul_le _ _).trans_lt ((hq r s).trans_lt ?_)
      exact_mod_cast s.is_lt
    · rw [degree_zero]
      exact WithBot.bot_lt_coe _
  · rw [hc, Finset.sum_apply, Fintype.sum_sigma, ← Finset.sum_coe_sort E.charPoly.roots.toFinset]
    refine sum_congr rfl fun r _ => ?_
    dsimp only
    rw [dite_eq_left r.2, eval_finsetSum, sum_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, eval_smul, smul_eq_mul, fundamentalSol,
      chooseMulPow_eq_eval_mul_pow (hne r r.2), mul_assoc]

end RootIndex

end Field

end LinearRecurrence
