/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

A linear recurrence of order $k$ with coefficients $c_0, \dots, c_{k-1}$ in a commutative ring $R$
is the relation $u_{n+k} = \sum_{i<k} c_i u_{n+i}$ for sequences $u \colon \mathbb{N} \to R$. Its
characteristic polynomial is $\Pi(X) = X^k - \sum_{i<k} c_i X^i$. Mathlib's `LinearRecurrence`
provides the solution space `LinearRecurrence.solSpace` of rank $k$, the solution
`LinearRecurrence.mkSol` with prescribed initial values, and the fact that $q^n$ is a solution if
and only if $\Pi(q) = 0$. This module adds the closed forms that the theory of linear difference
equations needs. It follows [quarteroni2000numerical], §11.4.

The module treats the inhomogeneous recurrence $u_{n+k} = \sum_i c_i u_{n+i} + \varphi_{n+k}$ and
proves existence and uniqueness of its solutions and the discrete Duhamel formula, which writes
every solution with the fundamental solutions $\psi_j$ of Kronecker initial values
$\psi_j(i) = \delta_{ij}$. For a root $r$ of $\Pi$ of multiplicity $m$, the sequences $n^s r^n$ and
the binomial sequences $\binom{n}{s} r^{n-s}$, $s < m$, are solutions over every commutative ring.
Over a field, the binomial sequences of all roots are linearly independent, and they span the
solution space when $\Pi$ splits. In characteristic zero and with $\Pi(0) \neq 0$, this gives the
general solution $u_n = \sum_j p_j(n) r_j^n$ with $\deg p_j < m_j$ of [quarteroni2000numerical],
(11.33). For $k$ distinct roots, the general solution is $u_n = \sum_j \gamma_j r_j^n$ with a unique
$\gamma$.

## Main definitions

* `Polynomial.eulerOp`: the Euler operator $\theta p = X p'$ on polynomials.
* `LinearRecurrence.IsSolutionWith`: $u$ solves the inhomogeneous recurrence with source $\varphi$.
* `LinearRecurrence.mkSolWith`: the solution of the inhomogeneous recurrence with given initial
  values.
* `LinearRecurrence.kroneckerSol`: the fundamental solution $\psi_j$ with $\psi_j(i) = \delta_{ij}$
  for $i < k$.
* `LinearRecurrence.shift`: the shift operator $(Su)_n = u_{n+1}$ on sequences.
* `LinearRecurrence.chooseMulPow`: the binomial sequence $n \mapsto \binom{n}{s} r^{n-s}$.
* `LinearRecurrence.map`: the recurrence with coefficients pushed forward along a ring homomorphism.
* `LinearRecurrence.RootIndex`: the pairs $(r, s)$ with $r$ a root of $\Pi$ and $s$ less than its
  multiplicity.
* `LinearRecurrence.fundamentalSol`: the binomial sequence attached to a pair $(r, s)$.

## Main results

* `LinearRecurrence.eq_mkSolWith_of_isSolutionWith_of_eq_init'`: a solution of the inhomogeneous
  recurrence is determined by its first $k$ values.
* `LinearRecurrence.isSolutionWith_sub`: the difference of two solutions with the same source solves
  the homogeneous recurrence.
* `LinearRecurrence.eq_sum_kroneckerSol`: every solution is $u_n = \sum_j u_j \psi_j(n)$ ((11.35) of
  [quarteroni2000numerical]).
* `LinearRecurrence.eq_sum_kroneckerSol_add_sum`: the discrete Duhamel formula ((11.42) of
  [quarteroni2000numerical]).
* `LinearRecurrence.isSolution_pow_mul_pow`: if $s$ is less than the multiplicity of the root $q$ of
  $\Pi$, then $n^s q^n$ is a solution.
* `LinearRecurrence.isSolution_chooseMulPow`: if $s$ is less than the multiplicity of the root $r$
  of $\Pi$, then $\binom{n}{s} r^{n-s}$ is a solution.
* `LinearRecurrence.linearIndependent_fundamentalSol`: over a field, the fundamental system is
  linearly independent.
* `LinearRecurrence.span_fundamentalSol_eq_solSpace`: if $\Pi$ splits, the fundamental system spans
  the solution space ((11.33) of [quarteroni2000numerical]).
* `LinearRecurrence.exists_eq_sum_eval_mul_pow_of_splits`: in characteristic zero, if $\Pi$ splits
  and $\Pi(0) \neq 0$, then every solution is $\sum_j p_j(n) r_j^n$ with $\deg p_j < m_j$.
* `LinearRecurrence.eq_sum_smul_pow_of_injective_roots`: if $\Pi$ has $k$ distinct roots $r_j$, then
  every solution is $\sum_j \gamma_j r_j^n$ for a unique $\gamma$ ((11.32) of
  [quarteroni2000numerical]).

## Proof outline

The sequences $n^s q^n$ solve the recurrence because the iterated Euler operator $\theta^s$ of
$X^n \Pi$ vanishes at a root $q$ of multiplicity greater than $s$. In the same way, the binomial
sequences solve it because the Hasse derivatives of $X^n \Pi$ of order less than the multiplicity
vanish at the root. The shift $S$ lowers the binomial sequences, $(S - r) e_{s+1} = e_s$ for
$e_s = \binom{n}{s} r^{n-s}$. So the binomial sequences of one root lie in the generalized
eigenspace of $S$ for the eigenvalue $r$, and the functionals $u \mapsto ((S - r)^j u)_0$ form a
dual family to them. This gives the linear independence for one root. Generalized eigenspaces for
distinct eigenvalues are independent, and this gives the linear independence for all roots. When
$\Pi$ splits, the number of pairs $(r, s)$ is the sum of the multiplicities, which is $k$, the
dimension of the solution space.

## Implementation notes

* The module is written to Mathlib conventions, and its natural home is
  `Mathlib.Algebra.LinearRecurrence`. The polynomial lemmas at the top (the Euler operator, and the
  vanishing of Hasse derivatives and of iterated Euler operators at a multiple root) do not depend
  on recurrences.
* Mathlib's `LinearRecurrence.IsSolution` is $u_{n+k} = \sum_{i<k} c_i u_{n+i}$. The equation
  $u_{n+k} + \alpha_{k-1} u_{n+k-1} + \dots + \alpha_0 u_n = 0$ of [quarteroni2000numerical] has
  $c_i = -\alpha_i$, and `LinearRecurrence.charPoly` is the polynomial $\Pi$ of the source.
* Sequences are indexed by $\mathbb{N}$. The convention $\psi_{k-1}(i) = 0$ for $i < 0$ in (11.42)
  of [quarteroni2000numerical] is encoded by a sum over $k \le l \le n$ only, where the index
  $n - l + k - 1$ is a natural number.
* The fundamental system uses the binomial sequences $\binom{n}{s} r^{n-s}$, not the sequences
  $n^s r^n$ of the source. The binomial sequences behave uniformly at the root $r = 0$: there
  $\binom{n}{s} 0^{n-s}$ is the Kronecker sequence $\delta_{ns}$, while $n^s 0^n$ is the zero
  sequence for $s \ge 1$. The shift lowers them, which makes their independence a triangular
  computation. Neither the independence nor the spanning statement needs characteristic zero or
  $\Pi(0) \neq 0$. The form $\sum_j p_j(n) r_j^n$ of the source needs both, because $\binom{n}{s}$
  is a polynomial in $n$ only in characteristic zero, and $n^s 0^n$ vanishes.
* The matrix $(r_m^i)$ of (11.37) of [quarteroni2000numerical] is the transpose of Mathlib's
  `Matrix.vandermonde`.
-/

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Let $R$ be a commutative ring, let $p \in R[X]$, $a \in R$ and $s < m$. If $(X - a)^m$ divides
$p$, then the $s$-th Hasse derivative of $p$ vanishes at $a$:
$$\bigl(D^{(s)} p\bigr)(a) = 0.$$

The Hasse derivative $D^{(s)}$ is `Polynomial.hasseDeriv s`. In other words, the Taylor
expansion of $p$ at $a$ starts at order $m$. -/
theorem eval_hasseDeriv_eq_zero_of_pow_sub_dvd {p : R[X]} {a : R} {m s : ℕ}
    (h : (X - C a) ^ m ∣ p) (hs : s < m) : (hasseDeriv s p).eval a = 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [← taylor_coeff, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right,
    coeff_X_pow_mul']
  simp [not_le.mpr hs]

/-- Let $p \in R[X]$ and $a \in R$. If $s$ is less than the multiplicity of $a$ as a root of $p$,
then the $s$-th Hasse derivative of $p$ vanishes at $a$. -/
theorem eval_hasseDeriv_eq_zero_of_lt_rootMultiplicity {p : R[X]} {a : R} {s : ℕ}
    (hs : s < p.rootMultiplicity a) : (hasseDeriv s p).eval a = 0 :=
  eval_hasseDeriv_eq_zero_of_pow_sub_dvd (p.pow_rootMultiplicity_dvd a) hs

/-- The **Euler operator** $\theta p = X p'$ on $R[X]$, as an $R$-linear map. It multiplies the
monomial $X^n$ by $n$, so $\theta^s$ multiplies it by $n^s$. It is the operator behind the
sequences $n^s q^n$. -/
noncomputable def eulerOp : R[X] →ₗ[R] R[X] :=
  (LinearMap.mulLeft R (X : R[X])).comp derivative

/-- The Euler operator is $\theta p = X p'$. -/
theorem eulerOp_apply (p : R[X]) : eulerOp p = X * derivative p := rfl

/-- The Euler operator maps the monomial $a X^n$ to $n a X^n$. -/
@[simp]
theorem eulerOp_monomial (n : ℕ) (a : R) : eulerOp (monomial n a) = monomial n (n * a) := by
  rw [eulerOp_apply, derivative_monomial]
  rcases n with _ | n
  · simp
  · rw [X_mul_monomial, Nat.add_sub_cancel, mul_comm]

/-- The $s$-th iterate of the Euler operator maps the monomial $a X^n$ to $n^s a X^n$. -/
theorem iterate_eulerOp_monomial (s n : ℕ) (a : R) :
    (⇑eulerOp)^[s] (monomial n a) = monomial n ((n : R) ^ s * a) := by
  induction s generalizing a with
  | zero => simp
  | succ s ih => rw [Function.iterate_succ_apply, eulerOp_monomial, ih, pow_succ]; ring_nf

/-- Let $p, q \in R[X]$. If $q^n$ divides $p$, then $q^{n-1}$ divides $\theta p$, where $n - 1 = 0$
for $n = 0$. -/
theorem pow_sub_one_dvd_eulerOp_of_pow_dvd {p q : R[X]} {n : ℕ} (h : q ^ n ∣ p) :
    q ^ (n - 1) ∣ eulerOp p :=
  (pow_sub_one_dvd_derivative_of_pow_dvd h).mul_left _

/-- Let $p, q \in R[X]$ and $s \in \mathbb{N}$. If $q^n$ divides $p$, then $q^{n-s}$ divides
$\theta^s p$, where $n - s = 0$ for $n \le s$. -/
theorem pow_sub_dvd_iterate_eulerOp_of_pow_dvd {p q : R[X]} {n : ℕ} (s : ℕ) (h : q ^ n ∣ p) :
    q ^ (n - s) ∣ (⇑eulerOp)^[s] p := by
  induction s generalizing p with
  | zero => simpa
  | succ s ih =>
    rw [Function.iterate_succ_apply', Nat.sub_succ']
    exact pow_sub_one_dvd_eulerOp_of_pow_dvd (ih h)

/-- Let $R$ be a commutative ring, let $p \in R[X]$, $a \in R$ and $s < m$. If $(X - a)^m$ divides
$p$, then the $s$-th iterate of the Euler operator $\theta = X \frac{d}{dX}$ applied to $p$
vanishes at $a$:
$$\bigl(\theta^s p\bigr)(a) = 0.$$
-/
theorem eval_iterate_eulerOp_eq_zero_of_pow_sub_dvd {p : R[X]} {a : R} {m s : ℕ}
    (h : (X - C a) ^ m ∣ p) (hs : s < m) : ((⇑eulerOp)^[s] p).eval a = 0 := by
  have := pow_sub_dvd_iterate_eulerOp_of_pow_dvd s h
  exact dvd_iff_isRoot.mp ((dvd_pow_self _ (Nat.sub_ne_zero_of_lt hs)).trans this)

end Polynomial

namespace LinearRecurrence

/-! ### The inhomogeneous recurrence -/

section CommSemiring

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

/-- Let $E$ be a linear recurrence of order $k$ with coefficients $c_i$ over a commutative semiring
$R$, and let $\varphi, u \colon \mathbb{N} \to R$. The sequence $u$ **solves the inhomogeneous
recurrence with source $\varphi$** if
$$u_{n+k} = \sum_{i<k} c_i u_{n+i} + \varphi_{n+k} \quad \text{for every } n \in \mathbb{N}.$$

This is the linear difference equation $u_{n+k} + \alpha_{k-1} u_{n+k-1} + \dots + \alpha_0
u_n = \varphi_{n+k}$ of [quarteroni2000numerical], (11.28), with $c_i = -\alpha_i$. The source
is indexed at $n + k$ as in the source text, so that the values
$\varphi_0, \dots, \varphi_{k-1}$ are never used. -/
def IsSolutionWith (φ u : ℕ → R) : Prop :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i) + φ (n + E.order)

/-- The inhomogeneous recurrence with source $0$ is the homogeneous recurrence: $u$ solves it if and
only if $u$ is a solution of $E$. -/
@[simp]
theorem isSolutionWith_zero_iff (u : ℕ → R) : E.IsSolutionWith 0 u ↔ E.IsSolution u := by
  simp [IsSolutionWith, IsSolution]

/-- The solution of the inhomogeneous recurrence with source $\varphi$ and initial values
$\mathrm{init}_0, \dots, \mathrm{init}_{k-1}$. It is defined by $u_n = \mathrm{init}_n$ for
$n < k$ and by the recursion
$$u_n = \sum_{i<k} c_i u_{n-k+i} + \varphi_n \quad \text{for } n \ge k.$$

It is the unique such solution, by
`LinearRecurrence.eq_mkSolWith_of_isSolutionWith_of_eq_init'`. -/
def mkSolWith (φ : ℕ → R) (init : Fin E.order → R) : ℕ → R
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      (∑ k : Fin E.order,
        have _ : n - E.order + k < n := by omega
        E.coeffs k * mkSolWith φ init (n - E.order + k)) + φ n

/-- The sequence `LinearRecurrence.mkSolWith` $\varphi$ $\mathrm{init}$ solves the inhomogeneous
recurrence with source $\varphi$. -/
theorem isSolutionWith_mkSolWith (φ : ℕ → R) (init : Fin E.order → R) :
    E.IsSolutionWith φ (E.mkSolWith φ init) := by
  intro n
  rw [mkSolWith]
  simp

/-- The first $k$ values of `LinearRecurrence.mkSolWith` $\varphi$ $\mathrm{init}$ are the initial
values: $u_n = \mathrm{init}_n$ for $n < k$. -/
theorem mkSolWith_eq_init (φ : ℕ → R) (init : Fin E.order → R) (n : Fin E.order) :
    E.mkSolWith φ init n = init n := by
  rw [mkSolWith]
  simp only [n.is_lt, dite_eq_left, Fin.mk_val]

/-- Uniqueness for the inhomogeneous recurrence, pointwise. Let $u$ solve the inhomogeneous
recurrence with source $\varphi$, and let $u_n = \mathrm{init}_n$ for $n < k$. Then for every
$n$, $u_n$ is the $n$-th value of `LinearRecurrence.mkSolWith` $\varphi$ $\mathrm{init}$. -/
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

/-- Uniqueness for the inhomogeneous recurrence. Let $u$ solve the inhomogeneous recurrence with
source $\varphi$, and let $u_n = \mathrm{init}_n$ for $n < k$. Then $u$ is the sequence
`LinearRecurrence.mkSolWith` $\varphi$ $\mathrm{init}$. -/
theorem eq_mkSolWith_of_isSolutionWith_of_eq_init' {φ u : ℕ → R} {init : Fin E.order → R}
    (h : E.IsSolutionWith φ u) (heq : ∀ n : Fin E.order, u n = init n) :
    u = E.mkSolWith φ init :=
  funext (E.eq_mkSolWith_of_isSolutionWith_of_eq_init h heq)

variable {E} in
/-- Let $u$ and $v$ solve the inhomogeneous recurrence with the same source $\varphi$. If
$u_n = v_n$ for all $n < k$, then $u = v$. -/
theorem IsSolutionWith.eq_of_eqOn_range_order {φ u v : ℕ → R} (hu : E.IsSolutionWith φ u)
    (hv : E.IsSolutionWith φ v) (h : ∀ n : Fin E.order, u n = v n) : u = v :=
  (E.eq_mkSolWith_of_isSolutionWith_of_eq_init' hu (init := fun n => v n) h).trans
    (E.eq_mkSolWith_of_isSolutionWith_of_eq_init' hv fun _ => rfl).symm

/-- Let $u$ solve the inhomogeneous recurrence with source $\varphi$, and let $w$ solve the
homogeneous recurrence. Then $u + w$ solves the inhomogeneous recurrence with source $\varphi$. -/
theorem isSolutionWith_add {φ u w : ℕ → R} (hu : E.IsSolutionWith φ u) (hw : E.IsSolution w) :
    E.IsSolutionWith φ (u + w) := by
  intro n
  simp only [Pi.add_apply, hu n, hw n, mul_add, sum_add_distrib]
  ring

/-! ### The Kronecker fundamental solutions -/

/-- The **Kronecker fundamental solution** $\psi_j$, for $j < k$: the solution of the homogeneous
recurrence with the initial values $\psi_j(i) = \delta_{ij}$ for $i < k$
([quarteroni2000numerical], (11.34)). -/
noncomputable def kroneckerSol (j : Fin E.order) : ℕ → R :=
  E.mkSol (Pi.single j 1)

/-- The Kronecker fundamental solutions solve the homogeneous recurrence. -/
theorem isSolution_kroneckerSol (j : Fin E.order) : E.IsSolution (E.kroneckerSol j) :=
  E.is_sol_mkSol _

/-- The Kronecker initial values (11.34) of [quarteroni2000numerical]: for $i < k$, $\psi_j(i)$ is
$1$ if $i = j$ and $0$ otherwise. -/
theorem kroneckerSol_apply_of_lt (j : Fin E.order) {i : ℕ} (hi : i < E.order) :
    E.kroneckerSol j i = if i = j then 1 else 0 := by
  have := E.mkSol_eq_init (Pi.single j 1) ⟨i, hi⟩
  rw [kroneckerSol, this, Pi.single_apply]
  simp only [Fin.ext_iff]

/-- The Kronecker fundamental solution satisfies $\psi_j(j) = 1$. -/
@[simp]
theorem kroneckerSol_apply_self (j : Fin E.order) : E.kroneckerSol j j = 1 := by
  simp [E.kroneckerSol_apply_of_lt j j.is_lt]

/-- For $i < k$ with $i \neq j$, the Kronecker fundamental solution satisfies $\psi_j(i) = 0$. -/
theorem kroneckerSol_apply_of_ne (j : Fin E.order) {i : ℕ} (hi : i < E.order) (hij : i ≠ j) :
    E.kroneckerSol j i = 0 := by
  simp [E.kroneckerSol_apply_of_lt j hi, hij]

/-- Let $c_0, \dots, c_{k-1} \in R$. For $i < k$, the combination of the Kronecker fundamental
solutions with these coefficients has the value $c_i$ at $i$:
$$\sum_{j<k} c_j \psi_j(i) = c_i.$$
-/
theorem sum_mul_kroneckerSol_apply_of_lt (c : Fin E.order → R) {i : ℕ} (hi : i < E.order) :
    ∑ j : Fin E.order, c j * E.kroneckerSol j i = c ⟨i, hi⟩ := by
  rw [sum_eq_single ⟨i, hi⟩ (fun j _ hj => ?_) (by simp)]
  · rw [E.kroneckerSol_apply_of_lt _ hi]
    simp
  · rw [E.kroneckerSol_apply_of_ne j hi fun h => hj (Fin.ext h.symm), mul_zero]

/-- For all $c_0, \dots, c_{k-1} \in R$, the sequence $n \mapsto \sum_{j<k} c_j \psi_j(n)$ solves
the homogeneous recurrence. -/
theorem isSolution_sum_mul_kroneckerSol (c : Fin E.order → R) :
    E.IsSolution fun n => ∑ j : Fin E.order, c j * E.kroneckerSol j n := by
  have : (fun n => ∑ j : Fin E.order, c j * E.kroneckerSol j n) =
      ∑ j : Fin E.order, c j • E.kroneckerSol j := by
    ext n; simp [Finset.sum_apply]
  rw [this, is_sol_iff_mem_solSpace]
  exact E.solSpace.sum_mem fun j _ => E.solSpace.smul_mem (c j) (E.isSolution_kroneckerSol j)

/-- Every solution $u$ of the homogeneous recurrence is the combination of the Kronecker fundamental
solutions with its initial values as coefficients:
$$u_n = \sum_{j<k} u_j \psi_j(n) \quad \text{for every } n \in \mathbb{N}.$$
This is (11.35) of [quarteroni2000numerical]. -/
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

/-- For $k \ge 1$, the convolution $w_n = \sum_{l=k}^{n} \varphi_l \psi_{k-1}(n + (k - 1) - l)$
satisfies $w_{m+k} = \sum_{i<k} c_i w_{m+i} + \varphi_{m+k}$ for every $m$. -/
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

/-- The **discrete Duhamel formula**. Let $E$ be a linear recurrence of order $k \ge 1$ over a
commutative semiring, and let $u$ solve the inhomogeneous recurrence with source $\varphi$. Then
$u$ is the solution of the homogeneous recurrence with the same initial values plus the
convolution of the source with the last Kronecker fundamental solution:
$$u_n = \sum_{j<k} u_j \psi_j(n) + \sum_{l=k}^{n} \varphi_l \, \psi_{k-1}(n - l + k - 1) \quad
  \text{for every } n \in \mathbb{N}.$$
This is (11.42) of [quarteroni2000numerical].

The source text sets $\psi_{k-1}(i) = 0$ for $i < 0$. Here the second sum runs over
$k \le l \le n$ only, so the index $n - l + k - 1$ is a natural number. For $n < k$ the second
sum is empty. -/
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
/-- The **shift operator** $(Su)_n = u_{n+1}$ on sequences $u \colon \mathbb{N} \to R$, as an
$R$-linear endomorphism of $R^{\mathbb{N}}$. A sequence solves the recurrence $E$ if and only if
$\Pi(S) u = 0$, and the fundamental solutions are organized by the generalized eigenspaces of
$S$. -/
def shift : Module.End R (ℕ → R) where
  toFun u n := u (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The shift operator satisfies $(Su)_n = u_{n+1}$. -/
@[simp]
theorem shift_apply (u : ℕ → R) (n : ℕ) : shift R u n = u (n + 1) := rfl

/-- The **binomial sequence** attached to $r \in R$ and $s \in \mathbb{N}$:
$$e_s(n) = \binom{n}{s} r^{n-s},$$
with $n - s = 0$ for $n < s$ (where the binomial coefficient is $0$). It is the $s$-th Hasse
derivative of $r \mapsto r^n$, and the coefficient of $X^s$ in $(X + r)^n$. For $s = 0$ it is
the geometric sequence $r^n$, and for $r = 0$ it is the Kronecker sequence $\delta_{ns}$. For
$r \neq 0$ in characteristic zero, the sequences $e_0, \dots, e_s$ span the same space as the
sequences $n^j r^n$, $j \le s$. The binomial sequence solves every recurrence whose
characteristic polynomial has $r$ as a root of multiplicity greater than $s$
(`LinearRecurrence.isSolution_chooseMulPow`). -/
def chooseMulPow (r : R) (s : ℕ) : ℕ → R := fun n => (n.choose s : R) * r ^ (n - s)

/-- The binomial sequence has the value $\binom{n}{s} r^{n-s}$ at $n$. -/
theorem chooseMulPow_apply (r : R) (s n : ℕ) :
    chooseMulPow r s n = (n.choose s : R) * r ^ (n - s) := rfl

/-- The binomial sequence with $s = 0$ is the geometric sequence $n \mapsto r^n$. -/
@[simp]
theorem chooseMulPow_zero (r : R) : chooseMulPow r 0 = fun n => r ^ n := by
  ext n; simp [chooseMulPow]

/-- The binomial sequence with index $s$ has the value $1$ at $n = s$. -/
@[simp]
theorem chooseMulPow_apply_self (r : R) (s : ℕ) : chooseMulPow r s s = 1 := by
  simp [chooseMulPow]

/-- The binomial sequence with index $s$ vanishes at every $n < s$. -/
theorem chooseMulPow_apply_of_lt (r : R) {s n : ℕ} (h : n < s) : chooseMulPow r s n = 0 := by
  simp [chooseMulPow, Nat.choose_eq_zero_of_lt h]

/-- The binomial sequence with index $s$ has the value $\binom{n+s}{s} r^n$ at $n + s$. -/
theorem chooseMulPow_apply_add (r : R) (s n : ℕ) :
    chooseMulPow r s (n + s) = ((n + s).choose s : R) * r ^ n := by
  simp [chooseMulPow]

/-- The binomial sequences at $r = 0$ are the Kronecker sequences:
$\binom{n}{s} 0^{n-s} = \delta_{ns}$ for all $n$ and $s$.

Here $0^0 = 1$. -/
theorem chooseMulPow_zero_left (s : ℕ) : chooseMulPow (0 : R) s = Pi.single s 1 := by
  ext n
  rcases lt_trichotomy n s with h | rfl | h
  · rw [chooseMulPow_apply_of_lt _ h, Pi.single_eq_of_ne h.ne]
  · simp
  · rw [Pi.single_eq_of_ne h.ne', chooseMulPow_apply, zero_pow (by omega), mul_zero]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

/-- Let $E$ be a linear recurrence over a commutative ring. If $u$ and $v$ solve the inhomogeneous
recurrence with the same source $\varphi$, then $u - v$ solves the homogeneous recurrence. So
the solutions with source $\varphi$ form a coset of the solution space. -/
theorem isSolutionWith_sub {φ u v : ℕ → R} (hu : E.IsSolutionWith φ u)
    (hv : E.IsSolutionWith φ v) : E.IsSolution (u - v) := by
  intro n
  simp only [Pi.sub_apply, hu n, hv n, mul_sub, sum_sub_distrib]
  ring

/-- For every $n \in \mathbb{N}$, $X^n \Pi = X^{n+k} - \sum_{i<k} c_i X^{n+i}$. -/
theorem X_pow_mul_charPoly (n : ℕ) :
    X ^ n * E.charPoly =
      monomial (n + E.order) 1 - ∑ i : Fin E.order, monomial (n + i) (E.coeffs i) := by
  simp only [charPoly, mul_sub, mul_sum, X_pow_mul_monomial, add_comm]

/-- Let $E$ be a linear recurrence over a commutative ring $R$ with characteristic polynomial $\Pi$,
and let $r \in R$. If $s$ is less than the multiplicity of $r$ as a root of $\Pi$, then the
binomial sequence
$$n \mapsto \binom{n}{s} r^{n-s}$$
solves $E$.

The recurrence at $n$ is the vanishing at $r$ of the $s$-th Hasse derivative of $X^n \Pi$. -/
theorem isSolution_chooseMulPow {r : R} {s : ℕ} (hs : s < E.charPoly.rootMultiplicity r) :
    E.IsSolution (chooseMulPow r s) := by
  intro n
  have h := eval_hasseDeriv_eq_zero_of_pow_sub_dvd
    ((E.charPoly.pow_rootMultiplicity_dvd r).mul_left (X ^ n)) hs
  rw [X_pow_mul_charPoly, map_sub, map_sum, eval_sub, eval_finsetSum, sub_eq_zero] at h
  simpa [hasseDeriv_monomial, eval_monomial, chooseMulPow, mul_assoc, mul_left_comm] using h

/-- Let $E$ be a linear recurrence over a commutative ring $R$ with characteristic polynomial $\Pi$,
and let $q \in R$. If $s$ is less than the multiplicity of $q$ as a root of $\Pi$, then the
sequence
$$n \mapsto n^s q^n$$
solves $E$. These are the fundamental solutions of a multiple root in [quarteroni2000numerical],
§11.4.

The recurrence at $n$ is the vanishing at $q$ of $\theta^s(X^n \Pi)$, where
$\theta = X \frac{d}{dX}$ is the Euler operator `Polynomial.eulerOp`. Here $0^0 = 1$. -/
theorem isSolution_pow_mul_pow {q : R} {s : ℕ} (hs : s < E.charPoly.rootMultiplicity q) :
    E.IsSolution fun n => (n : R) ^ s * q ^ n := by
  intro n
  have h := eval_iterate_eulerOp_eq_zero_of_pow_sub_dvd
    ((E.charPoly.pow_rootMultiplicity_dvd q).mul_left (X ^ n)) hs
  rw [X_pow_mul_charPoly, ← Module.End.pow_apply, map_sub, map_sum, Module.End.pow_apply,
    eval_sub, eval_finsetSum, sub_eq_zero] at h
  simp only [Module.End.pow_apply, iterate_eulerOp_monomial, eval_monomial] at h
  simpa [mul_assoc, mul_left_comm] using h

/-- Let $q \in R$ be a root of multiplicity at least $2$ of the characteristic polynomial $\Pi$,
that is, $\Pi(q) = \Pi'(q) = 0$. Then the sequence $n \mapsto n q^n$ solves $E$.

The equivalence of the two forms of the hypothesis is
`Polynomial.one_lt_rootMultiplicity_iff_isRoot`. This is the case $s = 1$ of
`LinearRecurrence.isSolution_pow_mul_pow`. -/
theorem isSolution_mul_pow_of_one_lt_rootMultiplicity {q : R}
    (hq : 1 < E.charPoly.rootMultiplicity q) : E.IsSolution fun n => (n : R) * q ^ n := by
  simpa using E.isSolution_pow_mul_pow hq

/-- Let $r \in R$ and let $e_s$ be the binomial sequences at $r$. Then $(S - r) e_{s+1} = e_s$ for
every $s$, where $S$ is the shift operator. This is Pascal's rule. -/
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

/-- The shift operator satisfies $(S - r) e_0 = 0$: it maps the geometric sequence $r^n$ to
$r^{n+1}$. -/
theorem shift_sub_smul_chooseMulPow_zero (r : R) :
    (shift R - r • 1) (chooseMulPow r 0) = 0 := by
  ext n; simp [pow_succ, mul_comm]

/-- Let $r \in R$ and let $e_s$ be the binomial sequences at $r$. Then for all
$j, s \in \mathbb{N}$,
$$(S - r)^j e_s = \begin{cases} e_{s-j} & \text{if } j \le s, \\ 0 & \text{if } j > s.
  \end{cases}$$
-/
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

/-- For all $j, s \in \mathbb{N}$, the value of $(S - r)^j e_s$ at $0$ is $1$ if $j = s$ and $0$
otherwise. So the functionals $u \mapsto ((S - r)^j u)_0$ form a dual family to the binomial
sequences. -/
theorem shift_sub_smul_pow_chooseMulPow_apply_zero (r : R) (j s : ℕ) :
    ((shift R - r • 1) ^ j) (chooseMulPow r s) 0 = if j = s then 1 else 0 := by
  rw [shift_sub_smul_pow_chooseMulPow]
  split_ifs with h1 h2 h2
  · subst h2; simp
  · rw [chooseMulPow_apply_of_lt _ (by omega)]
  · omega
  · rfl

/-- For every $s$, the binomial sequence $e_s$ at $r$ lies in the generalized eigenspace of the
shift operator for the eigenvalue $r$, that is, $(S - r)^j e_s = 0$ for some $j$. -/
theorem chooseMulPow_mem_genEigenspace (r : R) (s : ℕ) :
    chooseMulPow r s ∈ (shift R).genEigenspace r ⊤ := by
  rw [Module.End.mem_genEigenspace_top]
  refine ⟨s + 1, ?_⟩
  rw [LinearMap.mem_ker, shift_sub_smul_pow_chooseMulPow]
  simp

/-- Let $R$ be a commutative ring, let $r \in R$ and $m \in \mathbb{N}$. Then the binomial sequences
$e_s(n) = \binom{n}{s} r^{n-s}$, $s < m$, are linearly independent over $R$.

The proof uses the dual family of `LinearRecurrence.shift_sub_smul_pow_chooseMulPow_apply_zero`. -/
theorem linearIndependent_chooseMulPow (r : R) (m : ℕ) :
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

/-- Let $f \colon R \to S$ be a homomorphism of commutative rings. The recurrence $E$ **pushed
forward along $f$** has the same order $k$ and the coefficients $f(c_i)$. It carries a real
recurrence to the complex recurrence whose roots the theory discusses. -/
def map {S : Type*} [CommRing S] (f : R →+* S) : LinearRecurrence S :=
  ⟨E.order, fun i => f (E.coeffs i)⟩

/-- The recurrence pushed forward along $f$ has the same order as $E$. -/
@[simp]
theorem map_order {S : Type*} [CommRing S] (f : R →+* S) : (E.map f).order = E.order := rfl

/-- The recurrence pushed forward along $f$ has the coefficients $f(c_i)$. -/
@[simp]
theorem map_coeffs {S : Type*} [CommRing S] (f : R →+* S) (i : Fin (E.map f).order) :
    (E.map f).coeffs i = f (E.coeffs i) := rfl

/-- Let $f \colon R \to S$ be a homomorphism of commutative rings. The characteristic polynomial of
the recurrence pushed forward along $f$ is the image under $f$ of the characteristic polynomial
of $E$. -/
theorem charPoly_map {S : Type*} [CommRing S] (f : R →+* S) :
    (E.map f).charPoly = E.charPoly.map f := by
  simp only [charPoly, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_monomial, map_one]
  rfl

/-- Let $f \colon R \to S$ be a homomorphism of commutative rings. If $u$ solves $E$, then
$f \circ u$ solves the recurrence pushed forward along $f$. -/
theorem isSolution_map {S : Type*} [CommRing S] (f : R →+* S) {u : ℕ → R} (hu : E.IsSolution u) :
    (E.map f).IsSolution (f ∘ u) := by
  intro n
  simp only [Function.comp_apply, map_order, hu n, map_sum, map_mul]
  rfl

/-- Let $f \colon R \to S$ be a homomorphism of commutative rings. If $u$ solves the inhomogeneous
recurrence $E$ with source $\varphi$, then $f \circ u$ solves the recurrence pushed forward
along $f$ with source $f \circ \varphi$. -/
theorem isSolutionWith_map {S : Type*} [CommRing S] (f : R →+* S) {φ u : ℕ → R}
    (hu : E.IsSolutionWith φ u) : (E.map f).IsSolutionWith (f ∘ φ) (f ∘ u) := by
  intro n
  simp only [Function.comp_apply, map_order, hu n, map_add, map_sum, map_mul]
  rfl

end CommRing

/-! ### The fundamental system -/

section Field

variable {K : Type*} [Field K] (E : LinearRecurrence K)

/-- Over a field, the solution space of a recurrence is finite-dimensional, since it has the basis
`LinearRecurrence.basis` indexed by $\{0, \dots, k-1\}$. -/
instance : FiniteDimensional K E.solSpace := Module.Finite.of_basis E.basis

/-- Let $E$ be a linear recurrence of order $k$ over a field $K$. Then the solution space of $E$ has
dimension $k$.

This is Mathlib's `LinearRecurrence.solSpace_rank`, stated with `Module.finrank`. -/
theorem finrank_solSpace : Module.finrank K E.solSpace = E.order := by
  rw [Module.finrank_eq_card_basis E.basis, Fintype.card_fin]

/-! ### Simple roots -/

/-- Let $K$ be a field and let $r_0, \dots, r_{n-1} \in K$ be distinct. Then the matrix
$(r_m^i)_{i,m}$ is nonsingular.

This is the matrix $R$ of [quarteroni2000numerical], (11.37), and the result is Exercise 5 of
Chapter 11. The matrix is the transpose of `Matrix.vandermonde r`. -/
theorem det_vandermonde_transpose_ne_zero {n : ℕ} {r : Fin n → K} (hr : Function.Injective r) :
    (Matrix.vandermonde r).transpose.det ≠ 0 := by
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.2 hr

/-- The **closed form for simple roots**. Let $E$ be a linear recurrence of order $k$ over a field
$K$, and let $r_0, \dots, r_{k-1}$ be distinct roots of its characteristic polynomial. Then for
every solution $u$ of $E$ there is a unique $\gamma \in K^k$ such that
$$u_n = \sum_{j<k} \gamma_j r_j^n \quad \text{for every } n \in \mathbb{N}.$$
This is (11.32) of [quarteroni2000numerical], and Exercise 4 of Chapter 11.

At $n = i < k$, the formula is the Vandermonde system $\sum_j \gamma_j r_j^i = u_i$, which
determines $\gamma$. The hypotheses force the characteristic polynomial to split with simple
roots. -/
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

/-! ### The general solution as polynomials times powers -/

/-- Let $K$ be a field of characteristic zero, let $r \in K$ with $r \neq 0$, and let
$s, n \in \mathbb{N}$. Then the binomial sequence is a polynomial in $n$ of degree $s$ times
$r^n$:
$$\binom{n}{s} r^{n-s} = q(n) \, r^n, \qquad q = \frac{1}{s! \, r^s} X (X - 1) \cdots (X - s +
  1).$$

The falling factorial $X (X - 1) \cdots (X - s + 1)$ is `descPochhammer K s`. -/
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

/-- The index set of the fundamental system of a recurrence over a field: the pairs $(r, s)$ with
$r$ a root of the characteristic polynomial and $s$ less than the multiplicity of $r$. When the
characteristic polynomial splits, it has $k$ elements (`LinearRecurrence.card_rootIndex`). -/
abbrev RootIndex (E : LinearRecurrence K) : Type _ :=
  Σ r : E.charPoly.roots.toFinset, Fin (E.charPoly.rootMultiplicity (r : K))

/-- The **fundamental solution** attached to the pair $(r, s)$: the binomial sequence
$n \mapsto \binom{n}{s} r^{n-s}$ (`LinearRecurrence.chooseMulPow`). -/
noncomputable def fundamentalSol (E : LinearRecurrence K) (p : E.RootIndex) : ℕ → K :=
  chooseMulPow (p.1 : K) p.2

/-- The fundamental solution attached to $(r, s)$ has the value $\binom{n}{s} r^{n-s}$ at $n$. -/
theorem fundamentalSol_apply (p : E.RootIndex) (n : ℕ) :
    E.fundamentalSol p n = (n.choose p.2 : K) * (p.1 : K) ^ (n - p.2) := rfl

/-- The fundamental solutions solve the recurrence (`LinearRecurrence.isSolution_chooseMulPow`). -/
theorem isSolution_fundamentalSol (p : E.RootIndex) : E.IsSolution (E.fundamentalSol p) :=
  E.isSolution_chooseMulPow p.2.is_lt

/-- Let $E$ be a linear recurrence over a field $K$. Then the fundamental solutions
$n \mapsto \binom{n}{s} r^{n-s}$, for all roots $r$ of the characteristic polynomial and all $s$
less than the multiplicity of $r$, are linearly independent over $K$.

Within one root, the proof uses the dual family of
`LinearRecurrence.linearIndependent_chooseMulPow`. Across roots, the fundamental solutions lie
in the generalized eigenspaces of the shift for distinct eigenvalues, which are independent
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

/-- Let $E$ be a linear recurrence of order $k$ over a field. If the characteristic polynomial
splits, then the index set of the fundamental system has $k$ elements.

The proof is the count $\sum_r m_r = \#\text{roots} = \deg \Pi = k$. -/
theorem card_rootIndex (hs : E.charPoly.Splits) : Fintype.card E.RootIndex = E.order := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_coe_sort _ (fun r => E.charPoly.rootMultiplicity r)]
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq, splits_iff_card_roots.mp hs,
    natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order]

/-- The **general solution** of a linear recurrence whose characteristic polynomial splits
([quarteroni2000numerical], (11.33)). Let $E$ be a linear recurrence over a field $K$ whose
characteristic polynomial splits. Then the fundamental solutions span the solution space of $E$. -/
theorem span_fundamentalSol_eq_solSpace (hs : E.charPoly.Splits) :
    Submodule.span K (Set.range E.fundamentalSol) = E.solSpace := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact E.isSolution_fundamentalSol p
  · rw [finrank_span_eq_card E.linearIndependent_fundamentalSol, E.card_rootIndex hs,
      E.finrank_solSpace]

/-- Let $E$ be a linear recurrence over a field $K$ whose characteristic polynomial splits. Then
every solution $u$ of $E$ is a linear combination of the fundamental solutions: $u = \sum_{(r,
s)} c_{(r,s)} \binom{n}{s} r^{n-s}$ for some coefficients $c$. -/
theorem exists_eq_sum_smul_fundamentalSol (hs : E.charPoly.Splits) {u : ℕ → K}
    (hu : E.IsSolution u) : ∃ c : E.RootIndex → K, u = ∑ p, c p • E.fundamentalSol p := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
    ((E.span_fundamentalSol_eq_solSpace hs).symm ▸ (E.is_sol_iff_mem_solSpace u).1 hu)
  exact ⟨c, hc.symm⟩

/-- The **general solution** in the form of [quarteroni2000numerical], (11.33). Let $K$ be a field
of characteristic zero, and let $E$ be a linear recurrence over $K$ whose characteristic
polynomial $\Pi$ splits and has $\Pi(0) \neq 0$. Let $u$ solve $E$. Then there are polynomials
$p_r \in K[X]$, one for each $r \in K$, with $\deg p_r$ less than the multiplicity $m_r$ of $r$
as a root of $\Pi$, such that
$$u_n = \sum_{r} p_r(n) \, r^n \quad \text{for every } n \in \mathbb{N},$$
where the sum runs over the distinct roots $r$ of $\Pi$.

The condition $\Pi(0) \neq 0$ is the condition $\alpha_0 \neq 0$ of the source. In the source,
$p_j(n) = \sum_{s < m_j} \gamma_{sj} n^s$. For $r$ not a root, $m_r = 0$ and so $p_r = 0$. The
statement fails without $\Pi(0) \neq 0$, because $n^s 0^n = 0$ for $s \ge 1$. It fails without
characteristic zero, because then $\binom{n}{s}$ is not a polynomial in $n$. The fundamental
system `LinearRecurrence.fundamentalSol` needs neither condition. -/
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
