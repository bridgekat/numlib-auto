/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Hermite
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 8.4: Hermite–Birkhoff interpolation

This module formalizes Section 8.4 of [quarteroni2000numerical], Hermite interpolation. Let
$x_0, \ldots, x_n$ be distinct nodes with multiplicities $m_0, \ldots, m_n \ge 0$, and let
$N = \sum_i (m_i + 1)$. For data $y_i^{(k)}$, $k = 0, \ldots, m_i$, there is exactly one polynomial
$H_{N-1} \in \mathbb{P}_{N-1}$ with $H_{N-1}^{(k)}(x_i) = y_i^{(k)}$; the book quotes this from
Davis. The interpolant of $f$ is $H_{N-1} = \sum_i \sum_{k \le m_i} f^{(k)}(x_i) L_{ik}$ in the
Hermite characteristic polynomials $L_{ik}$ (8.32), and its error is
$$f(x) - H_{N-1}(x) = \frac{f^{(N)}(\xi)}{N!} \, \Omega_N(x), \qquad \Omega_N(x) = \prod_{i=0}^n
  (x - x_i)^{m_i + 1}. \tag{8.33}$$
Example 8.6 treats the osculatory case $m_i = 1$, with the explicit basis $A_i$, $B_i$.

The proofs specialize the backbone module `Numlib.Approximation.Hermite`: the interpolant
`Hermite.interpolate x m f` of degree less than $N$, the unisolvence `Hermite.isUnisolvent`, the
nodal polynomial `Hermite.nodal` and the error formula `Hermite.exists_sub_interpolate_eq`.

## Main definitions

* Section 8.4, `QuarteroniSaccoSaleri.Chapter08.hermiteBasis`: the Hermite characteristic polynomial
  $L_{ik} \in \mathbb{P}_{N-1}$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.example_8_6_A`: the osculatory basis polynomial
  $A_i = (1 - 2(x - x_i) l_i'(x_i)) l_i^2$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.example_8_6_B`: the osculatory basis polynomial
  $B_i = (x - x_i) l_i^2$.

## Main results

* Section 8.4, `QuarteroniSaccoSaleri.Chapter08.hermite_existsUnique`: the Hermite interpolant
  exists and is unique.
* Section 8.4, `QuarteroniSaccoSaleri.Chapter08.hermiteBasis_spec`: $L_{ik} \in \mathbb{P}_{N-1}$
  and $L_{ik}^{(p)}(x_j) = \delta_{ij} \delta_{kp}$.
* Section 8.4, `QuarteroniSaccoSaleri.Chapter08.degree_hermiteBasis_lt`:
  $L_{ik} \in \mathbb{P}_{N-1}$.
* Section 8.4, `QuarteroniSaccoSaleri.Chapter08.eval_iterate_derivative_hermiteBasis`:
  $L_{ik}^{(p)}(x_j) = \delta_{ij} \delta_{kp}$.
* (8.32), `QuarteroniSaccoSaleri.Chapter08.equation_8_32`: $H_{N-1} = \sum_i \sum_{k \le m_i}
  f^{(k)}(x_i) L_{ik}$.
* (8.33), `QuarteroniSaccoSaleri.Chapter08.equation_8_33`: the interpolation error $f(t) -
  H_{N-1}(t) = f^{(N)}(\xi) \Omega_N(t)/N!$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.example_8_6_deriv_basis`:
  $l_i'(x_i) = \sum_{k \neq i} 1/(x_i - x_k)$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.example_8_6_A_eval`: $A_i(x_k) = \delta_{ik}$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.example_8_6_A_deriv`: $A_i'(x_k) = 0$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.example_8_6_B_eval`: $B_i(x_k) = 0$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.example_8_6_B_deriv`: $B_i'(x_k) = \delta_{ik}$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.natDegree_example_8_6_le`: $A_i$ and $B_i$ have
  degree at most $2n + 1$.
* Example 8.6, `QuarteroniSaccoSaleri.Chapter08.example_8_6`: the osculatory interpolant is
  $\sum_i (y_i A_i + y_i^{(1)} B_i)$.

## Conventions

* The nodes are an injective family `x : Fin (n + 1) → ℝ` with multiplicities `m : Fin (n + 1) → ℕ`.
  The data $f^{(k)}(x_i)$ are `iteratedDeriv k f (x i)`.
* The nodal polynomial $\Omega_N$ is `Hermite.nodal x m`.

## Not formalized

* **Section 8.4, the recursive formula for the $L_{ij}$** in terms of the $l_{ij}$. The book gives
  it as an algorithm and states nothing about it.
* **The general Hermite–Birkhoff problem**, with derivative data that have gaps. The book treats it
  only in Exercise 9 of Chapter 8, which the text does not cite.
-/

open Polynomial Set

namespace QuarteroniSaccoSaleri.Chapter08

variable {n : ℕ}

/-- **Section 8.4** of [quarteroni2000numerical], existence and uniqueness of the Hermite
interpolant, which the book quotes from Davis. Let $x_0, \ldots, x_n$ be distinct nodes, let
$m_0, \ldots, m_n \ge 0$ be multiplicities with $N = \sum_i (m_i + 1)$, and let $y_i^{(k)}$ be
data for $k = 0, \ldots, m_i$. Then there exists a unique polynomial $H_{N-1}$ of degree less
than $N$ such that
$$H_{N-1}^{(k)}(x_i) = y_i^{(k)}, \qquad i = 0, \ldots, n, \quad k = 0, \ldots, m_i.$$

The proof specializes `Hermite.isUnisolvent`. -/
theorem hermite_existsUnique {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {m : Fin (n + 1) → ℕ} {N : ℕ} (hN : ∑ i, (m i + 1) = N) (y : Fin (n + 1) → ℕ → ℝ) :
    ∃! H : ℝ[X], H.degree < N ∧ ∀ i, ∀ k ≤ m i, (derivative^[k] H).eval (x i) = y i k :=
  Hermite.isUnisolvent hx hN y

open scoped Classical in
/-- **Section 8.4** of [quarteroni2000numerical], the Hermite characteristic polynomials. For
distinct nodes $x_0, \ldots, x_n$ with multiplicities $m_0, \ldots, m_n$, the polynomial
$L_{ik} \in \mathbb{P}_{N-1}$, $k = 0, \ldots, m_i$, is defined by the relations
$$L_{ik}^{(p)}(x_j) = \begin{cases} 1 & \text{if } i = j \text{ and } k = p, \\ 0 &
  \text{otherwise}, \end{cases}$$
for all $j$ and $p = 0, \ldots, m_j$.

The definition takes the unique solution of
`QuarteroniSaccoSaleri.Chapter08.hermite_existsUnique` for these data. For nodes that are not
distinct, where the problem is in general not solvable, it is $0$. -/
noncomputable def hermiteBasis (x : Fin (n + 1) → ℝ) (m : Fin (n + 1) → ℕ) (i : Fin (n + 1))
    (k : ℕ) : ℝ[X] :=
  if hx : Function.Injective x then
    (hermite_existsUnique hx (m := m) rfl fun j p => if i = j ∧ k = p then 1 else 0).choose
  else 0

/-- **Section 8.4** of [quarteroni2000numerical], the defining property of the Hermite
characteristic polynomials. For distinct nodes, $L_{ik}$ has degree less than
$N = \sum_i (m_i + 1)$, and $L_{ik}^{(p)}(x_j) = \delta_{ij} \delta_{kp}$ for all $j$ and
$p \le m_j$. -/
theorem hermiteBasis_spec {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (m : Fin (n + 1) → ℕ)
    (i : Fin (n + 1)) (k : ℕ) :
    (hermiteBasis x m i k).degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ) ∧
      ∀ j, ∀ p ≤ m j, (derivative^[p] (hermiteBasis x m i k)).eval (x j)
        = if i = j ∧ k = p then 1 else 0 := by
  classical
  rw [hermiteBasis, dite_eq_left hx]
  exact (hermite_existsUnique hx (m := m) rfl fun j p =>
    if i = j ∧ k = p then 1 else 0).choose_spec.1

/-- **Section 8.4** of [quarteroni2000numerical]. For distinct nodes, the Hermite characteristic
polynomial $L_{ik}$ has degree less than $N = \sum_i (m_i + 1)$, that is,
$L_{ik} \in \mathbb{P}_{N-1}$. -/
theorem degree_hermiteBasis_lt {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (m : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (k : ℕ) :
    (hermiteBasis x m i k).degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ) :=
  (hermiteBasis_spec hx m i k).1

/-- **Section 8.4** of [quarteroni2000numerical]. For distinct nodes, the derivatives of the Hermite
characteristic polynomials at the nodes are $L_{ik}^{(p)}(x_j) = \delta_{ij} \delta_{kp}$ for
all $j$ and $p \le m_j$. -/
theorem eval_iterate_derivative_hermiteBasis {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (m : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (k : ℕ) (j : Fin (n + 1)) {p : ℕ} (hp : p ≤ m j) :
    (derivative^[p] (hermiteBasis x m i k)).eval (x j) = if i = j ∧ k = p then 1 else 0 :=
  (hermiteBasis_spec hx m i k).2 j p hp

/-- **Equation (8.32)** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be distinct nodes with
multiplicities $m_0, \ldots, m_n$, and let $f : \mathbb{R} \to \mathbb{R}$. Then the Hermite
interpolant of $f$ is
$$H_{N-1}(x) = \sum_{i=0}^n \sum_{k=0}^{m_i} y_i^{(k)} L_{ik}(x), \qquad y_i^{(k)} =
  f^{(k)}(x_i).$$

Both sides have degree less than $N$ and the same derivative data at the nodes, so they are
equal by the uniqueness `Hermite.eq_interpolate`. -/
theorem equation_8_32 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (m : Fin (n + 1) → ℕ)
    (f : ℝ → ℝ) :
    Hermite.interpolate x m f
      = ∑ i, ∑ k ∈ Finset.range (m i + 1), C (iteratedDeriv k f (x i)) * hermiteBasis x m i k := by
  classical
  refine (Hermite.eq_interpolate hx ?_ ?_).symm
  · have hmem : (∑ i, ∑ k ∈ Finset.range (m i + 1),
        C (iteratedDeriv k f (x i)) * hermiteBasis x m i k)
          ∈ Polynomial.degreeLT ℝ (∑ i, (m i + 1)) := by
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => ?_
      rw [← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (Polynomial.mem_degreeLT.mpr (degree_hermiteBasis_lt hx m i k))
    exact Polynomial.mem_degreeLT.mp hmem
  · intro j p hp
    simp only [Polynomial.iterate_derivative_sum, Polynomial.iterate_derivative_C_mul,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      eval_iterate_derivative_hermiteBasis hx m _ _ j hp]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single p]
      · simp
      · intro k _ hk
        simp [hk]
      · intro hpj
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hp)) hpj
    · intro i _ hij
      exact Finset.sum_eq_zero fun k _ => by simp [hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

/-- **Equation (8.33)** of [quarteroni2000numerical], the interpolation error. Let
$x_0, \ldots, x_n$ be distinct nodes in $[a, b]$ with multiplicities $m_0, \ldots, m_n$ and
$N = \sum_i (m_i + 1)$, let $f$ be of class $C^N$ on $\mathbb{R}$, and let $t \in [a, b]$. Then
there is $\xi \in [a, b]$ with
$$f(t) - H_{N-1}(t) = \frac{f^{(N)}(\xi)}{N!} \, \Omega_N(t), \qquad \Omega_N(x) = (x -
  x_0)^{m_0 + 1} \cdots (x - x_n)^{m_n + 1}.$$

The book states the formula for all $x \in \mathbb{R}$ with $\xi \in I(x; x_0, \ldots, x_n)$,
the smallest interval that contains $x$ and the nodes. Here $[a, b]$ is any interval that
contains the nodes and $t$, so the book's form is the case where $[a, b]$ is that smallest
interval. The polynomial $\Omega_N$ is `Hermite.nodal x m`, with values given by
`Hermite.eval_nodal`. The proof specializes `Hermite.exists_sub_interpolate_eq`. -/
theorem equation_8_33 {a b : ℝ} {f : ℝ → ℝ} {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hxmem : ∀ i, x i ∈ Icc a b) {m : Fin (n + 1) → ℕ} {N : ℕ} (hN : ∑ i, (m i + 1) = N)
    (hf : ContDiff ℝ (N : WithTop ℕ∞) f) {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ ξ ∈ Icc a b, f t - (Hermite.interpolate x m f).eval t
      = iteratedDeriv N f ξ / N.factorial * (Hermite.nodal x m).eval t := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := by
    refine ⟨N - 1, ?_⟩
    have : 1 ≤ ∑ i, (m i + 1) := by
      calc 1 ≤ m 0 + 1 := Nat.le_add_left 1 (m 0)
        _ ≤ ∑ i, (m i + 1) :=
          Finset.single_le_sum (f := fun i => m i + 1) (fun i _ => Nat.zero_le _)
            (Finset.mem_univ 0)
    omega
  obtain ⟨ξ, hξ, h⟩ := Hermite.exists_sub_interpolate_eq hf hx hxmem hN ht
  exact ⟨ξ, hξ, by rw [h, Hermite.eval_nodal]⟩

/-! ### Example 8.6: osculatory interpolation -/

/-- **Example 8.6** of [quarteroni2000numerical], the derivative of a Lagrange characteristic
polynomial at its own node. For distinct nodes $x_0, \ldots, x_n$,
$$l_i'(x_i) = \sum_{k \neq i} \frac{1}{x_i - x_k}.$$

The proof differentiates the product $\prod_{k \neq i} (x - x_k)/(x_i - x_k)$ logarithmically:
every factor except the differentiated one is $1$ at $x_i$. -/
theorem example_8_6_deriv_basis {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (i : Fin (n + 1)) :
    (derivative (Lagrange.basis Finset.univ x i)).eval (x i)
      = ∑ k ∈ Finset.univ.erase i, 1 / (x i - x k) := by
  rw [Lagrange.basis, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  rw [Polynomial.eval_mul, Polynomial.eval_prod, Finset.prod_eq_one, one_mul,
    Lagrange.basisDivisor, Polynomial.derivative_C_mul, Polynomial.derivative_X_sub_C, mul_one,
    Polynomial.eval_C, one_div]
  intro a ha
  have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
  exact Lagrange.eval_basisDivisor_left_of_ne fun h => hai (hx h).symm

/-- **Example 8.6** of [quarteroni2000numerical], the osculatory basis polynomial $A_i(x) = (1 -
2(x - x_i) l_i'(x_i)) \, l_i(x)^2$, where $l_i$ is the Lagrange characteristic polynomial of the
nodes $x_0, \ldots, x_n$. -/
noncomputable def example_8_6_A (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ[X] :=
  (1 - 2 * (X - C (x i)) * C ((derivative (Lagrange.basis Finset.univ x i)).eval (x i)))
    * Lagrange.basis Finset.univ x i ^ 2

/-- **Example 8.6** of [quarteroni2000numerical], the osculatory basis polynomial
$B_i(x) = (x - x_i) \, l_i(x)^2$, where $l_i$ is the Lagrange characteristic polynomial of the
nodes $x_0, \ldots, x_n$. -/
noncomputable def example_8_6_B (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ[X] :=
  (X - C (x i)) * Lagrange.basis Finset.univ x i ^ 2

/-- **Example 8.6** of [quarteroni2000numerical]. For distinct nodes, $A_i(x_k) = \delta_{ik}$. -/
theorem example_8_6_A_eval {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i k : Fin (n + 1)) :
    (example_8_6_A x i).eval (x k) = if i = k then 1 else 0 := by
  simp only [example_8_6_A, eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_pow,
    equation_8_3 hx]
  split_ifs with h
  · subst h
    ring
  · ring

/-- **Example 8.6** of [quarteroni2000numerical]. For distinct nodes, $A_i'(x_k) = 0$ for every $k$.
-/
theorem example_8_6_A_deriv {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i k : Fin (n + 1)) :
    (derivative (example_8_6_A x i)).eval (x k) = 0 := by
  simp only [example_8_6_A, derivative_mul, derivative_sub, derivative_one, derivative_C,
    derivative_X, derivative_sq, eval_mul, eval_add, eval_sub, eval_one, eval_zero, eval_C, eval_X,
    eval_pow, eval_ofNat, equation_8_3 hx]
  split_ifs with h
  · subst h
    ring
  · ring

/-- **Example 8.6** of [quarteroni2000numerical]. For distinct nodes, $B_i(x_k) = 0$ for every $k$.
-/
theorem example_8_6_B_eval {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i k : Fin (n + 1)) :
    (example_8_6_B x i).eval (x k) = 0 := by
  simp only [example_8_6_B, eval_mul, eval_sub, eval_C, eval_X, eval_pow, equation_8_3 hx]
  split_ifs with h
  · subst h
    ring
  · ring

/-- **Example 8.6** of [quarteroni2000numerical]. For distinct nodes, $B_i'(x_k) = \delta_{ik}$. -/
theorem example_8_6_B_deriv {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i k : Fin (n + 1)) :
    (derivative (example_8_6_B x i)).eval (x k) = if i = k then 1 else 0 := by
  simp only [example_8_6_B, derivative_mul, derivative_sub, derivative_C, derivative_X,
    derivative_sq, eval_mul, eval_add, eval_sub, eval_one, eval_zero, eval_C, eval_X, eval_pow,
    equation_8_3 hx]
  split_ifs with h
  · subst h
    ring
  · ring

/-- **Example 8.6** of [quarteroni2000numerical]. For distinct nodes $x_0, \ldots, x_n$, the
osculatory basis polynomials $A_i$ and $B_i$ have degree at most $2n + 1$. -/
theorem natDegree_example_8_6_le {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (i : Fin (n + 1)) :
    (example_8_6_A x i).natDegree ≤ 2 * n + 1 ∧ (example_8_6_B x i).natDegree ≤ 2 * n + 1 := by
  have hl : (Lagrange.basis Finset.univ x i).natDegree = n := by
    rw [Lagrange.natDegree_basis hx.injOn (Finset.mem_univ i)]
    simp
  have hl2 : (Lagrange.basis Finset.univ x i ^ 2).natDegree ≤ 2 * n :=
    natDegree_pow_le.trans (by rw [hl])
  constructor
  · refine natDegree_mul_le.trans ?_
    have h1 : (1 - 2 * (X - C (x i))
        * C ((derivative (Lagrange.basis Finset.univ x i)).eval (x i)) : ℝ[X]).natDegree ≤ 1 := by
      compute_degree!
    omega
  · refine natDegree_mul_le.trans ?_
    have h1 : (X - C (x i) : ℝ[X]).natDegree ≤ 1 := by compute_degree!
    omega

/-- **Example 8.6** of [quarteroni2000numerical] (osculatory interpolation). Let $x_0, \ldots, x_n$
be distinct nodes with $m_i = 1$ for $i = 0, \ldots, n$, so that $N = 2n + 2$, and let
$f : \mathbb{R} \to \mathbb{R}$. Then the Hermite interpolant of $f$ is the osculating
polynomial
$$H_{N-1}(x) = \sum_{i=0}^n \big( y_i A_i(x) + y_i^{(1)} B_i(x) \big), \qquad y_i = f(x_i),
  \quad y_i^{(1)} = f'(x_i),$$
with $A_i(x) = (1 - 2(x - x_i) l_i'(x_i)) \, l_i(x)^2$ and $B_i(x) = (x - x_i) \, l_i(x)^2$.

Both sides have degree at most $2n + 1$ and the same values and derivatives at the nodes, by
`QuarteroniSaccoSaleri.Chapter08.example_8_6_A_eval`,
`QuarteroniSaccoSaleri.Chapter08.example_8_6_A_deriv`,
`QuarteroniSaccoSaleri.Chapter08.example_8_6_B_eval` and
`QuarteroniSaccoSaleri.Chapter08.example_8_6_B_deriv`. So they are equal by the uniqueness
`Hermite.eq_interpolate`. The derivative $f'(x_i)$ is `deriv f (x i)`, which is $0$ where $f$ is
not differentiable. -/
theorem example_8_6 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (f : ℝ → ℝ) :
    Hermite.interpolate x (fun _ => 1) f
      = ∑ i, (C (f (x i)) * example_8_6_A x i + C (deriv f (x i)) * example_8_6_B x i) := by
  classical
  refine (Hermite.eq_interpolate hx ?_ ?_).symm
  · have hsum : ∑ i : Fin (n + 1), ((fun _ => 1 : Fin (n + 1) → ℕ) i + 1) = 2 * n + 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    rw [hsum]
    refine lt_of_le_of_lt (degree_le_of_natDegree_le (natDegree_sum_le_of_forall_le _ _
      fun i _ => (natDegree_add_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans (natDegree_example_8_6_le hx i).1)
        ((natDegree_C_mul_le _ _).trans (natDegree_example_8_6_le hx i).2)))) ?_
    exact_mod_cast Nat.lt_succ_self (2 * n + 1)
  · intro k p hp
    interval_cases p
    · simp only [Function.iterate_zero, id_eq, eval_finsetSum, eval_add, eval_mul, eval_C,
        example_8_6_A_eval hx, example_8_6_B_eval hx, mul_zero, add_zero, mul_ite, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, iteratedDeriv_zero]
    · simp only [Function.iterate_one, derivative_sum, derivative_add, derivative_C_mul,
        eval_finsetSum, eval_add, eval_mul, eval_C, example_8_6_A_deriv hx,
        example_8_6_B_deriv hx, mul_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, iteratedDeriv_one]

end QuarteroniSaccoSaleri.Chapter08
