import Numlib.Approximation.Hermite
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01

/-!
# Quarteroni–Sacco–Saleri §8.4: Hermite–Birkhoff interpolation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §8.4: existence and uniqueness of the Hermite interpolant `H_{N-1}` at
distinct nodes with multiplicities `m_i` (quoted from Davis), its representation (8.32) in the
Hermite characteristic polynomials `L_ik`, the error formula with the nodal polynomial `Ω_N`
(8.33), and the osculatory case `m_i = 1` of Example 8.6 with its explicit basis `A_i, B_i`.

The backbone is `Numlib/Approximation/Hermite`: `Hermite.interpolate x m f` (the interpolant, of
degree `< N = ∑ (m i + 1)`), `Hermite.isUnisolvent`, `Hermite.nodal` and
`Hermite.exists_sub_interpolate_eq`. The recursive formula for the `L_ij` in terms of the `l_ij`
is not a node: the book gives it as an algorithm and states nothing about it. The general
Hermite–*Birkhoff* problem (derivative data with gaps) is not treated by the book beyond Exercise
9, which the text does not cite.

## Main definitions

* `hermiteBasis x m i k` — the Hermite characteristic polynomial `L_ik ∈ 𝒫_{N-1}`, defined by
  `L_ik^{(p)}(x_j) = 1` if `i = j` and `k = p`, and `0` otherwise.
* `example_8_6_A`, `example_8_6_B` — the osculatory basis `A_i = (1 - 2(x - x_i) l_i'(x_i)) l_i²`
  and `B_i = (x - x_i) l_i²` of Example 8.6.

## Main results

* `hermite_existsUnique` — existence and uniqueness of the Hermite interpolant.
* `equation_8_32` — `H_{N-1} = ∑_i ∑_{k ≤ m_i} f^{(k)}(x_i) L_ik`.
* `equation_8_33` — the error `f(x) - H_{N-1}(x) = f^{(N)}(ξ) Ω_N(x)/N!`.
* `example_8_6_deriv_basis`, `example_8_6` — `l_i'(x_i) = ∑_{k ≠ i} 1/(x_i - x_k)` and the
  osculatory polynomial `∑_i (y_i A_i + y_i^{(1)} B_i)`.

## Conventions

Nodes are injective `x : Fin (n + 1) → ℝ` with multiplicities `m : Fin (n + 1) → ℕ`, the data
`f^{(k)}(x_i)` are `iteratedDeriv k f (x i)`, and `Ω_N` is `Hermite.nodal x m`.
-/

open Polynomial Set

namespace QuarteroniSaccoSaleri.Chapter08

variable {n : ℕ}

/-- **§8.4, existence and uniqueness of the Hermite interpolant** (quoted from Davis). For distinct
nodes `x₀, …, x_n`, multiplicities `m_i` with `N = ∑_i (m_i + 1)`, and data `y_i^{(k)}` for
`k = 0, …, m_i`, there exists a unique polynomial `H_{N-1} ∈ 𝒫_{N-1}` such that
`H_{N-1}^{(k)}(x_i) = y_i^{(k)}` for `i = 0, …, n` and `k = 0, …, m_i`: `Hermite.isUnisolvent`. -/
theorem hermite_existsUnique {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {m : Fin (n + 1) → ℕ} {N : ℕ} (hN : ∑ i, (m i + 1) = N) (y : Fin (n + 1) → ℕ → ℝ) :
    ∃! H : ℝ[X], H.degree < N ∧ ∀ i, ∀ k ≤ m i, (derivative^[k] H).eval (x i) = y i k :=
  Hermite.isUnisolvent hx hN y

open scoped Classical in
/-- **The Hermite characteristic polynomials** `L_ik ∈ 𝒫_{N-1}`, `k = 0, …, m_i`, defined through
the relations `L_ik^{(p)}(x_j) = 1` if `i = j` and `k = p`, and `0` otherwise: the unique such
polynomial given by `hermite_existsUnique` (and `0` for non-distinct nodes, where the problem is
not solvable in general). -/
noncomputable def hermiteBasis (x : Fin (n + 1) → ℝ) (m : Fin (n + 1) → ℕ) (i : Fin (n + 1))
    (k : ℕ) : ℝ[X] :=
  if hx : Function.Injective x then
    (hermite_existsUnique hx (m := m) rfl fun j p => if i = j ∧ k = p then 1 else 0).choose
  else 0

/-- The defining property of the Hermite characteristic polynomials: `L_ik ∈ 𝒫_{N-1}` and
`L_ik^{(p)}(x_j) = δ_ij δ_kp` for `p ≤ m_j`. -/
theorem hermiteBasis_spec {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (m : Fin (n + 1) → ℕ)
    (i : Fin (n + 1)) (k : ℕ) :
    (hermiteBasis x m i k).degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ) ∧
      ∀ j, ∀ p ≤ m j, (derivative^[p] (hermiteBasis x m i k)).eval (x j)
        = if i = j ∧ k = p then 1 else 0 := by
  classical
  rw [hermiteBasis, dite_eq_left hx]
  exact (hermite_existsUnique hx (m := m) rfl fun j p =>
    if i = j ∧ k = p then 1 else 0).choose_spec.1

/-- The Hermite characteristic polynomials lie in `𝒫_{N-1}`. -/
theorem degree_hermiteBasis_lt {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (m : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (k : ℕ) :
    (hermiteBasis x m i k).degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ) :=
  (hermiteBasis_spec hx m i k).1

/-- The derivatives of the Hermite characteristic polynomials at the nodes. -/
theorem eval_iterate_derivative_hermiteBasis {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (m : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (k : ℕ) (j : Fin (n + 1)) {p : ℕ} (hp : p ≤ m j) :
    (derivative^[p] (hermiteBasis x m i k)).eval (x j) = if i = j ∧ k = p then 1 else 0 :=
  (hermiteBasis_spec hx m i k).2 j p hp

/-- **(8.32).** The Hermite interpolant of `f` has the form

`H_{N-1}(x) = ∑_{i=0}^n ∑_{k=0}^{m_i} y_i^{(k)} L_ik(x)`, `y_i^{(k)} = f^{(k)}(x_i)`.

Both sides have degree `< N` and the same derivative data at the nodes, so they agree by the
uniqueness `Hermite.eq_interpolate`. -/
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

/-- **(8.33), the interpolation error.** For `f` of class `C^N`, distinct nodes `x_i ∈ [a, b]` with
`∑_i (m_i + 1) = N`, and `t ∈ [a, b]`,

`f(t) - H_{N-1}(t) = f^{(N)}(ξ)/N! · Ω_N(t)`

for some `ξ ∈ [a, b]`, where `Ω_N(x) = (x - x₀)^{m₀+1} ⋯ (x - x_n)^{m_n+1}` is `Hermite.nodal x m`
(`Hermite.eval_nodal`). The book writes "`∀ x ∈ ℝ`" with `ξ ∈ I(x; x₀, …, x_n)`; `[a, b]` is any
interval containing the nodes and `t`. The backbone's `Hermite.exists_sub_interpolate_eq`. -/
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

/-- **Example 8.6**, the derivative of a Lagrange characteristic polynomial at its own node:
`l_i'(x_i) = ∑_{k ≠ i} 1/(x_i - x_k)`. Logarithmic differentiation of the product
`∏_{k ≠ i} (x - x_k)/(x_i - x_k)`: every factor but the differentiated one is `1` at `x_i`. -/
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

/-- The osculatory basis polynomial `A_i(x) = (1 - 2(x - x_i) l_i'(x_i)) l_i(x)²` of Example 8.6. -/
noncomputable def example_8_6_A (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ[X] :=
  (1 - 2 * (X - C (x i)) * C ((derivative (Lagrange.basis Finset.univ x i)).eval (x i)))
    * Lagrange.basis Finset.univ x i ^ 2

/-- The osculatory basis polynomial `B_i(x) = (x - x_i) l_i(x)²` of Example 8.6. -/
noncomputable def example_8_6_B (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ[X] :=
  (X - C (x i)) * Lagrange.basis Finset.univ x i ^ 2

/-- `A_i(x_k) = δ_ik`. -/
theorem example_8_6_A_eval {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i k : Fin (n + 1)) :
    (example_8_6_A x i).eval (x k) = if i = k then 1 else 0 := by
  simp only [example_8_6_A, eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_pow,
    equation_8_3 hx]
  split_ifs with h
  · subst h
    ring
  · ring

/-- `A_i'(x_k) = 0` for every `k`. -/
theorem example_8_6_A_deriv {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i k : Fin (n + 1)) :
    (derivative (example_8_6_A x i)).eval (x k) = 0 := by
  simp only [example_8_6_A, derivative_mul, derivative_sub, derivative_one, derivative_C,
    derivative_X, derivative_sq, eval_mul, eval_add, eval_sub, eval_one, eval_zero, eval_C, eval_X,
    eval_pow, eval_ofNat, equation_8_3 hx]
  split_ifs with h
  · subst h
    ring
  · ring

/-- `B_i(x_k) = 0` for every `k`. -/
theorem example_8_6_B_eval {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i k : Fin (n + 1)) :
    (example_8_6_B x i).eval (x k) = 0 := by
  simp only [example_8_6_B, eval_mul, eval_sub, eval_C, eval_X, eval_pow, equation_8_3 hx]
  split_ifs with h
  · subst h
    ring
  · ring

/-- `B_i'(x_k) = δ_ik`. -/
theorem example_8_6_B_deriv {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i k : Fin (n + 1)) :
    (derivative (example_8_6_B x i)).eval (x k) = if i = k then 1 else 0 := by
  simp only [example_8_6_B, derivative_mul, derivative_sub, derivative_C, derivative_X,
    derivative_sq, eval_mul, eval_add, eval_sub, eval_one, eval_zero, eval_C, eval_X, eval_pow,
    equation_8_3 hx]
  split_ifs with h
  · subst h
    ring
  · ring

/-- The osculatory basis polynomials have degree at most `2n + 1`. -/
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

/-- **Example 8.6 (osculatory interpolation).** With `m_i = 1` for `i = 0, …, n`, so `N = 2n + 2`,
the Hermite interpolant is the osculating polynomial

`H_{N-1}(x) = ∑_{i=0}^n (y_i A_i(x) + y_i^{(1)} B_i(x))`,

with `A_i(x) = (1 - 2(x - x_i) l_i'(x_i)) l_i(x)²` and `B_i(x) = (x - x_i) l_i(x)²`. Both sides have
degree `≤ 2n + 1` and the same values and derivatives at the nodes (`example_8_6_A_eval`,
`example_8_6_A_deriv`, `example_8_6_B_eval`, `example_8_6_B_deriv`), so they agree by the
uniqueness `Hermite.eq_interpolate`. -/
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
