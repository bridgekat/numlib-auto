import Numlib.Approximation.GaussLobatto

/-!
# Quarteroni–Sacco–Saleri §12.3: the spectral collocation method

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §12.3.

The boundary value problem `L u = -u'' = f` is set on `(-1, 1)` and discretized by *collocation*:
`u_n` is sought among the polynomials of degree at most `n` vanishing at both endpoints, and the
equation `L_n u_n (x_j) = f(x_j)` is imposed at the `n - 1` interior Legendre–Gauss–Lobatto nodes
(12.36), where `L_n v = L (I_n v)` is the differential operator applied to the interpolant at all
`n + 1` nodes — so `L_n v = L v` on the polynomials of degree at most `n`. With the discrete scalar
product `(u, v)_n = ∑_{j=0}^n u(x_j) v(x_j) w_j` of the Gauss–Lobatto weights (12.37), the
collocation problem is equivalent to the discrete weak form
`(L_n u_n, v_n)_n = (f, v_n)_n` for all `v_n ∈ P_n^0` (12.38), and the quadrature being exact on
`P_{2n-1}` turns the energy `(L_n v_n, v_n)_n` into `‖v_n'‖²_{L²(-1,1)}`.

## Main definitions

* `IsLegendreLobatto n x w` — the hypothesis bundle "`x`, `w` are the `n + 1` Legendre–Gauss–Lobatto
  nodes and weights of `[-1, 1]`", with `exists_isLegendreLobatto` for its nonemptiness.
* `equation_12_36 n x f p` — the spectral collocation problem (12.36).
* `equation_12_37 n x w u v` — the discrete scalar product (12.37).

## Main results

* `equation_12_37_exact` — the discrete scalar product is the integral on `P_{2n-1}`, and
  `equation_12_37_self_nonneg` that it is a positive form.
* `equation_12_38` — collocation (12.36) is the discrete weak form (12.38).
* `equation_12_38_energy` — `(L_n v, v)_n = (L_n v, v) = ‖v'‖²_{L²(-1,1)}` for `v ∈ P_n^0`.
* `exercise_12_8` — Young's inequality `ab ≤ ε a² + b²/(4ε)` (12.40), used in the proofs of
  Theorems 12.2 and 12.4.

## Not formalized here

The stability bound `‖u_n'‖_{L²} ≤ √6 C_P ‖f‖_∞` after (12.38) and Theorem 12.2 rest on results the
book quotes without proof from [CHQZ88]: the norm equivalence
`‖v_n‖_{L²} ≤ ‖v_n‖_n ≤ √3 ‖v_n‖_{L²}` on `P_n` (p. 286) and the quadrature error bound (10.36) in
weighted Sobolev norms, neither of which chapter 10 has. The plan keeps them as open nodes with the
reason.

## Conventions

Polynomials are `Polynomial ℝ` and `L v` is `-(derivative (derivative v))`; `P_n^0` is
`p.natDegree ≤ n` together with `p.eval (-1) = 0` and `p.eval 1 = 0`. The book's own statement of
(12.36) writes `P_n^0` with the conditions `p(0) = p(1) = 0` on `[0, 1]` although the problem is
posed on `(-1, 1)`; the reading here is `p(±1) = 0`, which is what the nodes and the rest of the
section use (errata).
-/

open MeasureTheory Polynomial Set

open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The Legendre–Gauss–Lobatto rule -/

/-- **The Legendre–Gauss–Lobatto nodes and weights** of `[-1, 1]` with `n + 1` points, §10.4: `x`
is injective with `x_0 = -1` and `x_n = 1`, all nodes lie in `[-1, 1]`, the weights are positive,
and the rule is exact on the polynomials of degree at most `2n - 1`. -/
structure IsLegendreLobatto (n : ℕ) (x w : Fin (n + 1) → ℝ) : Prop where
  /-- The nodes are distinct. -/
  injective : Function.Injective x
  /-- The first node is the left endpoint. -/
  first : x 0 = -1
  /-- The last node is the right endpoint. -/
  last : x (Fin.last n) = 1
  /-- Every node lies in the interval. -/
  mem : ∀ i, x i ∈ Icc (-1 : ℝ) 1
  /-- The weights are positive. -/
  weight_pos : ∀ i, 0 < w i
  /-- The rule integrates the polynomials of degree at most `2n - 1` exactly. -/
  exact : Quadrature.IsExactOnMeasure OrthogonalPolynomial.legendreMeasure w x (2 * n - 1)

/-- **The Legendre–Gauss–Lobatto rule exists** for every `n ≥ 1` (§10.4,
`Quadrature.exists_gaussLobatto` at the Legendre weight). -/
theorem exists_isLegendreLobatto {n : ℕ} (hn : 1 ≤ n) :
    ∃ x w : Fin (n + 1) → ℝ, IsLegendreLobatto n x w := by
  have hsupp : OrthogonalPolynomial.legendreMeasure (Icc (-1 : ℝ) 1)ᶜ = 0 := by
    have hempty : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioo (-1 : ℝ) 1 = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨ht1, ht2⟩
      exact ht1 ⟨ht2.1.le, ht2.2.le⟩
    rw [OrthogonalPolynomial.legendreMeasure, Measure.restrict_apply' measurableSet_Ioo, hempty,
      measure_empty]
  obtain ⟨x, w, hinj, hfirst, hlast, hmem, hwpos, hexact, -, -⟩ :=
    Quadrature.exists_gaussLobatto OrthogonalPolynomial.isWeight_legendreMeasure hsupp hn
  exact ⟨x, w, ⟨hinj, hfirst, hlast, hmem, hwpos, hexact⟩⟩

/-! ### The collocation problem (12.36) and the discrete scalar product (12.37) -/

/-- **The spectral collocation problem (12.36)**: `u_n ∈ P_n^0` with
`L_n u_n (x_j) = f(x_j)` at the interior nodes `x_1, …, x_{n-1}`, where `L = -d²/dx²` and
`L_n v = L (I_n v)` agrees with `L v` on `P_n`. -/
def equation_12_36 (n : ℕ) (x : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0 ∧
    ∀ j : Fin (n + 1), j ≠ 0 → j ≠ Fin.last n →
      -(derivative (derivative p)).eval (x j) = f (x j)

/-- **The discrete scalar product (12.37)** `(u, v)_n = ∑_{j=0}^n u(x_j) v(x_j) w_j` of the
Gauss–Lobatto rule. -/
noncomputable def equation_12_37 (n : ℕ) (x w : Fin (n + 1) → ℝ) (u v : ℝ → ℝ) : ℝ :=
  Quadrature.discreteInner w x u v

/-- (12.37) is the sum `∑_j u(x_j) v(x_j) w_j`. -/
theorem equation_12_37_eq (n : ℕ) (x w : Fin (n + 1) → ℝ) (u v : ℝ → ℝ) :
    equation_12_37 n x w u v = ∑ j, u (x j) * v (x j) * w j := by
  simp only [equation_12_37, Quadrature.discreteInner]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The discrete scalar product is the integral on `P_{2n-1}`**: for polynomials `P`, `Q` whose
product has degree at most `2n - 1`, `(P, Q)_n = ∫_{-1}^1 P Q`.  This is the exactness of the
Gauss–Lobatto rule, §10.2 and §10.4. -/
theorem equation_12_37_exact {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w)
    {P Q : ℝ[X]} (hPQ : (P * Q).degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ)) :
    equation_12_37 n x w (fun t => P.eval t) (fun t => Q.eval t)
      = ∫ t in (-1 : ℝ)..1, P.eval t * Q.eval t := by
  have h := hx.exact (P * Q) hPQ
  rw [OrthogonalPolynomial.integral_legendreMeasure] at h
  have hQ : (∫ t in (-1 : ℝ)..1, P.eval t * Q.eval t)
      = ∫ t in (-1 : ℝ)..1, (P * Q).eval t :=
    intervalIntegral.integral_congr fun t _ => by rw [eval_mul]
  simp only [equation_12_37, Quadrature.discreteInner]
  rw [hQ, ← h]
  exact Finset.sum_congr rfl fun j _ => by rw [eval_mul]; ring

/-- The discrete scalar product is a positive form: `(v, v)_n ≥ 0`. -/
theorem equation_12_37_self_nonneg {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w)
    (v : ℝ → ℝ) : 0 ≤ equation_12_37 n x w v v := by
  simp only [equation_12_37, Quadrature.discreteInner]
  refine Finset.sum_nonneg fun j _ => ?_
  have hw := (hx.weight_pos j).le
  nlinarith [sq_nonneg (v (x j))]

/-! ### The discrete weak form (12.38) -/

/-- **(12.38), the discrete weak form of the collocation problem**: `p` solves (12.36) if and only
if `p ∈ P_n^0` and `(L_n p, v_n)_n = (f, v_n)_n` for every `v_n ∈ P_n^0`.  Forwards, both sides are
sums over the nodes whose endpoint terms vanish because `v_n(±1) = 0` and whose interior terms
agree by the collocation equations; backwards, one tests with the Lagrange basis polynomial of an
interior node and divides by its positive weight. -/
theorem equation_12_38 {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w) (f : ℝ → ℝ)
    (p : ℝ[X]) :
    equation_12_36 n x f p ↔ p.natDegree ≤ n ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0 ∧
      ∀ q : ℝ[X], q.natDegree ≤ n → q.eval (-1) = 0 → q.eval 1 = 0 →
        equation_12_37 n x w (fun t => -(derivative (derivative p)).eval t) (fun t => q.eval t)
          = equation_12_37 n x w f (fun t => q.eval t) := by
  classical
  constructor
  · rintro ⟨hdeg, hm1, h1, hcoll⟩
    refine ⟨hdeg, hm1, h1, fun q _ hqm1 hq1 => ?_⟩
    simp only [equation_12_37, Quadrature.discreteInner]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj0 : j = 0
    · rw [hj0, hx.first, hqm1]
      ring
    by_cases hjn : j = Fin.last n
    · rw [hjn, hx.last, hq1]
      ring
    rw [hcoll j hj0 hjn]
  · rintro ⟨hdeg, hm1, h1, hweak⟩
    refine ⟨hdeg, hm1, h1, fun j hj0 hjn => ?_⟩
    set q := Lagrange.basis Finset.univ x j with hq
    have hqdeg : q.natDegree ≤ n := by
      rw [natDegree_le_iff_degree_le, hq,
        Lagrange.degree_basis hx.injective.injOn (Finset.mem_univ j)]
      simp
    have hqself : q.eval (x j) = 1 :=
      Lagrange.eval_basis_self hx.injective.injOn (Finset.mem_univ j)
    have hqne : ∀ k : Fin (n + 1), k ≠ j → q.eval (x k) = 0 := fun k hk =>
      Lagrange.eval_basis_of_ne (Ne.symm hk) (Finset.mem_univ k)
    have hqm1 : q.eval (-1) = 0 := by
      rw [← hx.first]
      exact hqne 0 (Ne.symm hj0)
    have hq1 : q.eval 1 = 0 := by
      rw [← hx.last]
      exact hqne (Fin.last n) (Ne.symm hjn)
    have hkey := hweak q hqdeg hqm1 hq1
    simp only [equation_12_37, Quadrature.discreteInner] at hkey
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j] at hkey
    · rw [hqself, mul_one, mul_one] at hkey
      exact mul_left_cancel₀ (hx.weight_pos j).ne' hkey
    · intro k _ hkj
      rw [hqne k hkj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
    · intro k _ hkj
      rw [hqne k hkj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

/-- **The energy identity of §12.3**: for `v ∈ P_n^0`,
`(L_n v, v)_n = (L_n v, v) = ‖v'‖²_{L²(-1,1)}`
— the discrete scalar product is exact on `v'' v ∈ P_{2n-2}`, and integration by parts costs
nothing because `v` vanishes at both endpoints.  It is the coercivity that makes the collocation
problem uniquely solvable and stable. -/
theorem equation_12_38_energy {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w)
    {v : ℝ[X]} (hdeg : v.natDegree ≤ n) (hm1 : v.eval (-1) = 0) (h1 : v.eval 1 = 0) :
    equation_12_37 n x w (fun t => -(derivative (derivative v)).eval t) (fun t => v.eval t)
      = ∫ t in (-1 : ℝ)..1, (derivative v).eval t ^ 2 := by
  -- the quadrature is exact on the product, whose degree is at most `2n - 2`
  have hprod : ((-derivative (derivative v)) * v).degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) := by
    rw [← natDegree_le_iff_degree_le]
    have d1 := natDegree_derivative_le v
    have d2 := natDegree_derivative_le (derivative v)
    have hm := natDegree_mul_le (p := -derivative (derivative v)) (q := v)
    rw [natDegree_neg] at hm
    omega
  have hex := hx.exact _ hprod
  rw [OrthogonalPolynomial.integral_legendreMeasure] at hex
  have hlhs : equation_12_37 n x w (fun t => -(derivative (derivative v)).eval t)
      (fun t => v.eval t) = ∑ j, w j * ((-derivative (derivative v)) * v).eval (x j) := by
    simp only [equation_12_37, Quadrature.discreteInner, eval_mul, eval_neg]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => (derivative v).eval t) (u' := fun t => (derivative (derivative v)).eval t)
    (v := fun t => v.eval t) (v' := fun t => (derivative v).eval t) (a := (-1 : ℝ)) (b := 1)
    (fun t _ => (derivative v).hasDerivAt t) (fun t _ => v.hasDerivAt t)
    ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)
  rw [h1, hm1, mul_zero, mul_zero, sub_zero, zero_sub] at hibp
  have e1 : (∫ t in (-1 : ℝ)..1, ((-derivative (derivative v)) * v).eval t)
      = -∫ t in (-1 : ℝ)..1, (derivative (derivative v)).eval t * v.eval t := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [eval_mul, eval_neg]
    ring
  have e2 : (∫ t in (-1 : ℝ)..1, (derivative v).eval t ^ 2)
      = ∫ t in (-1 : ℝ)..1, (derivative v).eval t * (derivative v).eval t :=
    intervalIntegral.integral_congr fun t _ => by rw [sq]
  rw [hlhs, hex, e1, e2, hibp]

/-! ### Young's inequality -/

/-- **Exercise 12.8, Young's inequality (12.40)**: `a b ≤ ε a² + b²/(4 ε)` for every `ε > 0`, used
in the proofs of Theorem 12.2 and Theorem 12.4. -/
theorem exercise_12_8 {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    a * b ≤ ε * a ^ 2 + b ^ 2 / (4 * ε) := by
  rw [← sub_nonneg]
  have h : ε * a ^ 2 + b ^ 2 / (4 * ε) - a * b = (2 * ε * a - b) ^ 2 / (4 * ε) := by
    field_simp
    ring
  rw [h]
  positivity

end QuarteroniSaccoSaleri.Chapter12
