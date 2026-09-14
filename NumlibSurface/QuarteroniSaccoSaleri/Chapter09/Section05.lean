import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section02

/-!
# Quarteroni–Sacco–Saleri §9.5: Hermite quadrature formulae

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.5.

Integrating the Hermite interpolant (9.28), `H_{2n+1} f = ∑ᵢ f(xᵢ) 𝓛ᵢ + ∑ᵢ f'(xᵢ) 𝓜ᵢ` with
`𝓛_k = [1 - (ω''(x_k)/ω'(x_k))(x - x_k)] l_k²` and `𝓜_k = (x - x_k) l_k²`, gives the Hermite
quadrature formula (9.29), `I_n(f) = ∑_k α_k f(x_k) + ∑_k β_k f'(x_k)` with `α_k = I(𝓛_k)`,
`β_k = I(𝓜_k)`, of degree of exactness `2n + 1`. With `n = 1` at the nodes `a, b` it is the
corrected trapezoidal formula (9.30), whose error is `h⁵/720 f⁗(ξ)` (9.31); its composite form
(9.32) carries the end correction `H²/12 (f'(a) - f'(b))` only, the corrections at the interior
nodes cancelling, and has an error of order `4` in `H`, as Example 9.5 observes. Exercise 9,
cited there, compares (9.31) with the Simpson error (9.16). Example 9.5 itself is a numerical
table and is not formalized.

The backbone is the Hermite section of `Numlib/Approximation/NewtonCotes`:
`Quadrature.hermiteBasisL`, `Quadrature.hermiteBasisM`, `Quadrature.hermiteQuadrature`,
`Quadrature.integral_eq_hermiteQuadrature_of_degree_le`, `Quadrature.correctedTrapezoid`,
`Quadrature.correctedTrapezoidSum` and their error theorems. The Hermite interpolant is chapter
8's `Hermite.interpolate x (fun _ => 1) f`, and (9.28) is chapter 8's Example 8.6 read with the
book's normalization of the cardinal polynomials.

## Main results

* `equation_9_28`, `equation_9_29` — the Hermite interpolant in the cardinal basis `𝓛_k, 𝓜_k`,
  and its integral, the Hermite quadrature formula.
* `hermiteQuadrature_degreeOfExactness` — the degree of exactness `2n + 1`.
* `equation_9_30`, `equation_9_31` — the corrected trapezoidal formula with its weights, and its
  error `h⁵/720 f⁗(ξ)`, `h = b - a`.
* `equation_9_32`, `compositeCorrectedTrapezoidalError` — the composite formula with the
  interior corrections cancelled, and its error `(b - a)H⁴/720 f⁗(ξ)`.
* `exercise_9_9` — `E₁^corr(f) = -4 E₂(f)` for `f` with constant fourth derivative.

## Erratum

The end correction of (9.32) is printed `(b - a)²/12 [f'(a) - f'(b)]`; on `m` panels it is
`H²/12 [f'(a) - f'(b)]` with `H = (b - a)/m`, as in the book's own Program 75
(`(h^2/12)*(f1a-f1b)`) and as the cancellation argument gives. The node states the corrected
formula.

## Conventions

As in §9.2; `f'` is `deriv f`, so that `f ∈ C⁴([a, b])` supplies it, and the error points `ξ` of
(9.31) and of the composite formula lie in `[a, b]` (the book writes `(a, b)`).
-/

open Set intervalIntegral Polynomial
open scoped Polynomial

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ}

/-! ### The Hermite interpolant (9.28) and the Hermite formula (9.29) -/

/-- The book's cardinal polynomial `𝓛_k` is chapter 8's osculatory basis polynomial `A_k` of
Example 8.6: `ω''(x_k)/ω'(x_k) = 2 l_k'(x_k)` (`Lagrange.eval_derivative_basis_self`). -/
theorem hermiteBasisL_eq_example_8_6_A {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (k : Fin (n + 1)) : Quadrature.hermiteBasisL x k = Chapter08.example_8_6_A x k := by
  rw [Quadrature.hermiteBasisL, Chapter08.example_8_6_A, Lagrange.eval_derivative_basis_self hx]
  congr 2
  rw [mul_assoc, ← C_ofNat, mul_comm (X - C (x k)), ← mul_assoc, ← C_mul]
  congr 2
  rw [mul_div_assoc', mul_div_mul_left _ _ (two_ne_zero' ℝ)]

/-- The book's cardinal polynomial `𝓜_k` is chapter 8's `B_k` of Example 8.6. -/
theorem hermiteBasisM_eq_example_8_6_B (x : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    Quadrature.hermiteBasisM x k = Chapter08.example_8_6_B x k := rfl

/-- **(9.28).** Given the `2(n + 1)` values `f(x_k), f'(x_k)` at `n + 1` distinct points, the
Hermite interpolating polynomial of `f` (§8.4) is
`H_{2n+1} f = ∑ᵢ f(xᵢ) 𝓛ᵢ + ∑ᵢ f'(xᵢ) 𝓜ᵢ`, where `𝓛_k = [1 - (ω''(x_k)/ω'(x_k))(x - x_k)] l_k²`
and `𝓜_k = (x - x_k) l_k²` are polynomials of `ℙ_{2n+1}` — chapter 8's Example 8.6, with
`ω''(x_k)/ω'(x_k) = 2 l_k'(x_k)`. -/
theorem equation_9_28 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (f : ℝ → ℝ) :
    Hermite.interpolate x (fun _ => 1) f
      = ∑ i, C (f (x i)) * Quadrature.hermiteBasisL x i
        + ∑ i, C (deriv f (x i)) * Quadrature.hermiteBasisM x i := by
  rw [Chapter08.example_8_6 hx f, Finset.sum_add_distrib]
  simp only [hermiteBasisL_eq_example_8_6_A hx, hermiteBasisM_eq_example_8_6_B]

/-- **(9.29).** Integrating (9.28) over `[a, b]` gives the Hermite quadrature formula
`I_n(f) = ∑_k α_k f(x_k) + ∑_k β_k f'(x_k)` with `α_k = I(𝓛_k)`, `β_k = I(𝓜_k)`: the backbone's
`Quadrature.hermiteQuadrature x a b f f'` is that sum by definition, and at `f' = f'` it is the
integral of the Hermite interpolant. -/
theorem equation_9_29 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (a b : ℝ) (f : ℝ → ℝ) :
    (∀ f' : ℝ → ℝ, Quadrature.hermiteQuadrature x a b f f'
        = ∑ k, (∫ t in a..b, (Quadrature.hermiteBasisL x k).eval t) * f (x k)
          + ∑ k, (∫ t in a..b, (Quadrature.hermiteBasisM x k).eval t) * f' (x k)) ∧
      Quadrature.hermiteQuadrature x a b f (deriv f)
        = ∫ t in a..b, (Hermite.interpolate x (fun _ => 1) f).eval t := by
  refine ⟨fun _ => rfl, ?_⟩
  rw [equation_9_28 hx f]
  simp only [eval_add, eval_finsetSum, eval_mul, eval_C]
  rw [integral_add
    ((by fun_prop : Continuous fun t => ∑ k, f (x k) * (Quadrature.hermiteBasisL x k).eval t)
      |>.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t =>
      ∑ k, deriv f (x k) * (Quadrature.hermiteBasisM x k).eval t) |>.intervalIntegrable _ _),
    integral_finsetSum fun k _ => ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _,
    integral_finsetSum fun k _ => ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _,
    Quadrature.hermiteQuadrature]
  simp only [integral_const_mul]
  congr 1 <;> exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **§9.5: "Formula (9.29) has degree of exactness equal to `2n + 1`."** For distinct nodes and
`p ∈ ℙ_{2n+1}`, `∫_a^b p = ∑_k α_k p(x_k) + ∑_k β_k p'(x_k)`: `p` is its own Hermite
interpolant. The backbone's `Quadrature.integral_eq_hermiteQuadrature_of_degree_le`. -/
theorem hermiteQuadrature_degreeOfExactness {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (a b : ℝ) {p : ℝ[X]} (hp : p.degree ≤ (2 * n + 1 : ℕ)) :
    (∫ t in a..b, p.eval t)
      = Quadrature.hermiteQuadrature x a b (fun t => p.eval t) (fun t => (derivative p).eval t) :=
  Quadrature.integral_eq_hermiteQuadrature_of_degree_le hx a b hp

/-! ### The corrected trapezoidal formula (9.30)–(9.32) -/

/-- **(9.30).** Taking `n = 1` at the nodes `x₀ = a`, `x₁ = b`, the Hermite formula is the
*corrected trapezoidal formula*
`I₁^corr(f) = (b - a)/2 [f(a) + f(b)] + (b - a)²/12 [f'(a) - f'(b)]`, with the weights
`α₀ = α₁ = (b - a)/2`, `β₀ = (b - a)²/12` and `β₁ = -β₀`. The identity of the two functionals is
the backbone's `Quadrature.hermiteQuadrature_two_eq_correctedTrapezoid`; the weights are read off
it at the functions supported at one node. -/
theorem equation_9_30 (hab : a ≠ b) :
    (∀ f f' : ℝ → ℝ, Quadrature.hermiteQuadrature ![a, b] a b f f'
        = (b - a) / 2 * (f a + f b) + (b - a) ^ 2 / 12 * (f' a - f' b)) ∧
      (∫ t in a..b, (Quadrature.hermiteBasisL ![a, b] 0).eval t) = (b - a) / 2 ∧
      (∫ t in a..b, (Quadrature.hermiteBasisL ![a, b] 1).eval t) = (b - a) / 2 ∧
      (∫ t in a..b, (Quadrature.hermiteBasisM ![a, b] 0).eval t) = (b - a) ^ 2 / 12 ∧
      (∫ t in a..b, (Quadrature.hermiteBasisM ![a, b] 1).eval t) = -((b - a) ^ 2 / 12) := by
  have key : ∀ f f' : ℝ → ℝ, Quadrature.hermiteQuadrature ![a, b] a b f f'
      = (b - a) / 2 * (f a + f b) + (b - a) ^ 2 / 12 * (f' a - f' b) := fun f f' =>
    Quadrature.hermiteQuadrature_two_eq_correctedTrapezoid hab f f'
  refine ⟨key, ?_, ?_, ?_, ?_⟩
  · have h := key (fun t => if t = a then 1 else 0) 0
    simp [Quadrature.hermiteQuadrature, Fin.sum_univ_two, hab.symm] at h
    linarith
  · have h := key (fun t => if t = b then 1 else 0) 0
    simp [Quadrature.hermiteQuadrature, Fin.sum_univ_two, hab] at h
    linarith
  · have h := key 0 (fun t => if t = a then 1 else 0)
    simp [Quadrature.hermiteQuadrature, Fin.sum_univ_two, hab.symm] at h
    linarith
  · have h := key 0 (fun t => if t = b then 1 else 0)
    simp [Quadrature.hermiteQuadrature, Fin.sum_univ_two, hab] at h
    linarith

/-- **(9.31).** For `f ∈ C⁴([a, b])`, the error of the corrected trapezoidal formula (9.30) is
`E₁^corr(f) = h⁵/720 f⁗(ξ)`, `h = b - a`, for some `ξ ∈ [a, b]` — of order `h⁵` like the
Cavalieri–Simpson formula, against the `h³` of (9.12). The backbone's
`Quadrature.exists_sub_correctedTrapezoid_eq`. -/
theorem equation_9_31 (hab : a ≤ b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.correctedTrapezoid f (deriv f) a b
      = (b - a) ^ 5 / 720 * iteratedDeriv 4 f ξ := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have h1 := hasDerivAt_of_contDiffOn hU hUab hf4 four_pos
  rw [iteratedDeriv_one] at h1
  exact Quadrature.exists_sub_correctedTrapezoid_eq hab h1
    (by simpa using hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num : 1 < 4))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4)

/-- **(9.32).** The composite corrected trapezoidal formula on `m` panels, `x_k = a + k H`,
`H = (b - a)/m`, is
`I^corr_{1,m}(f) = H {½[f(x₀) + f(x_m)] + f(x₁) + ⋯ + f(x_{m-1})} + H²/12 [f'(a) - f'(b)]`
(the book prints `(b - a)²/12` for the end correction; `H²/12` is the constant of its own Program
75): the panel corrections `H²/12 (f'(x_k) - f'(x_{k+1}))` telescope, so that the first
derivatives at the interior nodes `x₁, …, x_{m-1}` cancel — the sum of the corrected trapezoidal
formulae of the panels is the displayed formula. -/
theorem equation_9_32 (f f' : ℝ → ℝ) (a b : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Quadrature.correctedTrapezoidSum f f' a b m
        = (b - a) / m * ((f a + f (a + m * ((b - a) / m))) / 2
            + ∑ k ∈ Finset.Ico 1 m, f (a + k * ((b - a) / m)))
          + ((b - a) / m) ^ 2 / 12 * (f' a - f' b) ∧
      ∑ j ∈ Finset.range m,
          Quadrature.correctedTrapezoid f f' (a + j * ((b - a) / m)) (a + (j + 1) * ((b - a) / m))
        = Quadrature.correctedTrapezoidSum f f' a b m :=
  ⟨by rw [Quadrature.correctedTrapezoidSum, Quadrature.trapezoidSum_eq hm],
    (Quadrature.correctedTrapezoidSum_eq_sum f f' a b m).symm⟩

/-- **§9.5, the error of (9.32)** (the order `4` that Example 9.5 observes): for
`f ∈ C⁴([a, b])`, `m ≥ 1` and `H = (b - a)/m`,
`∫_a^b f - I^corr_{1,m}(f) = (b - a) H⁴/720 f⁗(ξ)` for some `ξ ∈ [a, b]`. The backbone's
`Quadrature.sub_correctedTrapezoidSum_eq`. -/
theorem compositeCorrectedTrapezoidalError (hab : a < b) {m : ℕ} (hm : 1 ≤ m) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.correctedTrapezoidSum f (deriv f) a b m
      = (b - a) * ((b - a) / m) ^ 4 / 720 * iteratedDeriv 4 f ξ := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have h1 := hasDerivAt_of_contDiffOn hU hUab hf4 four_pos
  rw [iteratedDeriv_one] at h1
  exact Quadrature.sub_correctedTrapezoidSum_eq hab hm h1
    (by simpa using hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num : 1 < 4))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4)

/-! ### Exercise 9 -/

/-- **Exercise 9** (cited in Example 9.5): `|E₁^corr(f)| ≃ 4 |E₂(f)|`, in its exact form. The
error constants of (9.31) and (9.16) on the same interval are `h⁵/720` and
`-(h/2)⁵/90 = -h⁵/2880`, `h = b - a`, in the ratio `-4`; so for a polynomial `f` of degree at most
`4`, whose fourth derivative is constant, `E₁^corr(f) = -4 E₂(f)` exactly. -/
theorem exercise_9_9 (hab : a < b) {p : ℝ[X]} (hp : p.degree ≤ 4) :
    (∫ x in a..b, p.eval x)
        - Quadrature.correctedTrapezoid (fun x => p.eval x) (deriv fun x => p.eval x) a b
      = -4 * ((∫ x in a..b, p.eval x)
        - (b - a) / 6 * (p.eval a + 4 * p.eval ((a + b) / 2) + p.eval b)) := by
  have hpc : ContDiffOn ℝ 4 (fun x => p.eval x) univ := p.contDiffOn_eval 4 univ
  obtain ⟨ξ, -, h1⟩ := equation_9_31 hab.le isOpen_univ (subset_univ _) hpc
  obtain ⟨η, -, h2⟩ := equation_9_16 hab isOpen_univ (subset_univ _) hpc
  have hconst : iteratedDeriv 4 (fun x => p.eval x) ξ = iteratedDeriv 4 (fun x => p.eval x) η := by
    rw [Polynomial.iteratedDeriv_eval]
    have hdeg : (Polynomial.derivative^[4] p).natDegree = 0 := by
      have h4 : p.natDegree ≤ 4 := Polynomial.natDegree_le_iff_degree_le.2 hp
      have := Polynomial.natDegree_iterate_derivative p 4
      omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hdeg
    simp [← hc]
  rw [h1, h2, hconst]
  ring

end QuarteroniSaccoSaleri.Chapter09
