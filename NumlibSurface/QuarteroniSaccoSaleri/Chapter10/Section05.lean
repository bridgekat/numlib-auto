import Numlib.Approximation.GaussRemainder
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section02

/-!
# Quarteroni–Sacco–Saleri §10.5: Gaussian integration over unbounded intervals

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §10.5.

Integration on the half line and on the whole real line by interpolatory Gaussian formulae whose
nodes are the zeros of the Laguerre and Hermite polynomials. The Laguerre polynomials
`ℒ_n(x) = e^x (d/dx)^n (e^{-x} x^n)` are orthogonal on `[0, ∞)` for the weight `e^{-x}` and satisfy
`ℒ_{n+1} = (2n + 1 - x) ℒ_n - n² ℒ_{n-1}`; writing `f = e^{-x} φ`, the Gauss–Laguerre formula
(10.41) with the `n` zeros of `ℒ_n` as nodes and weights `α_k = (n!)² x_k / ℒ_{n+1}(x_k)²` is exact
for `φ ∈ ℙ_{2n-1}`. The Hermite polynomials `ℋ_n(x) = (-1)^n e^{x²} (d/dx)^n e^{-x²}` are orthogonal
on `ℝ` for `e^{-x²}` and satisfy `ℋ_{n+1} = 2x ℋ_n - 2n ℋ_{n-1}`; the Gauss–Hermite formula (10.42)
with the zeros of `ℋ_n` and weights `α_k = 2^{n+1} n! √π / ℋ_{n+1}(x_k)²` is exact for
`φ ∈ ℙ_{2n-1}`. The remainder terms of (10.41)–(10.42) are the mean value forms
`((n!)²/(2n)!) φ^{(2n)}(ξ)` and `(n! √π / (2ⁿ (2n)!)) φ^{(2n)}(ξ)`; the book quotes them from
[DR75], and they come here from `Quadrature.exists_gauss_error_eq_of_convex`, the Gauss remainder
for a weight carried by an arbitrary interval.

The backbone is `Numlib/Approximation/OrthogonalPolynomial/Classical` — `Polynomial.laguerre`,
`Polynomial.physHermite` (the physicists' family; Mathlib's `Polynomial.hermite` is the
probabilists'), the weights `OrthogonalPolynomial.laguerreMeasure`, `hermiteMeasure`, and the
identifications `family_laguerreMeasure_eq`, `family_hermiteMeasure_eq` with the monic orthogonal
family — with the closed-form weights `Quadrature.laguerreGaussWeight_eq`,
`Quadrature.hermiteGaussWeight_eq` of `Numlib/Approximation/GaussLobatto`; exactness is (10.16) of
§10.2.

## Main results

* `laguerre` — Rodrigues' formula, the three-term recurrence and the orthogonality
  `∫_0^∞ ℒ_n ℒ_m e^{-x} dx = (n!)² δ_{nm}` of the Laguerre polynomials.
* `equation_10_41` — the Gauss–Laguerre formula: `ℒ_n` has `n` distinct zeros, and at them the
  weights `α_k = (n!)² x_k / ℒ_{n+1}(x_k)²` are positive and integrate `e^{-x} φ` exactly for every
  `φ ∈ ℙ_{2n-1}`.
* `equation_10_41_error` — the remainder of (10.41): the Gauss–Laguerre error is
  `((n!)²/(2n)!) φ^{(2n)}(ξ)` for some `ξ ∈ (0, ∞)`.
* `hermite`, `equation_10_42` — the same for the Hermite polynomials and the Gauss–Hermite
  formula with weights `α_k = 2^{n+1} n! √π / ℋ_{n+1}(x_k)²`.
* `equation_10_42_error` — the remainder of (10.42): the Gauss–Hermite error is
  `(n! √π / (2ⁿ (2n)!)) φ^{(2n)}(ξ)` for some `ξ ∈ ℝ`.

## Conventions

The book's `n` nodes `x_1, …, x_n` are `x : Fin n → ℝ`, injective; the backbone states the
weight formulas for `n + 1` nodes, which the proofs reach by writing `n = m + 1`. Exactness on
`ℙ_{2n-1}` is stated for real polynomials `φ` of degree at most `2n - 1`, in the book's form
`∫_0^∞ e^{-x} φ(x) dx = ∑_k α_k φ(x_k)` (respectively `∫_{-∞}^∞ e^{-x²} φ(x) dx`).

The book's integrand `φ` is written `g` in the remainder theorems, because `open scoped Nat` —
needed for the factorial notation `n !` — makes `φ` a token. The book's regularity hypothesis
`φ ∈ C^{2n}([0, +∞))` for (10.41) is read as `ContDiff ℝ (2n) g` on all of `ℝ`, the form in which
the backbone's Hermite interpolation error is stated; for (10.42) the book's `C^{2n}(ℝ)` is that
hypothesis verbatim. The convergence of the integral, which the book leaves implicit, is the
hypothesis `hint`.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter10

variable {n : ℕ}

/-! ### The Laguerre polynomials and the Gauss–Laguerre formula (10.41) -/

-- TODO(backbone): the Laguerre weight is carried by `(0, ∞)`; belongs beside
-- `OrthogonalPolynomial.isWeight_laguerreMeasure`.
/-- The Laguerre weight `e^{-x}` of §10.5 gives no mass outside `(0, ∞)`. -/
theorem laguerreMeasure_compl_Ioi : laguerreMeasure (Ioi (0 : ℝ))ᶜ = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply' measurableSet_Ioi, Set.compl_inter_self, measure_empty]

/-- Almost every point of the Laguerre weight of §10.5 is nonnegative. -/
theorem laguerreMeasure_ae_nonneg : ∀ᵐ t ∂laguerreMeasure, (0 : ℝ) ≤ t := by
  have h : ∀ᵐ t ∂laguerreMeasure, t ∈ Ioi (0 : ℝ) := by
    rw [MeasureTheory.ae_iff]; exact laguerreMeasure_compl_Ioi
  filter_upwards [h] with t ht using le_of_lt ht

/-- **§10.5, the Laguerre polynomials.** `ℒ_n(x) = e^x (d/dx)^n (e^{-x} x^n)`, `n ≥ 0`, are
orthogonal on `[0, ∞)` with respect to the weight `w(x) = e^{-x}`, with
`∫_0^∞ ℒ_n ℒ_m e^{-x} dx = (n!)² δ_{nm}`, and satisfy the three-term relation
`ℒ_{n+1} = (2n + 1 - x) ℒ_n - n² ℒ_{n-1}`, `n ≥ 0`, `ℒ_{-1} = 0`, `ℒ_0 = 1` — stated as `ℒ_0 = 1`,
`ℒ_1 = 1 - x` (the step `n = 0`) and the step `n + 1`. The backbone's
`Polynomial.laguerre_eq_deriv_exp_mul`, `Polynomial.laguerre_succ_succ` and
`Polynomial.integral_laguerre_mul_laguerre`. -/
theorem laguerre (n m : ℕ) (x : ℝ) :
    (Polynomial.laguerre n).eval x = exp x * deriv^[n] (fun y => exp (-y) * y ^ n) x ∧
      Polynomial.laguerre 0 = 1 ∧ Polynomial.laguerre 1 = 1 - X ∧
      Polynomial.laguerre (n + 2) =
        (C (2 * ((n : ℝ) + 1) + 1) - X) * Polynomial.laguerre (n + 1) -
          C (((n : ℝ) + 1) ^ 2) * Polynomial.laguerre n ∧
      ∫ x in Ioi (0 : ℝ), (Polynomial.laguerre n).eval x * (Polynomial.laguerre m).eval x *
        exp (-x) = if n = m then (n ! : ℝ) ^ 2 else 0 :=
  ⟨Polynomial.laguerre_eq_deriv_exp_mul n x, Polynomial.laguerre_zero, Polynomial.laguerre_one, by
    rw [show 2 * ((n : ℝ) + 1) + 1 = 2 * n + 3 by ring]
    exact Polynomial.laguerre_succ_succ n, Polynomial.integral_laguerre_mul_laguerre n m⟩

/-- **(10.41), the Gauss–Laguerre formula: nodes, weights and exactness.** For `n ≥ 1`, the
Laguerre polynomial `ℒ_n` has `n` distinct zeros `x_1, …, x_n`; with the weights
`α_k = (n!)² x_k / ℒ_{n+1}(x_k)²`, which are positive,

`∫_0^∞ e^{-x} φ(x) dx = ∑_{k=1}^n α_k φ(x_k)` for every `φ ∈ ℙ_{2n-1}`,

so the formula is exact for `f = φ e^{-x}` with `φ ∈ ℙ_{2n-1}`: it has degree of exactness
`2n - 1`. The zeros are those of the monic orthogonal polynomial of the weight `e^{-x}`
(`OrthogonalPolynomial.family_laguerreMeasure_eq`), so exactness is (10.16) with the interpolatory
weights, which `Quadrature.laguerreGaussWeight_eq` puts in closed form. The remainder term of
(10.41) is `equation_10_41_error`. -/
theorem equation_10_41 (hn : 1 ≤ n) :
    (∃ x : Fin n → ℝ, Function.Injective x ∧ ∀ k, (Polynomial.laguerre n).eval (x k) = 0) ∧
      ∀ x : Fin n → ℝ, Function.Injective x → (∀ k, (Polynomial.laguerre n).eval (x k) = 0) →
        (∀ k, 0 < (n ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 1)).eval (x k) ^ 2) ∧
        ∀ p : ℝ[X], p.degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) →
          ∫ x in Ioi (0 : ℝ), exp (-x) * p.eval x =
            ∑ k, (n ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 1)).eval (x k) ^ 2 *
              p.eval (x k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw := isWeight_laguerreMeasure
  have hfam : ∀ x : ℝ, (family laguerreMeasure (m + 1)).eval x = 0 ↔
      (Polynomial.laguerre (m + 1)).eval x = 0 := fun x => by
    rw [family_laguerreMeasure_eq, eval_mul, eval_C, mul_eq_zero, or_iff_right (by simp)]
  refine ⟨?_, fun x hx hroot => ?_⟩
  · obtain ⟨x, hx, hroot⟩ := exists_gauss_nodes hw m
    exact ⟨x, hx, fun k => (hfam _).mp (hroot k)⟩
  -- the interpolatory weights are exact and equal the closed form
  set α : Fin (m + 1) → ℝ := fun k => ∫ t, (Lagrange.basis Finset.univ x k).eval t ∂laguerreMeasure
    with hα
  have hint : IsInterpolatoryMeasure laguerreMeasure α x := fun k => rfl
  have hexact : IsExactOnMeasure laguerreMeasure α x (2 * m + 1) :=
    (equation_10_16 hw hx α).mpr ⟨fun k => (hfam _).mpr (hroot k), hint⟩
  have hform : ∀ k, α k = ((m + 1)! : ℝ) ^ 2 * x k /
      (Polynomial.laguerre (m + 1 + 1)).eval (x k) ^ 2 := fun k =>
    laguerreGaussWeight_eq hx hint hroot k
  refine ⟨fun k => hform k ▸ pos_of_isExactOnMeasure_of_le hw hx (by omega) hexact k,
    fun p hp => ?_⟩
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at hp
  rw [← integral_laguerreMeasure, ← hexact p hp]
  exact Finset.sum_congr rfl fun k _ => by rw [hform k]

/-- **(10.41), the remainder of the Gauss–Laguerre formula.** For `n ≥ 1`, nodes `x_1, …, x_n`
the distinct zeros of `ℒ_n`, weights `α_k = (n!)² x_k / ℒ_{n+1}(x_k)²` and an integrand
`g ∈ C^{2n}` for which `e^{-x} g` is integrable on `(0, ∞)`,

`∫_0^∞ e^{-x} g(x) dx = ∑_{k=1}^n α_k g(x_k) + ((n!)²/(2n)!) g^{(2n)}(ξ)`, `0 < ξ < +∞`,

stated as the error `∫ - ∑`. The book quotes this from [DR75]; it is
`Quadrature.exists_gauss_error_eq_of_convex` for the weight `OrthogonalPolynomial.laguerreMeasure`
carried by the convex set `(0, ∞)`, whose nodes lie in `(0, ∞)` by
`OrthogonalPolynomial.lt_root_family` and whose `∫ p_n² ∂μ` is `(n!)²`
(`OrthogonalPolynomial.normSq_laguerreMeasure`). -/
theorem equation_10_41_error (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : Function.Injective x)
    (hroot : ∀ k, (Polynomial.laguerre n).eval (x k) = 0) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) g)
    (hint : IntegrableOn (fun t => exp (-t) * g t) (Ioi 0)) :
    ∃ ξ ∈ Ioi (0 : ℝ),
      (∫ t in Ioi (0 : ℝ), exp (-t) * g t) -
          ∑ k, (n ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 1)).eval (x k) ^ 2 * g (x k) =
        ((n ! : ℝ) ^ 2 / (2 * n)!) * iteratedDeriv (2 * n) g ξ := by
  have hw := isWeight_laguerreMeasure
  set α : Fin n → ℝ :=
    fun k => (n ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 1)).eval (x k) ^ 2
  have hfam : ∀ k, (family laguerreMeasure n).eval (x k) = 0 := fun k => by
    rw [family_laguerreMeasure_eq, eval_mul, eval_C, hroot k, mul_zero]
  have hxmem : ∀ k, x k ∈ Ioi (0 : ℝ) := fun k =>
    lt_root_family hw laguerreMeasure_ae_nonneg (hfam k)
  have hexact0 : IsExactOnMeasure laguerreMeasure α x (2 * n - 1) := by
    intro p hp
    rw [integral_laguerreMeasure]
    exact (((equation_10_41 hn).2 x hx hroot).2 p hp).symm
  have hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ k, α k * p.eval (x k) = ∫ t, p.eval t ∂laguerreMeasure := by
    have h := isExactOnMeasure_iff_forall_degree_lt.mp hexact0
    rwa [show 2 * n - 1 + 1 = 2 * n by omega] at h
  have hgint : Integrable g laguerreMeasure := (integrable_laguerreMeasure_iff g).mpr hint
  obtain ⟨ξ, hξ, heq⟩ := exists_gauss_error_eq_of_convex hw (convex_Ioi 0)
    laguerreMeasure_compl_Ioi hx hxmem hexact hg hgint
  refine ⟨ξ, hξ, ?_⟩
  rw [← integral_laguerreMeasure, heq, normSq_laguerreMeasure]
  ring

/-! ### The Hermite polynomials and the Gauss–Hermite formula (10.42) -/

/-- **§10.5, the Hermite polynomials.** `ℋ_n(x) = (-1)^n e^{x²} (d/dx)^n e^{-x²}`, `n ≥ 0`, are
orthogonal on the real line with respect to the weight `w(x) = e^{-x²}`, with
`∫ ℋ_n ℋ_m e^{-x²} dx = 2^n n! √π δ_{nm}`, and are generated recursively by
`ℋ_{n+1} = 2x ℋ_n - 2n ℋ_{n-1}`, `n ≥ 0`, `ℋ_{-1} = 0`, `ℋ_0 = 1` — stated as `ℋ_0 = 1`,
`ℋ_1 = 2x` and the step `n + 1`. These are the physicists' Hermite polynomials, the backbone's
`Polynomial.physHermite` (Mathlib's `Polynomial.hermite` is the probabilists' family), with
`Polynomial.physHermite_eq_deriv_gaussian`, `Polynomial.physHermite_succ_succ` and
`Polynomial.integral_physHermite_mul_physHermite`. -/
theorem hermite (n m : ℕ) (x : ℝ) :
    (Polynomial.physHermite n).eval x =
        (-1) ^ n * exp (x ^ 2) * deriv^[n] (fun y => exp (-y ^ 2)) x ∧
      Polynomial.physHermite 0 = 1 ∧ Polynomial.physHermite 1 = 2 * X ∧
      Polynomial.physHermite (n + 2) =
        2 * X * Polynomial.physHermite (n + 1) - C (2 * ((n : ℝ) + 1)) * Polynomial.physHermite n ∧
      ∫ x, (Polynomial.physHermite n).eval x * (Polynomial.physHermite m).eval x * exp (-x ^ 2) =
        if n = m then 2 ^ n * (n ! : ℝ) * √π else 0 :=
  ⟨Polynomial.physHermite_eq_deriv_gaussian n x, Polynomial.physHermite_zero,
    Polynomial.physHermite_one, Polynomial.physHermite_succ_succ n,
    Polynomial.integral_physHermite_mul_physHermite n m⟩

/-- **(10.42), the Gauss–Hermite formula: nodes, weights and exactness.** For `n ≥ 1`, the Hermite
polynomial `ℋ_n` has `n` distinct zeros `x_1, …, x_n`; with the weights
`α_k = 2^{n+1} n! √π / ℋ_{n+1}(x_k)²`, which are positive,

`∫_{-∞}^{∞} e^{-x²} φ(x) dx = ∑_{k=1}^n α_k φ(x_k)` for every `φ ∈ ℙ_{2n-1}`,

so the formula is exact for `f = φ e^{-x²}` with `φ ∈ ℙ_{2n-1}`: it has degree of exactness
`2n - 1`. As for (10.41), through `OrthogonalPolynomial.family_hermiteMeasure_eq`, (10.16) and
`Quadrature.hermiteGaussWeight_eq`. The remainder term of (10.42) is `equation_10_42_error`. -/
theorem equation_10_42 (hn : 1 ≤ n) :
    (∃ x : Fin n → ℝ, Function.Injective x ∧ ∀ k, (Polynomial.physHermite n).eval (x k) = 0) ∧
      ∀ x : Fin n → ℝ, Function.Injective x → (∀ k, (Polynomial.physHermite n).eval (x k) = 0) →
        (∀ k, 0 < 2 ^ (n + 1) * (n ! : ℝ) * √π / (Polynomial.physHermite (n + 1)).eval (x k) ^ 2) ∧
        ∀ p : ℝ[X], p.degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) →
          ∫ x, exp (-x ^ 2) * p.eval x =
            ∑ k, 2 ^ (n + 1) * (n ! : ℝ) * √π / (Polynomial.physHermite (n + 1)).eval (x k) ^ 2 *
              p.eval (x k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw := isWeight_hermiteMeasure
  have hfam : ∀ x : ℝ, (family hermiteMeasure (m + 1)).eval x = 0 ↔
      (Polynomial.physHermite (m + 1)).eval x = 0 := fun x => by
    rw [family_hermiteMeasure_eq, eval_mul, eval_C, mul_eq_zero, or_iff_right (by simp)]
  refine ⟨?_, fun x hx hroot => ?_⟩
  · obtain ⟨x, hx, hroot⟩ := exists_gauss_nodes hw m
    exact ⟨x, hx, fun k => (hfam _).mp (hroot k)⟩
  set α : Fin (m + 1) → ℝ := fun k => ∫ t, (Lagrange.basis Finset.univ x k).eval t ∂hermiteMeasure
    with hα
  have hint : IsInterpolatoryMeasure hermiteMeasure α x := fun k => rfl
  have hexact : IsExactOnMeasure hermiteMeasure α x (2 * m + 1) :=
    (equation_10_16 hw hx α).mpr ⟨fun k => (hfam _).mpr (hroot k), hint⟩
  have hform : ∀ k, α k = 2 ^ (m + 1 + 1) * ((m + 1)! : ℝ) * √π /
      (Polynomial.physHermite (m + 1 + 1)).eval (x k) ^ 2 := fun k =>
    hermiteGaussWeight_eq hx hint hroot k
  refine ⟨fun k => hform k ▸ pos_of_isExactOnMeasure_of_le hw hx (by omega) hexact k,
    fun p hp => ?_⟩
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at hp
  rw [← integral_hermiteMeasure, ← hexact p hp]
  exact Finset.sum_congr rfl fun k _ => by rw [hform k]


/-- **(10.42), the remainder of the Gauss–Hermite formula.** For `n ≥ 1`, nodes `x_1, …, x_n` the
distinct zeros of `ℋ_n`, weights `α_k = 2^{n+1} n! √π / ℋ_{n+1}(x_k)²` and an integrand
`g ∈ C^{2n}(ℝ)` for which `e^{-x²} g` is integrable,

`∫_{-∞}^∞ e^{-x²} g(x) dx = ∑_{k=1}^n α_k g(x_k) + (n! √π / (2ⁿ (2n)!)) g^{(2n)}(ξ)`, `ξ ∈ ℝ`,

stated as the error `∫ - ∑`. As for (10.41), this is
`Quadrature.exists_gauss_error_eq_of_convex` for `OrthogonalPolynomial.hermiteMeasure`, carried by
the convex set `ℝ`, with `∫ p_n² ∂μ = n! √π / 2ⁿ`
(`OrthogonalPolynomial.normSq_hermiteMeasure`). -/
theorem equation_10_42_error (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : Function.Injective x)
    (hroot : ∀ k, (Polynomial.physHermite n).eval (x k) = 0) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) g)
    (hint : Integrable fun t => exp (-t ^ 2) * g t) :
    ∃ ξ : ℝ,
      (∫ t, exp (-t ^ 2) * g t) -
          ∑ k, 2 ^ (n + 1) * (n ! : ℝ) * √π / (Polynomial.physHermite (n + 1)).eval (x k) ^ 2 *
            g (x k) =
        ((n ! : ℝ) * √π / (2 ^ n * (2 * n)!)) * iteratedDeriv (2 * n) g ξ := by
  have hw := isWeight_hermiteMeasure
  set α : Fin n → ℝ :=
    fun k => 2 ^ (n + 1) * (n ! : ℝ) * √π / (Polynomial.physHermite (n + 1)).eval (x k) ^ 2
  have hexact0 : IsExactOnMeasure hermiteMeasure α x (2 * n - 1) := by
    intro p hp
    rw [integral_hermiteMeasure]
    exact (((equation_10_42 hn).2 x hx hroot).2 p hp).symm
  have hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ k, α k * p.eval (x k) = ∫ t, p.eval t ∂hermiteMeasure := by
    have h := isExactOnMeasure_iff_forall_degree_lt.mp hexact0
    rwa [show 2 * n - 1 + 1 = 2 * n by omega] at h
  have hgint : Integrable g hermiteMeasure := (integrable_hermiteMeasure_iff g).mpr hint
  obtain ⟨ξ, -, heq⟩ := exists_gauss_error_eq_of_convex hw convex_univ (by simp) hx
    (fun _ => Set.mem_univ _) hexact hg hgint
  refine ⟨ξ, ?_⟩
  rw [← integral_hermiteMeasure, heq, normSq_hermiteMeasure]
  ring

end QuarteroniSaccoSaleri.Chapter10
