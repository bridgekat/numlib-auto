import Numlib.Approximation.NewtonCotes

/-!
# Quarteroni–Sacco–Saleri §9.2: interpolatory quadratures

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.2.

The section treats the three Lagrange quadrature formulae (9.2) with `n = 0, 1, 2`: the midpoint
formula (9.5) with its error (9.6) and composite form (9.7)–(9.8), the trapezoidal formula (9.11)
with its error (9.12) and composite forms (9.13)–(9.14), and the Cavalieri–Simpson formula (9.15)
with its error (9.16) and composite form (9.17); and the discrete mean value theorem (Theorem 9.1)
by which the panel errors of a composite rule are collected into one value of the derivative.
Example 9.1 is a numerical table and is not formalized; Exercise 1, cited in Example 9.4, is
here.

The rules are the backbone's: the midpoint rule and its composite sum are
`Quadrature.midpointRule`, `Quadrature.midpointSum` (`Numlib/Approximation/NewtonCotes`), the
composite trapezoidal and Simpson sums are `Quadrature.trapezoidSum`, `Quadrature.simpsonSum`
(`Numlib/Approximation/CompositeQuadrature`), and the single-panel formulae (9.11), (9.15) are the
composite sums with one panel. The error formulae are the Peano-kernel mean value theorems of
those modules; the discrete mean value theorem is `ContinuousOn.exists_sum_mul_eq_mul_sum` of
`Numlib/Topology/Order/IntermediateValue`.

## Main results

* `theorem_9_1` — the discrete mean value theorem (9.9), for weights all of the same sign.
* `equation_9_6`, `midpoint_degreeOfExactness`, `equation_9_8` — the midpoint error `h³/3 f''(ξ)`,
  `h = (b - a)/2`, the degree of exactness `1`, and the composite error `(b - a)/24 H² f''(ξ)`.
* `equation_9_12`, `compositeTrapezoidalError` — the trapezoidal error `-h³/12 f''(ξ)`,
  `h = b - a`, and the composite error `-(b - a)/12 H² f''(ξ)`.
* `equation_9_16`, `compositeSimpsonError` — the Cavalieri–Simpson error `-h⁵/90 f⁗(ξ)`,
  `h = (b - a)/2`, and the composite error `-(b - a)/180 (H/2)⁴ f⁗(ξ)`.
* `exercise_9_1` — the ratio `-2` between the trapezoidal and midpoint errors, in the exact form
  the two kernel integrals give.

## Conventions

A real function `f ∈ C^k([a, b])` is `f : ℝ → ℝ` with `ContDiffOn ℝ k f U` on an open set
`U ⊇ [a, b]`, as chapter 8 reads Theorem 8.2 and as the chapter-9 backbone states its error
formulae; `f^{(k)}(ξ)` is `iteratedDeriv k f ξ`. The book puts the intermediate point `ξ` of every
error formula in the open interval `(a, b)`; the single-panel formulae (9.6), (9.12) and (9.16)
are stated so, and the composite ones with `ξ ∈ [a, b]`, which is what the discrete mean value
theorem on the closed interval gives (the backbone's `Quadrature.sub_composite_*_eq`). The
composite mesh is `H = (b - a)/m` with `m ≥ 1` panels, as the book writes it.
-/

open Set intervalIntegral
open scoped Polynomial

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ}

/-! ### From `C^k` on an open neighbourhood to the derivative chain on `[a, b]` -/

/-- For `f ∈ C^N` on an open set `U ⊇ [a, b]` and `j < N`, the `j`-th derivative of `f` has the
`(j + 1)`-st as its derivative at every point of `[a, b]`; the bridge from the book's regularity
hypotheses to the explicit-derivative hypotheses of the backbone's Peano-kernel theorems. -/
theorem hasDerivAt_iteratedDeriv_of_contDiffOn (hU : IsOpen U) (hUab : Icc a b ⊆ U) {N : ℕ}
    (hf : ContDiffOn ℝ N f U) {j : ℕ} (hj : j < N) :
    ∀ x ∈ Icc a b, HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x :=
  fun _ hx => hf.hasDerivAt_iteratedDeriv_of_isOpen hU hj (hUab hx)

-- TODO(backbone): a polynomial-calculus module should hold this (NewtonCotes has it privately).
/-- A real polynomial function is `C^k` on any set. -/
theorem _root_.Polynomial.contDiffOn_eval (p : ℝ[X]) (k : WithTop ℕ∞) (s : Set ℝ) :
    ContDiffOn ℝ k (fun x => p.eval x) s :=
  (by simpa [Polynomial.coe_aeval_eq_eval] using p.contDiff_aeval (𝕜 := ℝ) k :
    ContDiff ℝ k fun x => p.eval x).contDiffOn

/-- For `f ∈ C^N` on an open set `U ⊇ [a, b]`, `f` itself has `f'` as its derivative at every
point of `[a, b]`. -/
theorem hasDerivAt_of_contDiffOn (hU : IsOpen U) (hUab : Icc a b ⊆ U) {N : ℕ}
    (hf : ContDiffOn ℝ N f U) (hN : 0 < N) :
    ∀ x ∈ Icc a b, HasDerivAt f (iteratedDeriv 1 f x) x := fun x hx => by
  simpa using hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf hN x hx

/-- For `f ∈ C^N` on an open set `U ⊇ [a, b]`, `f^{(N)}` is continuous on `[a, b]`. -/
theorem continuousOn_iteratedDeriv_of_contDiffOn (hU : IsOpen U) (hUab : Icc a b ⊆ U) {N : ℕ}
    (hf : ContDiffOn ℝ N f U) : ContinuousOn (iteratedDeriv N f) (Icc a b) :=
  (hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab

/-! ### Theorem 9.1 -/

/-- **Theorem 9.1 (discrete mean value theorem).** Let `u ∈ C⁰([a, b])`, let `x₀, …, x_s` be
`s + 1` points in `[a, b]` and `δ₀, …, δ_s` be `s + 1` constants, all having the same sign. Then
there exists `η ∈ [a, b]` such that `∑ⱼ δⱼ u(xⱼ) = u(η) ∑ⱼ δⱼ` (9.9). The backbone's
`ContinuousOn.exists_sum_mul_eq_mul_sum` for nonnegative weights, applied to `-δ` when the weights
are nonpositive. -/
theorem theorem_9_1 (hab : a ≤ b) {u : ℝ → ℝ} (hu : ContinuousOn u (Icc a b)) {s : ℕ}
    {x : Fin (s + 1) → ℝ} (hx : ∀ j, x j ∈ Icc a b) {δ : Fin (s + 1) → ℝ}
    (hδ : (∀ j, 0 ≤ δ j) ∨ ∀ j, δ j ≤ 0) :
    ∃ η ∈ Icc a b, ∑ j, δ j * u (x j) = u η * ∑ j, δ j := by
  rcases hδ with hδ | hδ
  · exact hu.exists_sum_mul_eq_mul_sum hab hx hδ
  · obtain ⟨η, hη, h⟩ := hu.exists_sum_mul_eq_mul_sum hab hx (δ := fun j => -δ j)
      fun j => neg_nonneg.2 (hδ j)
    refine ⟨η, hη, ?_⟩
    simp only [neg_mul, Finset.sum_neg_distrib, mul_neg, neg_inj] at h
    exact h

/-! ### The midpoint formula (9.5)–(9.8) -/

/-- **(9.6), the midpoint error.** For `f ∈ C²([a, b])`, the error of the midpoint formula (9.5),
`I₀(f) = (b - a) f((a + b)/2)`, is `E₀(f) = h³/3 f''(ξ)` with `h = (b - a)/2` and `ξ ∈ (a, b)`.
The Peano identity `Quadrature.sub_midpoint_eq_integral_peanoKernel` with the nonnegative kernel
`Quadrature.midpointKernel`, of integral `(b - a)³/24 = h³/3`, and the weighted mean value theorem
on the open interval. -/
theorem equation_9_6 (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - (b - a) * f ((a + b) / 2)
      = ((b - a) / 2) ^ 3 / 3 * iteratedDeriv 2 f ξ := by
  have hf2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have hpeano := Quadrature.sub_midpoint_eq_integral_peanoKernel hab.le
    (hasDerivAt_of_contDiffOn hU hUab hf2 two_pos)
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf2 one_lt_two)
    ((continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2).intervalIntegrable_of_Icc hab.le)
  rw [Quadrature.midpointRule] at hpeano
  rw [hpeano]
  obtain ⟨ξ, hξ, h⟩ := Quadrature.exists_mem_Ioo_integral_mul_eq_mul_integral hab
    (Quadrature.continuous_midpointKernel a b).continuousOn
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2)
    (fun t _ => Quadrature.midpointKernel_nonneg a b t)
    (by rw [Quadrature.integral_midpointKernel hab.le]; positivity)
  refine ⟨ξ, hξ, ?_⟩
  rw [h, Quadrature.integral_midpointKernel hab.le]
  ring

/-- **§9.2.1: "the midpoint rule has degree of exactness equal to `1`."** The formula (9.5) is
exact for constant and affine functions — `f'' = 0` in (9.6) — and not for `x²`. -/
theorem midpoint_degreeOfExactness (hab : a < b) :
    (∀ p : ℝ[X], p.degree ≤ 1 →
        (∫ x in a..b, p.eval x) = (b - a) * p.eval ((a + b) / 2)) ∧
      (∫ x in a..b, x ^ 2) ≠ (b - a) * ((a + b) / 2) ^ 2 := by
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨ξ, -, h⟩ := equation_9_6 (f := fun x => p.eval x) hab isOpen_univ (subset_univ _)
      (p.contDiffOn_eval 2 univ)
    have h2 : iteratedDeriv 2 (fun x => p.eval x) ξ = 0 := by
      have hdeg : p.natDegree < 2 :=
        Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_degree_le.2 hp)
      rw [Polynomial.iteratedDeriv_eval, Polynomial.iterate_derivative_eq_zero hdeg]
      simp
    rw [h2, mul_zero, sub_eq_zero] at h
    exact h
  · rw [integral_pow]
    intro h
    have : (b - a) ^ 3 = 0 := by push_cast at h; nlinarith
    exact (pow_ne_zero 3 (sub_ne_zero.2 hab.ne')) this

/-- **(9.8), the composite midpoint error.** For `m ≥ 1`, `H = (b - a)/m`, the composite
midpoint formula (9.7), `I_{0,m}(f) = H ∑_{k<m} f(a + (2k + 1) H/2)`, has the error
`E_{0,m}(f) = (b - a)/24 H² f''(ξ)` for `f ∈ C²([a, b])` and some `ξ ∈ [a, b]`: (9.6) on each
panel and Theorem 9.1 with `u = f''`, `δⱼ = 1`. -/
theorem equation_9_8 (hab : a < b) {m : ℕ} (hm : 1 ≤ m) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.midpointSum f a ((b - a) / m) m
      = (b - a) / 24 * ((b - a) / m) ^ 2 * iteratedDeriv 2 f ξ := by
  have hf2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  exact Quadrature.sub_composite_midpoint_eq hab hm rfl (hasDerivAt_of_contDiffOn hU hUab hf2
    two_pos) (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf2 one_lt_two)
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2)

/-- The composite midpoint formula (9.7) written out: `I_{0,m}(f) = H ∑_{k<m} f(x_k)` with the
nodes `x_k = a + (2k + 1) H/2`. -/
theorem equation_9_7 (H : ℝ) (m : ℕ) :
    Quadrature.midpointSum f a H m = H * ∑ k ∈ Finset.range m, f (a + (2 * k + 1) * H / 2) := by
  rw [Quadrature.midpointSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring_nf

/-! ### The trapezoidal formula (9.11)–(9.14) -/

/-- **(9.12), the trapezoidal error.** For `f ∈ C²([a, b])`, the error of the trapezoidal formula
(9.11), `I₁(f) = (b - a)/2 (f(a) + f(b))`, is `E₁(f) = -h³/12 f''(ξ)` with `h = b - a` and
`ξ ∈ (a, b)`. The Peano identity `Quadrature.sub_trapezoid_eq_integral_peanoKernel` with the
nonpositive kernel `(t - a)(t - b)/2`, of integral `-(b - a)³/12`, and the weighted mean value
theorem on the open interval. -/
theorem equation_9_12 (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - (b - a) / 2 * (f a + f b)
      = -(b - a) ^ 3 / 12 * iteratedDeriv 2 f ξ := by
  have hf2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  rw [Quadrature.sub_trapezoid_eq_integral_peanoKernel
    (by rw [huIcc]; exact hasDerivAt_of_contDiffOn hU hUab hf2 two_pos)
    (by rw [huIcc]; exact hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf2 one_lt_two)
    ((continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2).intervalIntegrable_of_Icc hab.le)]
  obtain ⟨ξ, hξ, h⟩ := Quadrature.exists_mem_Ioo_integral_mul_eq_mul_integral_of_nonpos hab
    (K := fun t => (t - a) * (t - b) / 2) (by fun_prop)
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2)
    (fun t ht => by
      have : (t - a) * (t - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1])
        (by linarith [ht.2])
      linarith)
    (by
      rw [Quadrature.integral_peanoKernel]
      have : 0 < (b - a) ^ 3 := by positivity
      linarith)
  refine ⟨ξ, hξ, ?_⟩
  rw [h, Quadrature.integral_peanoKernel]
  ring

/-- **(9.13)–(9.14), the composite trapezoidal formula.** With the nodes `x_k = a + k H`,
`H = (b - a)/m`, `I_{1,m}(f) = (H/2) ∑_{k<m} (f(x_k) + f(x_{k+1}))` (9.13) is the backbone's
`Quadrature.trapezoidSum f a H m`, and it equals
`H [f(x₀)/2 + f(x₁) + ⋯ + f(x_{m-1}) + f(x_m)/2]` (9.14), each interior term being counted
twice. -/
theorem equation_9_14 {m : ℕ} (hm : 1 ≤ m) (H : ℝ) :
    (Quadrature.trapezoidSum f a H m
        = ∑ k ∈ Finset.range m, H / 2 * (f (a + k * H) + f (a + (k + 1) * H))) ∧
      Quadrature.trapezoidSum f a H m
        = H * ((f a + f (a + m * H)) / 2 + ∑ k ∈ Finset.Ico 1 m, f (a + k * H)) :=
  ⟨rfl, Quadrature.trapezoidSum_eq hm⟩

/-- **§9.2.2, the composite trapezoidal error.** For `f ∈ C²([a, b])`, `m ≥ 1` and
`H = (b - a)/m`, the composite trapezoidal formula (9.14) has the error
`E_{1,m}(f) = -(b - a)/12 H² f''(ξ)` for some `ξ ∈ [a, b]`. -/
theorem compositeTrapezoidalError (hab : a < b) {m : ℕ} (hm : 1 ≤ m) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.trapezoidSum f a ((b - a) / m) m
      = -(b - a) / 12 * ((b - a) / m) ^ 2 * iteratedDeriv 2 f ξ := by
  have hf2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  obtain ⟨ξ, hξ, h⟩ := Quadrature.sub_composite_trapezoid_eq hab hm rfl
    (hasDerivAt_of_contDiffOn hU hUab hf2 two_pos)
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf2 one_lt_two)
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf2)
  exact ⟨ξ, hξ, by rw [h]; ring⟩

/-! ### The Cavalieri–Simpson formula (9.15)–(9.17) -/

/-- **(9.16), the Cavalieri–Simpson error.** For `f ∈ C⁴([a, b])`, the error of the
Cavalieri–Simpson formula (9.15), `I₂(f) = (b - a)/6 (f(a) + 4 f((a + b)/2) + f(b))`, is
`E₂(f) = -h⁵/90 f⁗(ξ)` with `h = (b - a)/2` and `ξ ∈ [a, b]`. The backbone's
`Quadrature.sub_composite_simpson_eq` on one panel: `-(b - a)⁵/2880 = -h⁵/90`. -/
theorem equation_9_16 (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - (b - a) / 6 * (f a + 4 * f ((a + b) / 2) + f b)
      = -((b - a) / 2) ^ 5 / 90 * iteratedDeriv 4 f ξ := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  obtain ⟨ξ, hξ, h⟩ := Quadrature.sub_composite_simpson_eq hab one_pos (h := b - a) (by simp)
    (hasDerivAt_of_contDiffOn hU hUab hf4 four_pos)
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4)
  refine ⟨ξ, hξ, ?_⟩
  rw [Quadrature.simpsonSum, Finset.sum_range_one] at h
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul] at h
  rw [show a + (b - a) / 2 = (a + b) / 2 by ring, show a + (b - a) = b by ring] at h
  rw [h]
  ring

/-- **§9.2.3: "(9.15) has degree of exactness equal to `3`."** Simpson's formula is exact on
`ℙ₃` — `f⁗ = 0` in (9.16) — and not on `x⁴`. -/
theorem simpson_degreeOfExactness (hab : a < b) :
    (∀ p : ℝ[X], p.degree ≤ 3 →
        (∫ x in a..b, p.eval x) = (b - a) / 6 * (p.eval a + 4 * p.eval ((a + b) / 2) + p.eval b)) ∧
      (∫ x in a..b, x ^ 4) ≠ (b - a) / 6 * (a ^ 4 + 4 * ((a + b) / 2) ^ 4 + b ^ 4) := by
  refine ⟨fun p hp => Quadrature.integral_eq_simpson_of_natDegree_le hab.le
    (Polynomial.natDegree_le_iff_degree_le.2 hp), ?_⟩
  rw [integral_pow]
  intro h
  have : (b - a) ^ 5 = 0 := by push_cast at h; nlinarith
  exact (pow_ne_zero 5 (sub_ne_zero.2 hab.ne')) this

/-- **§9.2.3, the composite Simpson error.** For `f ∈ C⁴([a, b])`, `m ≥ 1` and `H = (b - a)/m`,
the composite Cavalieri–Simpson formula (9.17) — the backbone's `Quadrature.simpsonSum f a H m`,
with the nodes `x_k = a + k H/2` — has the error `E_{2,m}(f) = -(b - a)/180 (H/2)⁴ f⁗(ξ)` for
some `ξ ∈ [a, b]`. -/
theorem compositeSimpsonError (hab : a < b) {m : ℕ} (hm : 1 ≤ m) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.simpsonSum f a ((b - a) / m) m
      = -(b - a) / 180 * ((b - a) / m / 2) ^ 4 * iteratedDeriv 4 f ξ := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  obtain ⟨ξ, hξ, h⟩ := Quadrature.sub_composite_simpson_eq hab hm rfl
    (hasDerivAt_of_contDiffOn hU hUab hf4 four_pos)
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4)
  exact ⟨ξ, hξ, by rw [h]; ring⟩

/-- **(9.17), the composite Cavalieri–Simpson formula written out.** With the nodes
`x_k = a + k H/2`, `k = 0, …, 2m`, `H = (b - a)/m`, the backbone's `Quadrature.simpsonSum f a H m`
is `(H/6) [f(x₀) + 2 ∑_{r=1}^{m-1} f(x_{2r}) + 4 ∑_{s=0}^{m-1} f(x_{2s+1}) + f(x_{2m})]`. -/
theorem equation_9_17 {m : ℕ} (hm : 1 ≤ m) (H : ℝ) :
    Quadrature.simpsonSum f a H m
      = H / 6 * (f a + 2 * ∑ r ∈ Finset.Ico 1 m, f (a + (2 * r) * (H / 2))
        + 4 * ∑ s ∈ Finset.range m, f (a + (2 * s + 1) * (H / 2)) + f (a + (2 * m) * (H / 2))) := by
  set g : ℕ → ℝ := fun j => f (a + j * (H / 2)) with hg
  have hnode : ∀ j : ℕ, f (a + j * H) = g (2 * j) := fun j => by
    simp only [hg]; push_cast; ring_nf
  have hmid : ∀ j : ℕ, f (a + j * H + H / 2) = g (2 * j + 1) := fun j => by
    simp only [hg]; push_cast; ring_nf
  have hodd : ∀ s : ℕ, f (a + (2 * s + 1) * (H / 2)) = g (2 * s + 1) := fun s => by
    simp only [hg]; push_cast; ring_nf
  have heven : ∀ r : ℕ, f (a + (2 * r) * (H / 2)) = g (2 * r) := fun r => by
    simp only [hg]; push_cast; ring_nf
  -- the even-node sums: `∑_{j<m} g(2j)` and `∑_{j<m} g(2(j+1))` against the interior sum
  have hbot : ∑ j ∈ Finset.range m, g (2 * j) = g 0 + ∑ r ∈ Finset.Ico 1 m, g (2 * r) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm]
  have htop : ∑ j ∈ Finset.range m, g (2 * (j + 1))
      = (∑ j ∈ Finset.range m, g (2 * j)) + g (2 * m) - g 0 := by
    have h1 := Finset.sum_range_succ' (fun j => g (2 * j)) m
    have h2 := Finset.sum_range_succ (fun j => g (2 * j)) m
    simp only [mul_zero] at h1 h2
    linarith
  have hsplit : Quadrature.simpsonSum f a H m
      = ∑ j ∈ Finset.range m, H / 6 * (g (2 * j) + 4 * g (2 * j + 1) + g (2 * (j + 1))) := by
    rw [Quadrature.simpsonSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hnode j, hmid j, show a + ((j : ℝ) + 1) * H = a + ((j + 1 : ℕ) : ℝ) * H by push_cast; ring,
      hnode (j + 1)]
  have hlin : ∑ j ∈ Finset.range m, H / 6 * (g (2 * j) + 4 * g (2 * j + 1) + g (2 * (j + 1)))
      = H / 6 * ((∑ j ∈ Finset.range m, g (2 * j)) + 4 * ∑ j ∈ Finset.range m, g (2 * j + 1)
        + ∑ j ∈ Finset.range m, g (2 * (j + 1))) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, hlin, htop, hbot]
  simp only [hodd, heven]
  have hg0 : g 0 = f a := by simp [hg]
  rw [hg0]
  ring

/-! ### Exercise 1 -/

/-- **Exercise 1** (cited in Example 9.4): `|E₁(f)| ≃ 2 |E₀(f)|`, in its exact form. The error
constants of (9.12) and (9.6) are `-(b - a)³/12` and `(b - a)³/24`, in the ratio `-2` — the
trapezoidal Peano kernel `(t - a)(t - b)/2` and the midpoint kernel integrate to those values — so
for a quadratic `f` (whose `f''` is constant) `E₁(f) = -2 E₀(f)` exactly. -/
theorem exercise_9_1 (hab : a < b) :
    ((∫ t in a..b, (t - a) * (t - b) / 2) = -(b - a) ^ 3 / 12 ∧
      (∫ t in a..b, Quadrature.midpointKernel a b t) = (b - a) ^ 3 / 24) ∧
    ∀ p : ℝ[X], p.degree ≤ 2 →
      (∫ x in a..b, p.eval x) - (b - a) / 2 * (p.eval a + p.eval b)
        = -2 * ((∫ x in a..b, p.eval x) - (b - a) * p.eval ((a + b) / 2)) := by
  refine ⟨⟨Quadrature.integral_peanoKernel, Quadrature.integral_midpointKernel hab.le⟩,
    fun p hp => ?_⟩
  have hpc : ContDiffOn ℝ 2 (fun x => p.eval x) univ := p.contDiffOn_eval 2 univ
  obtain ⟨ξ, -, h1⟩ := equation_9_12 hab isOpen_univ (subset_univ _) hpc
  obtain ⟨η, -, h0⟩ := equation_9_6 hab isOpen_univ (subset_univ _) hpc
  -- the second derivative of a quadratic is constant
  have hconst : iteratedDeriv 2 (fun x => p.eval x) ξ = iteratedDeriv 2 (fun x => p.eval x) η := by
    rw [Polynomial.iteratedDeriv_eval]
    have hdeg : (Polynomial.derivative^[2] p).natDegree = 0 := by
      have h2 : p.natDegree ≤ 2 := Polynomial.natDegree_le_iff_degree_le.2 hp
      have := Polynomial.natDegree_iterate_derivative p 2
      omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hdeg
    simp [← hc]
  rw [h1, h0, hconst]
  ring

end QuarteroniSaccoSaleri.Chapter09
