import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section03

/-!
# Quarteroni–Sacco–Saleri §9.4: composite Newton–Cotes formulae

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.4.

The interval `[a, b]` is partitioned into `m` subintervals `T_j = [y_j, y_{j+1}]`, `y_j = a + jH`,
`H = (b - a)/m`, and on each the closed Newton–Cotes formula with `n + 1` equally spaced nodes is
used; the composite formula is (9.25), `I_{n,m}(f) = ∑_j ∑_k α_k^{(j)} f(x_k^{(j)})` with
`α_k^{(j)} = h w_k`, `h = H/n`. Theorem 9.3 gives the error (9.26)–(9.27) — with the constant of
(9.26) corrected to `M_n/n^{n+3}` (see `notes/book-errata.md`: the closed spacing is `H/n`, and
`n = 2` must return the composite Simpson constant `-(b - a)H⁴/2880`) — and the remark after it
the convergence `E_{n,m}(f) → 0` as `m → ∞`; Property 9.1 is the convergence for merely
continuous integrands when the weights are nonnegative, with the bound `2(b - a)Ω(f; H)` by the
modulus of continuity. Example 9.4 is a numerical table and is not formalized.

The backbone is `Numlib/Approximation/NewtonCotes`: `Quadrature.compositeNewtonCotes`,
`Quadrature.exists_sub_compositeNewtonCotes_eq_of_even` (Theorem 9.3 with the corrected
constant), `Quadrature.abs_sub_compositeNewtonCotes_le` and
`Quadrature.tendsto_compositeNewtonCotes` (Property 9.1, whose bound the backbone proves with the
constant `1`; the book's `2` follows).

## Main results

* `equation_9_25` — the composite formula written as the double sum of the book.
* `theorem_9_3_even` — (9.26), the composite error for even `n`, with the corrected constant.
* `theorem_9_3_tendsto_even` — `E_{n,m}(f) → 0` as `m → ∞` for even `n`.
* `property_9_1`, `property_9_1_midpoint`, `property_9_1_bound` — convergence for `f ∈ C⁰([a, b])`
  and nonnegative weights (for the closed formulae, and for the composite midpoint formula, which
  is the open one with `n = 0`), and the modulus-of-continuity bound.

## Not yet stated

Theorem 9.3 for odd `n` (9.27) and its convergence remark wait on the backbone's odd-`n` error
formula (`Quadrature.exists_sub_compositeNewtonCotes_eq_of_odd`); their nodes are open.

## Conventions

As in §9.2. The modulus of continuity `Ω(f; H)` is `modulusOfContinuity f a b H`, the supremum
of `|f(x) - f(y)|` over `x ≠ y` in `[a, b]` with `|x - y| ≤ H`, as the book defines it.
-/

open Set Filter Topology intervalIntegral

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ}

/-! ### The composite formula (9.25) -/

/-- **(9.25).** The composite closed Newton–Cotes formula on the `m` subintervals
`T_j = [y_j, y_{j+1}]`, `y_j = a + jH`, `H = (b - a)/m`, is
`I_{n,m}(f) = ∑_{j<m} ∑_{k≤n} α_k^{(j)} f(x_k^{(j)})` with the nodes `x_k^{(j)} = y_j + k h`,
`h = H/n`, and the weights `α_k^{(j)} = h w_k`, independent of `T_j`. -/
theorem equation_9_25 (n : ℕ) (f : ℝ → ℝ) (a b : ℝ) (m : ℕ) :
    Quadrature.compositeNewtonCotes n f a b m
      = ∑ j ∈ Finset.range m, ∑ k : Fin (n + 1),
        (b - a) / m / n * Quadrature.newtonCotesWeight n k
          * f (a + j * ((b - a) / m) + k * ((b - a) / m / n)) := by
  unfold Quadrature.compositeNewtonCotes Quadrature.closedNewtonCotes
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : a + ((j : ℝ) + 1) * ((b - a) / m) - (a + j * ((b - a) / m)) = (b - a) / m := by ring
  rw [e]
  ring_nf

/-! ### Theorem 9.3 -/

/-- **Theorem 9.3, even `n`, (9.26).** For a composite closed Newton–Cotes formula with even
`n ≥ 2` and `f ∈ C^{n+2}([a, b])`,
`E_{n,m}(f) = (b - a)/(n + 2)! · M_n/n^{n+3} · H^{n+2} f^{(n+2)}(ξ)`, `H = (b - a)/m`, for some
`ξ ∈ [a, b]`. **Erratum:** the book prints `M_n/(n + 2)^{n+3}`; the panel spacing of the closed
formula is `h = H/n`, so `n^{n+3}` is the constant that makes `n = 2` return the composite
Simpson error `-(b - a)H⁴/2880` of §9.2.3. Therefore the error is an infinitesimal of order
`n + 2` in `H` and the degree of exactness is `n + 1`. The backbone's
`Quadrature.exists_sub_compositeNewtonCotes_eq_of_even`: (9.19) on each subinterval and Theorem
9.1 with `u = f^{(n+2)}`, `δ_j = 1`. -/
theorem theorem_9_3_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) {m : ℕ} (hm : 1 ≤ m)
    (hU : IsOpen U) (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.compositeNewtonCotes n f a b m
      = (b - a) / (n + 2).factorial * (Quadrature.newtonCotesM n / n ^ (n + 3))
        * ((b - a) / m) ^ (n + 2) * iteratedDeriv (n + 2) f ξ :=
  Quadrature.exists_sub_compositeNewtonCotes_eq_of_even hn hn0 hab hm hU hUab hf

/-- **§9.4: "for `n` fixed, `E_{n,m}(f) → 0` as `m → ∞`"**, for even `n` and
`f ∈ C^{n+2}([a, b])`: the bound (9.26) with `M = max |f^{(n+2)}|` and `H^{n+2} → 0`. -/
theorem theorem_9_3_tendsto_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    Tendsto (fun m => Quadrature.compositeNewtonCotes n f a b m) atTop
      (𝓝 (∫ x in a..b, f x)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf)
  set C : ℝ := (b - a) / (n + 2).factorial * (|Quadrature.newtonCotesM n| / n ^ (n + 3)) * M
    with hC
  have hbound : ∀ m : ℕ, 1 ≤ m →
      ‖Quadrature.compositeNewtonCotes n f a b m - ∫ x in a..b, f x‖
        ≤ C * ((b - a) / m) ^ (n + 2) := by
    intro m hm
    obtain ⟨ξ, hξ, h⟩ := theorem_9_3_even hn hn0 hab hm hU hUab hf
    rw [Real.norm_eq_abs, abs_sub_comm, h, abs_mul, abs_mul, abs_mul, abs_div, abs_div,
      abs_of_pos (by linarith : (0 : ℝ) < b - a),
      abs_of_pos (by positivity : (0 : ℝ) < (n + 2).factorial),
      abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ (n + 3)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((b - a) / m) ^ (n + 2)), hC]
    have := hM ξ hξ
    rw [Real.norm_eq_abs] at this
    have h0 : (0 : ℝ) ≤ (b - a) / (n + 2).factorial * (|Quadrature.newtonCotesM n| / n ^ (n + 3))
        * ((b - a) / m) ^ (n + 2) := by
      have : (0 : ℝ) ≤ b - a := by linarith
      positivity
    calc _ ≤ (b - a) / (n + 2).factorial * (|Quadrature.newtonCotesM n| / n ^ (n + 3))
          * ((b - a) / m) ^ (n + 2) * M := by gcongr
      _ = _ := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _)
    (eventually_atTop.2 ⟨1, hbound⟩) ?_
  have hH : Tendsto (fun m : ℕ => ((b - a) / (m : ℝ)) ^ (n + 2)) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (b - a)).pow (n + 2)
  simpa using hH.const_mul C

/-! ### Property 9.1 -/

/-- **Property 9.1, first clause.** Let `f ∈ C⁰([a, b])` and assume the weights of the composite
formula (9.25) are nonnegative; then `lim_{m→∞} I_{n,m}(f) = ∫_a^b f`. For the closed
Newton–Cotes formulae with `n ≥ 1` the weights are `h w_k`, so the hypothesis is `w_k ≥ 0`. The
backbone's `Quadrature.tendsto_compositeNewtonCotes`, a Riemann-sum argument. -/
theorem property_9_1 (hn : 1 ≤ n) (hw : ∀ k, 0 ≤ Quadrature.newtonCotesWeight n k) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun m => Quadrature.compositeNewtonCotes n f a b m) atTop
      (𝓝 (∫ x in a..b, f x)) :=
  Quadrature.tendsto_compositeNewtonCotes hn hw hab hf

/-- **Property 9.1 for `n = 0`**: the composite midpoint formula (9.7), the composite form of the
open formula with `n = 0` (whose weight `w₀ = 2` is positive), converges for every
`f ∈ C⁰([a, b])`. The backbone's `Quadrature.tendsto_midpointSum`. -/
theorem property_9_1_midpoint (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun m : ℕ => Quadrature.midpointSum f a ((b - a) / (m + 1)) (m + 1)) atTop
      (𝓝 (∫ x in a..b, f x)) :=
  Quadrature.tendsto_midpointSum hab hf (N := fun m => m + 1) (hs := fun m => (b - a) / (m + 1))
    (fun m => Nat.succ_pos m) (fun m => by push_cast; rfl)
    (by simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a))

/-- **The modulus of continuity** of Property 9.1,
`Ω(f; H) = sup {|f(x) - f(y)| : x, y ∈ [a, b], x ≠ y, |x - y| ≤ H}`. -/
noncomputable def modulusOfContinuity (f : ℝ → ℝ) (a b H : ℝ) : ℝ :=
  sSup {r | ∃ x ∈ Icc a b, ∃ y ∈ Icc a b, x ≠ y ∧ |x - y| ≤ H ∧ r = |f x - f y|}

/-- The modulus of continuity of a continuous function on `[a, b]` bounds every change of value
over a distance at most `H` (including `x = y`, since `Ω(f; H) ≥ 0`). -/
theorem abs_sub_le_modulusOfContinuity (hf : ContinuousOn f (Icc a b)) {H : ℝ} {x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : |x - y| ≤ H) :
    |f x - f y| ≤ modulusOfContinuity f a b H := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hbdd : BddAbove
      {r | ∃ x ∈ Icc a b, ∃ y ∈ Icc a b, x ≠ y ∧ |x - y| ≤ H ∧ r = |f x - f y|} := by
    refine ⟨2 * M, ?_⟩
    rintro r ⟨u, hu, v, hv, -, -, rfl⟩
    have h1 := hM u hu
    have h2 := hM v hv
    rw [Real.norm_eq_abs] at h1 h2
    calc |f u - f v| ≤ |f u| + |f v| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  by_cases hne : x = y
  · subst hne
    simp only [sub_self, abs_zero]
    exact Real.sSup_nonneg (by rintro r ⟨u, -, v, -, -, -, rfl⟩; exact abs_nonneg _)
  · exact le_csSup hbdd ⟨x, hx, y, hy, hne, hxy, rfl⟩

/-- The modulus of continuity is nonnegative. -/
theorem modulusOfContinuity_nonneg (f : ℝ → ℝ) (a b H : ℝ) : 0 ≤ modulusOfContinuity f a b H :=
  Real.sSup_nonneg (by rintro r ⟨u, -, v, -, -, -, rfl⟩; exact abs_nonneg _)

/-- **Property 9.1, second clause.** Under the same hypotheses,
`|∫_a^b f - I_{n,m}(f)| ≤ 2(b - a) Ω(f; H)`, `H = (b - a)/m`, where `Ω(f; H)` is the modulus of
continuity of `f`. The backbone (`Quadrature.abs_sub_compositeNewtonCotes_le`) proves the bound
with the constant `1`; the book's `2` follows since `Ω(f; H) ≥ 0`. -/
theorem property_9_1_bound (hn : 1 ≤ n) (hw : ∀ k, 0 ≤ Quadrature.newtonCotesWeight n k)
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) {m : ℕ} (hm : 1 ≤ m) :
    |(∫ x in a..b, f x) - Quadrature.compositeNewtonCotes n f a b m|
      ≤ 2 * (b - a) * modulusOfContinuity f a b ((b - a) / m) := by
  have h := Quadrature.abs_sub_compositeNewtonCotes_le hn hw hab hf hm
    (ε := modulusOfContinuity f a b ((b - a) / m))
    fun u hu v hv huv => abs_sub_le_modulusOfContinuity hf hu hv huv
  have h0 : 0 ≤ (b - a) * modulusOfContinuity f a b ((b - a) / m) :=
    mul_nonneg (by linarith) (modulusOfContinuity_nonneg f a b _)
  linarith

end QuarteroniSaccoSaleri.Chapter09
