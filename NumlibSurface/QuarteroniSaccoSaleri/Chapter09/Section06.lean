import Numlib.Approximation.Extrapolation
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section02

/-!
# Quarteroni–Sacco–Saleri §9.6: Richardson extrapolation and Romberg integration

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.6.

A quantity `𝒜(h)` with the expansion (9.33), `𝒜(h) = α₀ + α₁ h + ⋯ + α_k h^k + ℛ_{k+1}(h)`,
`|ℛ_{k+1}(h)| ≤ C_{k+1} h^{k+1}`, is combined at `h` and `δh` to kill the leading error term:
`ℬ(h) = (𝒜(δh) - δ^p 𝒜(h))/(1 - δ^p)` approximates `α₀` to order `p + 1` when `𝒜` has order `p`;
iterating gives the extrapolation table (9.34) and Property 9.2, `𝒜_{m,q} = α₀ + O((δ^m h)^{q+1})`.
Romberg integration (§9.6.1) is the table built on the composite trapezoidal rule with `2^m`
panels, whose expansion in `h_m²` is the Euler–Maclaurin formula (Property 9.3); the recursion
becomes (9.37), with `δ = 1/2` the `4^{q+1}` recursion, and the entries converge at order
`h_s^{2(n+1)}`. Examples 9.6 and 9.7 are numerical tables and are not formalized.

The backbone is `Numlib/Approximation/Extrapolation` (`Richardson.HasExpansion`,
`Richardson.step`, `Richardson.table`, `Romberg.table` and their theorems) and
`Numlib/Analysis/SpecialFunctions/EulerMaclaurin`. Everything is stated for the *sampled*
sequence `A m = 𝒜(δ^m h)`, which is what the algorithm (9.34) consumes.

## Main results

* `equation_9_33`, `equation_9_33_iff` — the expansion (9.33) for the sampled sequence.
* `richardsonStep` — one extrapolation step raises the order from `p` to `p + 1`, and
  `α̃ᵢ ≠ 0 ↔ αᵢ ≠ 0`.
* `equation_9_34`, `property_9_2` — the table and its convergence, in the reading
  `𝒜_{m,q} = α₀ + O((δ^m h)^{q+1})` for `q ≤ m` (see the erratum below).
* `property_9_3`, `bernoulliNumber_eq` — the Euler–Maclaurin formula (9.36), with Mathlib's
  Bernoulli numbers, and their agreement with the book's zeta-series definition.
* `equation_9_37`, `rombergConvergence` — the Romberg recursion in its two forms and the
  convergence `𝒜_{m,n} = ∫_a^b f + O(h_s^{2(n+1)})`.

## Erratum

Property 9.2 prints `𝒜_{m,n} = α₀ + O((δ^m h)^{n+1})` for `m = 0, …, n`, but (9.34) defines
`𝒜_{m,q}` only for `m ≥ q`. The statement proved, [Com95] Proposition 4.1, is
`𝒜_{m,q} = α₀ + O((δ^m h)^{q+1})` for `q ≤ m`, with a constant independent of `m`.

## Conventions

`𝒜(δ^m h)` is `A m` for `A : ℕ → ℝ`; `f ∈ C^{2k+2}([a, b])` is as in §9.2; `B_j` is Mathlib's
`bernoulli j : ℚ`, cast to `ℝ`.
-/

open Set Filter Topology intervalIntegral
open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ}

/-! ### Richardson extrapolation -/

/-- **(9.33), sampled at `h, δh, δ²h, …`.** `𝒜(δ^m h) = α₀ + α₁ (δ^m h) + ⋯ + α_k (δ^m h)^k +
ℛ_{k+1}(δ^m h)` with `|ℛ_{k+1}(δ^m h)| ≤ C_{k+1} (δ^m h)^{k+1}` for every `m`: the backbone's
`Richardson.HasExpansion A δ h α k C` for the sequence `A m = 𝒜(δ^m h)`. -/
def equation_9_33 (A : ℕ → ℝ) (δ h : ℝ) (α : ℕ → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  Richardson.HasExpansion A δ h α k C

/-- (9.33) unfolded: the remainder after the `k`-th term is bounded by `C (δ^m h)^{k+1}`. -/
theorem equation_9_33_iff (A : ℕ → ℝ) (δ h : ℝ) (α : ℕ → ℝ) (k : ℕ) (C : ℝ) :
    equation_9_33 A δ h α k C ↔
      ∀ m, |A m - ∑ i ∈ Finset.range (k + 1), α i * (δ ^ m * h) ^ i| ≤ C * (δ ^ m * h) ^ (k + 1) :=
  Iff.rfl

/-- **§9.6, the effect of one extrapolation step.** If `𝒜(h)` is an approximation of `α₀` of
order `p` — (9.33) with `α₁ = ⋯ = α_{p-1} = 0`, `1 ≤ p ≤ k` — then
`ℬ(h) = (𝒜(δh) - δ^p 𝒜(h))/(1 - δ^p)` approximates `α₀` up to order `p + 1` at least:
`|ℬ(δ^m h) - α₀| ≤ C' (δ^m h)^{p+1}` for every `m`. Moreover the new coefficients are
`α̃ᵢ = αᵢ (δ^i - δ^p)/(1 - δ^p)`, so that `α̃ᵢ ≠ 0` iff `αᵢ ≠ 0` for `i ≠ p` (the case `p = 1` is
the book's first display, `ℬ(h) = α₀ + α̃₂ h² + ⋯`). The backbone's
`Richardson.hasExpansion_step`, whose expansion has `α̃₁ = ⋯ = α̃_p = 0`, and
`Richardson.abs_sub_le_of_hasExpansion`. -/
theorem richardsonStep {A : ℕ → ℝ} {δ h : ℝ} {α : ℕ → ℝ} {k : ℕ} {C : ℝ}
    (hA : equation_9_33 A δ h α k C) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) {p : ℕ}
    (hp : 1 ≤ p) (hpk : p ≤ k) (hzero : ∀ i, 1 ≤ i → i < p → α i = 0) :
    (∃ C', ∀ m, |Richardson.step A δ p m - α 0| ≤ C' * (δ ^ m * h) ^ (p + 1)) ∧
      ∀ i, i ≠ p → (α i * (δ ^ i - δ ^ p) / (1 - δ ^ p) ≠ 0 ↔ α i ≠ 0) := by
  have hδp : δ ^ p < 1 := pow_lt_one₀ hδ0.le hδ1 (by omega)
  have hne : (1 - δ ^ p) ≠ 0 := by linarith
  refine ⟨?_, fun i hi => ?_⟩
  · have hstep := Richardson.hasExpansion_step hA hδ0 hδ1 hh hp
    have hzero' : ∀ i, 1 ≤ i → i ≤ p → α i * (δ ^ i - δ ^ p) / (1 - δ ^ p) = 0 := by
      intro i hi1 hip
      rcases lt_or_eq_of_le hip with hlt | rfl
      · rw [hzero i hi1 hlt, zero_mul, zero_div]
      · rw [sub_self, mul_zero, zero_div]
    refine ⟨((∑ i ∈ Finset.range (k + 1), |α i * (δ ^ i - δ ^ p) / (1 - δ ^ p)|)
      + |C * (δ ^ (k + 1) + δ ^ p) / (1 - δ ^ p)|) * (1 + h) ^ (k + 1), fun m => ?_⟩
    have := Richardson.abs_sub_le_of_hasExpansion hstep hδ0 hδ1.le hh hpk hzero' m
    rwa [pow_zero, mul_div_assoc, div_self hne, mul_one] at this
  · have hδi : δ ^ i - δ ^ p ≠ 0 :=
      sub_ne_zero.2 fun h => hi (pow_right_injective₀ hδ0 hδ1.ne h)
    rw [Ne, div_eq_zero_iff, mul_eq_zero, not_or, not_or]
    exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hδi⟩, hne⟩⟩

/-- **(9.34), the Richardson extrapolation table.** With `𝒜_{m,0} = 𝒜(δ^m h)` and
`𝒜_{m,q+1} = (𝒜_{m,q} - δ^{q+1} 𝒜_{m-1,q})/(1 - δ^{q+1})`, the entries are the backbone's
`Richardson.table A δ m q` (the book's ranges `m = 0, …, n`, `q = 0, …, n - 1`,
`m = q + 1, …, n` restrict the recursion to the triangle; entries with `m < q` are junk). -/
theorem equation_9_34 (A : ℕ → ℝ) (δ : ℝ) (m q : ℕ) :
    Richardson.table A δ m 0 = A m ∧
      Richardson.table A δ m (q + 1)
        = (Richardson.table A δ m q - δ ^ (q + 1) * Richardson.table A δ (m - 1) q)
          / (1 - δ ^ (q + 1)) :=
  ⟨rfl, rfl⟩

/-- **Property 9.2 (9.35).** For `δ ∈ (0, 1)` and `𝒜` with the expansion (9.33) to order `k`, the
entries of the table (9.34) satisfy `𝒜_{m,q} = α₀ + O((δ^m h)^{q+1})` for `0 ≤ q ≤ m` and
`q ≤ k`, with a constant independent of `m`: the first column converges at the rate `O(δ^m h)`
and the `q`-th `q` times faster. **Reading:** the book prints `𝒜_{m,n}` for `m = 0, …, n`, which
(9.34) does not define; this is [Com95], Proposition 4.1. The backbone's
`Richardson.exists_abs_table_sub_le`. -/
theorem property_9_2 {A : ℕ → ℝ} {δ h : ℝ} {α : ℕ → ℝ} {k : ℕ} {C : ℝ}
    (hA : equation_9_33 A δ h α k C) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) {q : ℕ}
    (hqk : q ≤ k) :
    ∃ C', ∀ m, q ≤ m → |Richardson.table A δ m q - α 0| ≤ C' * (δ ^ m * h) ^ (q + 1) :=
  Richardson.exists_abs_table_sub_le hA hδ0 hδ1 hh hqk

/-! ### Romberg integration -/

/-- **Property 9.3, the Euler–Maclaurin formula (9.36).** Let `f ∈ C^{2k+2}([a, b])`, `k ≥ 0`,
and approximate `α₀ = ∫_a^b f` by the composite trapezoidal rule (9.14) with `h_m = (b - a)/m`,
`m ≥ 1`. Then
`I_{1,m}(f) = α₀ + ∑_{i=1}^k B_{2i}/(2i)! h_m^{2i} (f^{(2i-1)}(b) - f^{(2i-1)}(a))
  + B_{2k+2}/(2k+2)! h_m^{2k+2} (b - a) f^{(2k+2)}(η)`
for some `η ∈ (a, b)`, where the `B_{2j}` are the Bernoulli numbers (Mathlib's `bernoulli`; see
`bernoulliNumber_eq` for the book's definition). The backbone's
`EulerMaclaurin.trapezoidSum_eq_integral_add_sum_add_mul`. -/
theorem property_9_3 (hab : a < b) {k : ℕ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * k + 2 : ℕ) : WithTop ℕ∞) f U) {m : ℕ} (hm : 1 ≤ m) :
    ∃ η ∈ Ioo a b, Quadrature.trapezoidSum f a ((b - a) / m) m
      = (∫ x in a..b, f x)
        + ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * ((b - a) / m) ^ (2 * i)
            * (iteratedDeriv (2 * i - 1) f b - iteratedDeriv (2 * i - 1) f a)
        + ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)! * ((b - a) / m) ^ (2 * k + 2) * (b - a)
            * iteratedDeriv (2 * k + 2) f η :=
  EulerMaclaurin.trapezoidSum_eq_integral_add_sum_add_mul hab hU hUab hf hm

/-- **Property 9.3, the Bernoulli numbers.** The book's definition
`B_{2j} = (-1)^{j-1} [∑_{n=1}^∞ 2/(2nπ)^{2j}] (2j)!`, `j ≥ 1`, agrees with Mathlib's
`bernoulli (2j)` used in `property_9_3` (the sum over `n ≥ 1` is written over `n + 1`, `n : ℕ`).
The backbone's `bernoulli_eq_tsum_two_div_pow`, from Mathlib's `hasSum_zeta_nat`. -/
theorem bernoulliNumber_eq {j : ℕ} (hj : 1 ≤ j) :
    ((bernoulli (2 * j) : ℚ) : ℝ)
      = (-1) ^ (j - 1) * (∑' n : ℕ, 2 / (2 * ((n : ℝ) + 1) * Real.pi) ^ (2 * j)) * (2 * j)! := by
  rw [bernoulli_eq_tsum_two_div_pow hj]
  ring

/-- **(9.37) and the Romberg algorithm.** Applying (9.34) to (9.36) with `h = h_m²` gives the
recursion `𝒜_{m,q+1} = (𝒜_{m,q} - δ^{2(q+1)} 𝒜_{m-1,q})/(1 - δ^{2(q+1)})`; with `h = b - a`,
`δ = 1/2` and `T(h_s) = I_{1,s}(f)` the composite trapezoidal rule over `s = 2^m` subintervals of
width `h_s = (b - a)/2^m`, the algorithm reads `𝒜_{m,0} = T((b - a)/2^m)` and
`𝒜_{m,q+1} = (4^{q+1} 𝒜_{m,q} - 𝒜_{m-1,q})/(4^{q+1} - 1)`. The three displays for the backbone's
`Romberg.table f a b`. -/
theorem equation_9_37 (f : ℝ → ℝ) (a b : ℝ) (m q : ℕ) :
    Romberg.table f a b m 0 = Quadrature.trapezoidSum f a ((b - a) / 2 ^ m) (2 ^ m) ∧
      Romberg.table f a b m (q + 1)
        = (Romberg.table f a b m q - (1 / 2) ^ (2 * (q + 1)) * Romberg.table f a b (m - 1) q)
          / (1 - (1 / 2) ^ (2 * (q + 1))) ∧
      Romberg.table f a b m (q + 1)
        = (4 ^ (q + 1) * Romberg.table f a b m q - Romberg.table f a b (m - 1) q)
          / (4 ^ (q + 1) - 1) := by
  refine ⟨rfl, ?_, Romberg.table_succ f a b m q⟩
  have e : ((1 : ℝ) / 2) ^ (2 * (q + 1)) = (1 / 4) ^ (q + 1) := by
    rw [pow_mul]; norm_num
  rw [e]
  rfl

/-- **§9.6.1, convergence of Romberg integration.** For `f ∈ C^{2n+2}([a, b])`,
`𝒜_{m,n} = ∫_a^b f + O(h_s^{2(n+1)})`, `h_s = (b - a)/2^m`: there is `C` with
`|𝒜_{m,n} - ∫_a^b f| ≤ C h_s^{2(n+1)}` for every `m ≥ n`. Property 9.2 applied to the
Euler–Maclaurin expansion of Property 9.3 in the parameter `h_m²`; the backbone's
`Romberg.exists_abs_table_sub_integral_le`. -/
theorem rombergConvergence (hab : a < b) {n : ℕ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ C, ∀ m, n ≤ m →
      |Romberg.table f a b m n - ∫ x in a..b, f x| ≤ C * ((b - a) / 2 ^ m) ^ (2 * (n + 1)) :=
  Romberg.exists_abs_table_sub_integral_le hab hU hUab hf

end QuarteroniSaccoSaleri.Chapter09
