import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section06

/-!
# Quarteroni–Sacco–Saleri §9.7: automatic integration

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.7.

An automatic integrator pairs each approximation `𝓘_k` of `∫_a^b f` with an estimate `𝓔_k` of its
error; the section's statements are the a posteriori estimators behind the two strategies. The
non adaptive one (§9.7.1) doubles the number of panels of a composite Newton–Cotes formula and
extrapolates: (9.39)–(9.40), `I(f) - I_{n,2m}(f) ≃ (I_{n,2m}(f) - I_{n,m}(f))/(2^{n+p} - 1)`,
with `p = 2` for even and `p = 1` for odd `n` (a reduction by the factor `15` for Simpson's rule).
The adaptive one (§9.7.2) compares Simpson's rule on `[α, β]` with the rule on its two halves:
(9.42)–(9.44), `|I_f(α, β) - S_{f,2}(α, β)| ≃ |𝓔_f(α, β)|/15`, and the local tolerance (9.45),
`|𝓔_f(α, β)|/10 ≤ ε (β - α)/(b - a)`, ensures the global one. The stopping test (9.38), Program
77, the Gauss–Kronrod paragraph and Examples 9.8–9.9 are algorithms, prose or numerical runs and
are not formalized.

The book writes (9.39)–(9.40) and (9.43)–(9.44) with `≃`, the point where the derivative is
evaluated changing between the two rules. The nodes state them as identities with an explicit
remainder: of the next order in `H` for (9.40), through the Euler–Maclaurin expansion of Property
9.3 and the backbone's `Richardson.abs_sub_sub_estimate_le` — for the trapezoidal (`n = 1`) and
Simpson (`n = 2`) rules, the only composite Newton–Cotes rules whose asymptotic expansion the book
provides — and bounded by the oscillation of `f⁗` for (9.44)
(`Quadrature.abs_sub_simpson_add_estimate_le`).

## Main results

* `equation_9_40_trapezoid`, `equation_9_40_simpson` — the doubling estimators with the factors
  `3` and `15`, with remainders `O(H⁴)` and `O(H⁶)`.
* `equation_9_42`, `equation_9_44` — the Simpson panel error and the adaptive estimator, with the
  remainder `h₀⁵ ω(f⁗)/1350`.
* `equation_9_45` — local tolerances proportional to the panel lengths add up to the global one.

## Conventions

As in §9.2 and §9.6. `T_m` is `Quadrature.trapezoidSum f a ((b - a)/m) m` and `S_m` is
`Quadrature.simpsonSum f a ((b - a)/m) m`; the one-panel Simpson value `S_f(α, β)` of §9.7.2 is
`simpsonRule f α β`.
-/

open Set Filter Topology intervalIntegral
open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ}

/-! ### The Euler–Maclaurin expansion as a two- and three-term bound -/

/-- The Euler–Maclaurin coefficient `c_i = B_{2i}/(2i)! (f^{(2i-1)}(b) - f^{(2i-1)}(a))` of the
`h^{2i}` term in the expansion of the composite trapezoidal rule (Property 9.3). -/
noncomputable def eulerMaclaurinTerm (f : ℝ → ℝ) (a b : ℝ) (i : ℕ) : ℝ :=
  ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * (iteratedDeriv (2 * i - 1) f b
    - iteratedDeriv (2 * i - 1) f a)

/-- Property 9.3 as a bound: for `f ∈ C^{2k+2}([a, b])` there is `C` with
`|T_m - ∫_a^b f - ∑_{i=1}^k c_i h_m^{2i}| ≤ C h_m^{2k+2}` for every `m ≥ 1`. -/
theorem abs_trapezoidSum_sub_le (hab : a < b) {k : ℕ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * k + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ C, ∀ m : ℕ, 1 ≤ m →
      |Quadrature.trapezoidSum f a ((b - a) / m) m - (∫ x in a..b, f x)
        - ∑ i ∈ Finset.Icc 1 k, eulerMaclaurinTerm f a b i * ((b - a) / m) ^ (2 * i)|
        ≤ C * ((b - a) / m) ^ (2 * k + 2) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf)
  refine ⟨|((bernoulli (2 * k + 2) : ℚ) : ℝ)| / (2 * k + 2)! * (b - a) * M, fun m hm => ?_⟩
  obtain ⟨η, hη, h⟩ := property_9_3 hab hU hUab hf hm
  have hsum : ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)!
        * ((b - a) / m) ^ (2 * i)
        * (iteratedDeriv (2 * i - 1) f b - iteratedDeriv (2 * i - 1) f a)
      = ∑ i ∈ Finset.Icc 1 k, eulerMaclaurinTerm f a b i * ((b - a) / m) ^ (2 * i) :=
    Finset.sum_congr rfl fun i _ => by rw [eulerMaclaurinTerm]; ring
  rw [h, hsum]
  have hη' := hM η (Ioo_subset_Icc_self hη)
  rw [Real.norm_eq_abs] at hη'
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hη'
  have hh : (0 : ℝ) ≤ ((b - a) / m) ^ (2 * k + 2) := by
    have : (0 : ℝ) ≤ b - a := by linarith
    positivity
  rw [show (∫ x in a..b, f x) + ∑ i ∈ Finset.Icc 1 k, eulerMaclaurinTerm f a b i
        * ((b - a) / m) ^ (2 * i) + ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)!
        * ((b - a) / m) ^ (2 * k + 2) * (b - a) * iteratedDeriv (2 * k + 2) f η
      - (∫ x in a..b, f x) - ∑ i ∈ Finset.Icc 1 k, eulerMaclaurinTerm f a b i
        * ((b - a) / m) ^ (2 * i)
      = ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)! * (b - a) * iteratedDeriv (2 * k + 2) f η
        * ((b - a) / m) ^ (2 * k + 2) by ring]
  rw [abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 * k + 2)!),
    abs_of_pos (by linarith : (0 : ℝ) < b - a), abs_of_nonneg hh]
  gcongr

/-! ### The non adaptive estimator (9.40) -/

/-- **(9.39)–(9.40) for the composite trapezoidal rule** (`n = 1`, `p = 1`, `2^{n+p} - 1 = 3`).
For `f ∈ C⁴([a, b])` and `T_m` the composite trapezoidal rule on `m` panels,
`I(f) - T_{2m} ≃ (T_{2m} - T_m)/3`: precisely, there is `C` depending only on `f` and `[a, b]`
with `|(I(f) - T_{2m}) - (T_{2m} - T_m)/3| ≤ C H⁴`, `H = (b - a)/m`, for every `m ≥ 1`. The
two-term Euler–Maclaurin expansion (Property 9.3 with `k = 1`) and the backbone's
`Richardson.abs_sub_sub_estimate_le` in the parameter `H²`, `δ = 1/4`. -/
theorem equation_9_40_trapezoid (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 4 f U) :
    ∃ C, ∀ m : ℕ, 1 ≤ m →
      |((∫ x in a..b, f x) - Quadrature.trapezoidSum f a ((b - a) / (2 * m)) (2 * m))
        - (Quadrature.trapezoidSum f a ((b - a) / (2 * m)) (2 * m)
          - Quadrature.trapezoidSum f a ((b - a) / m) m) / 3| ≤ C * ((b - a) / m) ^ 4 := by
  have hf4 : ContDiffOn ℝ ((2 * 1 + 2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  obtain ⟨C, hC⟩ := abs_trapezoidSum_sub_le hab hU hUab hf4
  simp only [Finset.Icc_self, Finset.sum_singleton, mul_one] at hC
  set I := ∫ x in a..b, f x
  set c₁ := eulerMaclaurinTerm f a b 1
  refine ⟨C * ((1 / 4) ^ 2 + 1 / 4) / (1 - 1 / 4), fun m hm => ?_⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- the sampled sequence `T_{m 2^j}` in the parameter `(1/4)^j H²`
  have hA : ∀ j : ℕ, |Quadrature.trapezoidSum f a ((b - a) / (m * 2 ^ j)) (m * 2 ^ j) - I
      - c₁ * ((1 / 4) ^ j * ((b - a) / m) ^ 2) ^ 1|
      ≤ C * ((1 / 4) ^ j * ((b - a) / m) ^ 2) ^ 2 := by
    intro j
    have h := hC (m * 2 ^ j) (Nat.one_le_iff_ne_zero.2 (by positivity))
    push_cast at h
    have e : (1 / 4 : ℝ) ^ j * ((b - a) / m) ^ 2 = ((b - a) / (m * 2 ^ j)) ^ 2 := by
      have h4 : (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [div_pow, div_pow, one_pow, h4]
      field_simp
    rw [e, pow_one]
    refine h.trans (le_of_eq ?_)
    ring
  have h := Richardson.abs_sub_sub_estimate_le (δ := 1 / 4) (h := ((b - a) / m) ^ 2) (p := 1)
    (q := 2) (A := fun j => Quadrature.trapezoidSum f a ((b - a) / (m * 2 ^ j)) (m * 2 ^ j))
    (by norm_num) (by norm_num) one_pos hA 0
  simp only [zero_add, pow_one, pow_zero, one_mul, mul_one] at h
  rw [mul_comm m 2, mul_comm (m : ℝ) 2] at h
  have e13 : (1 / 4 : ℝ) / (1 - 1 / 4) = 1 / 3 := by norm_num
  rw [e13, one_div_mul_eq_div] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **(9.39)–(9.40) for the composite Simpson rule** (`n = p = 2`, `2^{n+p} - 1 = 15`): "(9.40)
predicts a reduction of the absolute error by a factor of `15` when passing from `m` to `2m`
subintervals". For `f ∈ C⁶([a, b])` and `S_m` the composite Simpson rule on `m` panels, there is
`C` with `|(I(f) - S_{2m}) - (S_{2m} - S_m)/15| ≤ C H⁶`, `H = (b - a)/m`, for every `m ≥ 1`.
Simpson's rule is the first Romberg column, `S_N = (4 T_{2N} - T_N)/3`, so it inherits from the
three-term Euler–Maclaurin expansion (Property 9.3 with `k = 2`) an expansion in `H²` whose `H²`
term is gone; then the backbone's `Richardson.abs_sub_sub_estimate_le` with `p = 2`, `q = 3`. -/
theorem equation_9_40_simpson (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 6 f U) :
    ∃ C, ∀ m : ℕ, 1 ≤ m →
      |((∫ x in a..b, f x) - Quadrature.simpsonSum f a ((b - a) / (2 * m)) (2 * m))
        - (Quadrature.simpsonSum f a ((b - a) / (2 * m)) (2 * m)
          - Quadrature.simpsonSum f a ((b - a) / m) m) / 15| ≤ C * ((b - a) / m) ^ 6 := by
  have hf6 : ContDiffOn ℝ ((2 * 2 + 2 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  obtain ⟨C, hC⟩ := abs_trapezoidSum_sub_le hab hU hUab hf6
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  simp only [hIcc, Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)),
    Finset.sum_singleton] at hC
  set c₁ := eulerMaclaurinTerm f a b 1
  set c₂ := eulerMaclaurinTerm f a b 2
  set I := ∫ x in a..b, f x
  -- Simpson on `N` panels: `|S_N - I + c₂/4 h_N⁴| ≤ 17C/48 h_N⁶`
  have hS : ∀ N : ℕ, 1 ≤ N →
      |Quadrature.simpsonSum f a ((b - a) / N) N - I - (-(c₂ / 4)) * (((b - a) / N) ^ 2) ^ 2|
        ≤ C * 17 / 48 * (((b - a) / N) ^ 2) ^ 3 := by
    intro N hN
    have h1 := hC N hN
    have h2 := hC (2 * N) (by omega)
    rw [Quadrature.simpsonSum_eq_trapezoidSum, show (b - a) / N / 2 = (b - a) / ((2 * N : ℕ) : ℝ) by
      push_cast; ring]
    have e2 : ((b - a) / ((2 * N : ℕ) : ℝ)) = (b - a) / N / 2 := by push_cast; ring
    rw [e2] at h2 ⊢
    set R₁ := Quadrature.trapezoidSum f a ((b - a) / N) N - I - (c₁ * ((b - a) / N) ^ (2 * 1)
      + c₂ * ((b - a) / N) ^ (2 * 2)) with hR₁
    set R₂ := Quadrature.trapezoidSum f a ((b - a) / N / 2) (2 * N) - I
      - (c₁ * ((b - a) / N / 2) ^ (2 * 1) + c₂ * ((b - a) / N / 2) ^ (2 * 2)) with hR₂
    have hcomb : (4 * Quadrature.trapezoidSum f a ((b - a) / N / 2) (2 * N)
        - Quadrature.trapezoidSum f a ((b - a) / N) N) / 3 - I
        - (-(c₂ / 4)) * (((b - a) / N) ^ 2) ^ 2 = (4 * R₂ - R₁) / 3 := by
      rw [hR₁, hR₂]; ring
    rw [hcomb, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_le_iff₀ (by norm_num)]
    have hR₂' : |R₂| ≤ C * ((b - a) / N) ^ (2 * 2 + 2) / 64 := by
      refine h2.trans (le_of_eq ?_)
      ring
    calc |4 * R₂ - R₁| ≤ |4 * R₂| + |R₁| := abs_sub _ _
      _ = 4 * |R₂| + |R₁| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      _ ≤ 4 * (C * ((b - a) / N) ^ (2 * 2 + 2) / 64) + C * ((b - a) / N) ^ (2 * 2 + 2) := by
        gcongr
      _ = C * 17 / 48 * (((b - a) / N) ^ 2) ^ 3 * 3 := by ring
  refine ⟨C * 17 / 48 * ((1 / 4) ^ 3 + (1 / 4) ^ 2) / (1 - (1 / 4) ^ 2), fun m hm => ?_⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hA : ∀ j : ℕ, |Quadrature.simpsonSum f a ((b - a) / (m * 2 ^ j)) (m * 2 ^ j) - I
      - (-(c₂ / 4)) * ((1 / 4) ^ j * ((b - a) / m) ^ 2) ^ 2|
      ≤ C * 17 / 48 * ((1 / 4) ^ j * ((b - a) / m) ^ 2) ^ 3 := by
    intro j
    have h := hS (m * 2 ^ j) (Nat.one_le_iff_ne_zero.2 (by positivity))
    push_cast at h
    have e : (1 / 4 : ℝ) ^ j * ((b - a) / m) ^ 2 = ((b - a) / (m * 2 ^ j)) ^ 2 := by
      have h4 : (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [div_pow, div_pow, one_pow, h4]
      field_simp
    rw [e]
    exact h
  have h := Richardson.abs_sub_sub_estimate_le (δ := 1 / 4) (h := ((b - a) / m) ^ 2) (p := 2)
    (q := 3) (A := fun j => Quadrature.simpsonSum f a ((b - a) / (m * 2 ^ j)) (m * 2 ^ j))
    (by norm_num) (by norm_num) two_pos hA 0
  simp only [zero_add, pow_one, pow_zero, one_mul, mul_one] at h
  rw [mul_comm m 2, mul_comm (m : ℝ) 2] at h
  have e115 : ((1 / 4 : ℝ) ^ 2) / (1 - (1 / 4) ^ 2) = 1 / 15 := by norm_num
  rw [e115, one_div_mul_eq_div] at h
  refine h.trans (le_of_eq ?_)
  ring

/-! ### The adaptive estimator (9.42)–(9.44) -/

/-- **`S_f(α, β)`**, the Cavalieri–Simpson formula on `[α, β]` written as in §9.7.2:
`(h₀/3)[f(α) + 4f(α + h₀) + f(β)]`, `h₀ = (β - α)/2`. -/
noncomputable def simpsonRule (f : ℝ → ℝ) (α β : ℝ) : ℝ :=
  (β - α) / 2 / 3 * (f α + 4 * f (α + (β - α) / 2) + f β)

/-- `S_f(α, β)` is the composite Simpson sum with one panel, and
`S_{f,2}(α, β) = S_f(α, (α + β)/2) + S_f((α + β)/2, β)` the one with two panels. -/
theorem simpsonRule_eq_simpsonSum (f : ℝ → ℝ) (α β : ℝ) :
    simpsonRule f α β = Quadrature.simpsonSum f α (β - α) 1 ∧
      simpsonRule f α ((α + β) / 2) + simpsonRule f ((α + β) / 2) β
        = Quadrature.simpsonSum f α ((β - α) / 2) 2 := by
  constructor
  · simp only [simpsonRule, Quadrature.simpsonSum, Finset.sum_range_one, Nat.cast_zero, zero_mul,
      add_zero, zero_add, one_mul]
    ring_nf
  · simp only [simpsonRule, Quadrature.simpsonSum, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.cast_zero, Nat.cast_one, zero_mul, add_zero, zero_add, one_mul]
    ring_nf

/-- **(9.42).** For `f ∈ C⁴([α, β])`, `I_f(α, β) - S_f(α, β) = -h₀⁵/90 f⁗(ξ)`, `h₀ = (β - α)/2`,
for some `ξ ∈ [α, β]`: (9.16) on `[α, β]`. -/
theorem equation_9_42 {α β : ℝ} (hαβ : α < β) (hU : IsOpen U) (hUab : Icc α β ⊆ U)
    (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc α β, (∫ x in α..β, f x) - simpsonRule f α β
      = -((β - α) / 2) ^ 5 / 90 * iteratedDeriv 4 f ξ := by
  obtain ⟨ξ, hξ, h⟩ := equation_9_16 hαβ hU hUab hf
  refine ⟨ξ, hξ, ?_⟩
  rw [← h, simpsonRule, show α + (β - α) / 2 = (α + β) / 2 by ring]
  ring

/-- **(9.43)–(9.44), the adaptive Simpson estimator.** On `[α, β] ⊆ [a, b]` with
`h₀ = (β - α)/2`, let `S_f(α, β)` be Simpson's rule, `S_{f,2}(α, β)` the same rule on the two
halves `[α, (α + β)/2]`, `[(α + β)/2, β]`, and `𝓔_f(α, β) = S_f(α, β) - S_{f,2}(α, β)`. For
`f ∈ C⁴([α, β])` with `|f⁗(u) - f⁗(v)| ≤ ω` on `[α, β]`,
`|(I_f(α, β) - S_{f,2}(α, β)) + 𝓔_f(α, β)/15| ≤ h₀⁵ ω/1350`: the book's
`|I_f(α, β) - S_{f,2}(α, β)| ≃ |𝓔_f(α, β)|/15` is this with the variation of `f⁗` neglected (note
the sign, `I_f - S_{f,2} ≈ -𝓔_f/15`). The backbone's
`Quadrature.abs_sub_simpson_add_estimate_le`. -/
theorem equation_9_44 {α β : ℝ} (hαβ : α < β) (hU : IsOpen U) (hUab : Icc α β ⊆ U)
    (hf : ContDiffOn ℝ 4 f U) {ω : ℝ}
    (hω : ∀ u ∈ Icc α β, ∀ v ∈ Icc α β, |iteratedDeriv 4 f u - iteratedDeriv 4 f v| ≤ ω) :
    |((∫ x in α..β, f x) - (simpsonRule f α ((α + β) / 2) + simpsonRule f ((α + β) / 2) β))
        + (simpsonRule f α β
          - (simpsonRule f α ((α + β) / 2) + simpsonRule f ((α + β) / 2) β)) / 15|
      ≤ ((β - α) / 2) ^ 5 / 1350 * ω := by
  have hf4 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) f U := by exact_mod_cast hf
  rw [(simpsonRule_eq_simpsonSum f α β).1, (simpsonRule_eq_simpsonSum f α β).2]
  exact Quadrature.abs_sub_simpson_add_estimate_le hαβ (hasDerivAt_of_contDiffOn hU hUab hf4
    four_pos) (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (hasDerivAt_iteratedDeriv_of_contDiffOn hU hUab hf4 (by norm_num))
    (continuousOn_iteratedDeriv_of_contDiffOn hU hUab hf4) hω

/-- **(9.45) and the sentence before it.** If `[a, b]` is partitioned into the subintervals
`[t_j, t_{j+1}]`, `j < N`, `t₀ = a`, `t_N = b`, and on each the approximate integral `J_j`
satisfies `|I_f(t_j, t_{j+1}) - J_j| ≤ ε (t_{j+1} - t_j)/(b - a)`, then
`|∫_a^b f - ∑_j J_j| ≤ ε`: enforcing the local constraint (9.45) on every subinterval ensures the
global accuracy `ε`. The triangle inequality and `∑_j (t_{j+1} - t_j) = b - a`. -/
theorem equation_9_45 (hab : a < b) {N : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = a) (htN : t N = b)
    (hf : ∀ j < N, IntervalIntegrable f MeasureTheory.volume (t j) (t (j + 1))) {J : ℕ → ℝ}
    {ε : ℝ} (hJ : ∀ j < N, |(∫ x in t j..t (j + 1), f x) - J j| ≤ ε * (t (j + 1) - t j) / (b - a)) :
    |(∫ x in a..b, f x) - ∑ j ∈ Finset.range N, J j| ≤ ε := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hf
  rw [ht0, htN] at hsum
  rw [← hsum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Finset.range N, |(∫ x in t j..t (j + 1), f x) - J j|
      ≤ ∑ j ∈ Finset.range N, ε * (t (j + 1) - t j) / (b - a) :=
        Finset.sum_le_sum fun j hj => hJ j (Finset.mem_range.1 hj)
    _ = ε * (t N - t 0) / (b - a) := by
        rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_range_sub]
    _ = ε := by rw [ht0, htN, mul_div_assoc, div_self (sub_ne_zero.2 hab.ne'), mul_one]

end QuarteroniSaccoSaleri.Chapter09
