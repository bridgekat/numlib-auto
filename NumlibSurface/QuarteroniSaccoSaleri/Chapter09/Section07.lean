/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section06

/-!
# Quarteroni, Sacco and Saleri, Section 9.7: Automatic integration

This module formalizes Section 9.7 of [quarteroni2000numerical]. An automatic integrator pairs each
approximation $\mathcal{I}_k$ of $\int_a^b f$ with an estimate $\mathcal{E}_k$ of its error. The
statements of the section are the a posteriori error estimators behind two strategies. The non
adaptive strategy (Section 9.7.1) doubles the number of panels of a composite Newton–Cotes formula
and extrapolates. By (9.39)–(9.40),
$$I(f) - I_{n,2m}(f) \simeq \frac{I_{n,2m}(f) - I_{n,m}(f)}{2^{n+p} - 1},$$
with $p = 2$ for even $n$ and $p = 1$ for odd $n$; for Simpson's formula the factor is $15$. The
adaptive strategy (Section 9.7.2) compares Simpson's formula $S_f(\alpha, \beta)$ on
$[\alpha, \beta]$ with the formula $S_{f,2}(\alpha, \beta)$ on the two halves. By (9.42)–(9.44),
$|I_f(\alpha, \beta) - S_{f,2}(\alpha, \beta)| \simeq |\mathcal{E}_f(\alpha, \beta)|/15$ with
$\mathcal{E}_f = S_f - S_{f,2}$, and the local tolerance (9.45), $|\mathcal{E}_f(\alpha, \beta)|/10
\le \varepsilon (\beta - \alpha)/(b - a)$, on each subinterval ensures the global tolerance.

The book writes (9.39)–(9.40) and (9.43)–(9.44) with $\simeq$, because the point where the
derivative is evaluated changes between the two formulae. Here they are stated as identities with an
explicit remainder. For (9.40) the remainder is of the next order in $H$; the proof uses the
Euler–Maclaurin expansion of Property 9.3 and the backbone's `Richardson.abs_sub_sub_estimate_le`.
For (9.44) the remainder is bounded by the oscillation of $f^{(4)}$
(`Quadrature.abs_sub_simpson_add_estimate_le`).

## Main definitions

* Section 9.7.1, `QuarteroniSaccoSaleri.Chapter09.eulerMaclaurinTerm`: the coefficient of $h^{2i}$
  in the Euler–Maclaurin expansion.
* Section 9.7.2, `QuarteroniSaccoSaleri.Chapter09.simpsonRule`: the Cavalieri–Simpson formula
  $S_f(\alpha, \beta)$ on $[\alpha, \beta]$.

## Main results

* Section 9.7.1, `QuarteroniSaccoSaleri.Chapter09.abs_trapezoidSum_sub_le`: the Euler–Maclaurin
  expansion as a bound with remainder $O(h_m^{2k+2})$.
* Equations (9.39)–(9.40), `QuarteroniSaccoSaleri.Chapter09.equation_9_40_trapezoid`: the doubling
  estimator with the factor $3$ for the trapezoidal formula, with remainder $O(H^4)$.
* Equations (9.39)–(9.40), `QuarteroniSaccoSaleri.Chapter09.equation_9_40_simpson`: the doubling
  estimator with the factor $15$ for Simpson's formula, with remainder $O(H^6)$.
* Section 9.7.2, `QuarteroniSaccoSaleri.Chapter09.simpsonRule_eq_simpsonSum`: $S_f$ and $S_{f,2}$
  are the composite Simpson formulae with one and two panels.
* Equation (9.42), `QuarteroniSaccoSaleri.Chapter09.equation_9_42`: the Simpson error on
  $[\alpha, \beta]$.
* Equations (9.43)–(9.44), `QuarteroniSaccoSaleri.Chapter09.equation_9_44`: the adaptive estimator,
  with the remainder $h_0^5 \omega / 1350$.
* Equation (9.45), `QuarteroniSaccoSaleri.Chapter09.equation_9_45`: local tolerances proportional to
  the lengths of the subintervals give the global tolerance.

## Conventions

* As in Sections 9.2 and 9.6, $f \in C^k([a, b])$ is `ContDiffOn ℝ k f U` on an open set
  $U \supseteq [a, b]$.
* The composite trapezoidal formula $T_m$ on $m$ panels is
  `Quadrature.trapezoidSum f a ((b - a) / m) m`, and the composite Simpson formula $S_m$ is
  `Quadrature.simpsonSum f a ((b - a) / m) m`.
* The one-panel Simpson value $S_f(\alpha, \beta)$ of Section 9.7.2 is
  `QuarteroniSaccoSaleri.Chapter09.simpsonRule f α β`.

## Deviations from the source

* **Equations (9.39)–(9.40)** (reading). The source writes an approximate equality $\simeq$ for
  every $n$. The library states it as a bound with a remainder of the next order in $H$, for the
  trapezoidal ($n = 1$) and Simpson ($n = 2$) formulae, the only composite Newton–Cotes formulae for
  which the book gives an asymptotic expansion. See
  `QuarteroniSaccoSaleri.Chapter09.equation_9_40_trapezoid` and
  `QuarteroniSaccoSaleri.Chapter09.equation_9_40_simpson`.
* **Equations (9.43)–(9.44)** (reading). The source writes an approximate equality $\simeq$. The
  library states it as a bound with a remainder controlled by the oscillation of $f^{(4)}$. See
  `QuarteroniSaccoSaleri.Chapter09.equation_9_44`.

## Not formalized

* **The stopping test (9.38).** It is part of an algorithm.
* **Program 77.** It is an algorithm.
* **The paragraph on Gauss–Kronrod formulae.** It is prose.
* **Examples 9.8 and 9.9.** They are numerical runs.
-/

open Set Filter Topology intervalIntegral
open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ}

/-! ### The Euler–Maclaurin expansion as a bound with two or three terms -/

/-- The Euler–Maclaurin coefficient
$$c_i = \frac{B_{2i}}{(2i)!} \bigl(f^{(2i-1)}(b) - f^{(2i-1)}(a)\bigr)$$
of the term $h^{2i}$ in the expansion of the composite trapezoidal formula (Property 9.3). -/
noncomputable def eulerMaclaurinTerm (f : ℝ → ℝ) (a b : ℝ) (i : ℕ) : ℝ :=
  ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * (iteratedDeriv (2 * i - 1) f b
    - iteratedDeriv (2 * i - 1) f a)

/-- Property 9.3 as a bound. Let $a < b$ and $f \in C^{2k+2}([a, b])$. Then there is a constant $C$
such that for every $m \ge 1$, with $h_m = (b - a)/m$,
$$\Bigl|T_m - \int_a^b f(x)\,dx - \sum_{i=1}^{k} c_i h_m^{2i}\Bigr| \le C h_m^{2k+2}.$$
-/
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

/-- **Equations (9.39)–(9.40)** of [quarteroni2000numerical], for the composite trapezoidal formula
($n = 1$, $p = 1$, $2^{n+p} - 1 = 3$). Let $a < b$ and $f \in C^4([a, b])$. Then there is a
constant $C$, depending only on $f$ and $[a, b]$, such that for every $m \ge 1$, with
$H = (b - a)/m$,
$$\Bigl|\bigl(I(f) - T_{2m}\bigr) - \frac{T_{2m} - T_m}{3}\Bigr| \le C H^4.$$

**Reading.** The source writes $I(f) - T_{2m} \simeq (T_{2m} - T_m)/3$. The statement here makes
the approximation precise with a remainder of order $H^4$.

The proof uses the Euler–Maclaurin expansion with two terms (Property 9.3 with $k = 1$) and the
backbone's `Richardson.abs_sub_sub_estimate_le` in the parameter $H^2$ with $\delta = 1/4$. -/
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

/-- **Equations (9.39)–(9.40)** of [quarteroni2000numerical], for the composite Simpson formula
($n = p = 2$, $2^{n+p} - 1 = 15$). Let $a < b$ and $f \in C^6([a, b])$. Then there is a constant
$C$ such that for every $m \ge 1$, with $H = (b - a)/m$,
$$\Bigl|\bigl(I(f) - S_{2m}\bigr) - \frac{S_{2m} - S_m}{15}\Bigr| \le C H^6.$$

**Reading.** The source writes that "(9.40) predicts a reduction of the absolute error by a
factor of $15$ when passing from $m$ to $2m$ subintervals", as an approximate equality. The
statement here makes it precise with a remainder of order $H^6$.

Simpson's formula is the first Romberg column, $S_N = (4 T_{2N} - T_N)/3$. It therefore inherits
from the Euler–Maclaurin expansion with three terms (Property 9.3 with $k = 2$) an expansion in
$H^2$ without the $H^2$ term. The proof then applies the backbone's
`Richardson.abs_sub_sub_estimate_le` with $p = 2$ and $q = 3$. -/
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

/-- **Section 9.7.2** of [quarteroni2000numerical], the Cavalieri–Simpson formula on
$[\alpha, \beta]$:
$$S_f(\alpha, \beta) = \frac{h_0}{3} [f(\alpha) + 4 f(\alpha + h_0) + f(\beta)], \qquad h_0 =
  \frac{\beta - \alpha}{2}.$$
-/
noncomputable def simpsonRule (f : ℝ → ℝ) (α β : ℝ) : ℝ :=
  (β - α) / 2 / 3 * (f α + 4 * f (α + (β - α) / 2) + f β)

/-- For every $f$ and all $\alpha, \beta$, the value $S_f(\alpha, \beta)$ is the composite Simpson
sum with one panel, and
$$S_{f,2}(\alpha, \beta) = S_f\Bigl(\alpha, \frac{\alpha + \beta}{2}\Bigr) +
  S_f\Bigl(\frac{\alpha + \beta}{2}, \beta\Bigr)$$
is the composite Simpson sum with two panels. -/
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

/-- **Equation (9.42)** of [quarteroni2000numerical]. Let $\alpha < \beta$ and
$f \in C^4([\alpha, \beta])$. Then
$$I_f(\alpha, \beta) - S_f(\alpha, \beta) = -\frac{h_0^5}{90} f^{(4)}(\xi), \qquad h_0 =
  \frac{\beta - \alpha}{2},$$
for some $\xi \in [\alpha, \beta]$, where $I_f(\alpha, \beta) = \int_\alpha^\beta f(x)\,dx$.

This is (9.16) on $[\alpha, \beta]$. -/
theorem equation_9_42 {α β : ℝ} (hαβ : α < β) (hU : IsOpen U) (hUab : Icc α β ⊆ U)
    (hf : ContDiffOn ℝ 4 f U) :
    ∃ ξ ∈ Icc α β, (∫ x in α..β, f x) - simpsonRule f α β
      = -((β - α) / 2) ^ 5 / 90 * iteratedDeriv 4 f ξ := by
  obtain ⟨ξ, hξ, h⟩ := equation_9_16 hαβ hU hUab hf
  refine ⟨ξ, hξ, ?_⟩
  rw [← h, simpsonRule, show α + (β - α) / 2 = (α + β) / 2 by ring]
  ring

/-- **Equations (9.43)–(9.44)** of [quarteroni2000numerical], the adaptive Simpson estimator. Let
$\alpha < \beta$, let $h_0 = (\beta - \alpha)/2$, let $f \in C^4([\alpha, \beta])$, and let
$|f^{(4)}(u) - f^{(4)}(v)| \le \omega$ for all $u, v \in [\alpha, \beta]$. Let
$\mathcal{E}_f(\alpha, \beta) = S_f(\alpha, \beta) - S_{f,2}(\alpha, \beta)$. Then
$$\Bigl|\bigl(I_f(\alpha, \beta) - S_{f,2}(\alpha, \beta)\bigr) + \frac{\mathcal{E}_f(\alpha,
  \beta)}{15}\Bigr| \le \frac{h_0^5}{1350} \omega.$$

**Reading.** The source writes $|I_f(\alpha, \beta) - S_{f,2}(\alpha, \beta)| \simeq
|\mathcal{E}_f(\alpha, \beta)|/15$. The statement here is that approximation with the variation
of $f^{(4)}$ made explicit. Note the sign: $I_f - S_{f,2} \approx -\mathcal{E}_f/15$.

The proof is the backbone's `Quadrature.abs_sub_simpson_add_estimate_le`. -/
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

/-- **Equation (9.45)** of [quarteroni2000numerical] and the sentence before it. Let $a < b$, let
$t_0, \dots, t_N$ be real numbers with $t_0 = a$ and $t_N = b$, and let $f$ be integrable on
each interval between $t_j$ and $t_{j+1}$. If for each $j < N$ the approximate integral $J_j$
satisfies
$$\Bigl|\int_{t_j}^{t_{j+1}} f(x)\,dx - J_j\Bigr| \le \varepsilon \frac{t_{j+1} - t_j}{b - a},$$
then
$$\Bigl|\int_a^b f(x)\,dx - \sum_{j=0}^{N-1} J_j\Bigr| \le \varepsilon.$$

So the local constraint on every subinterval ensures the global accuracy $\varepsilon$. The book
writes the local test (9.45) with the estimator, as $|\mathcal{E}_f(\alpha, \beta)|/10 \le
\varepsilon (\beta - \alpha)/(b - a)$; the statement here takes the resulting bound on the error
of each $J_j$ as its hypothesis. The points $t_j$ need not be increasing. The proof is the
triangle inequality together with $\sum_j (t_{j+1} - t_j) = b - a$. -/
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
