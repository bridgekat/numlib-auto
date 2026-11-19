/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Extrapolation
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 9.6: Richardson extrapolation and Romberg integration

This module formalizes Section 9.6 of [quarteroni2000numerical]. A quantity $\mathcal{A}(h)$ with
the expansion (9.33)
$$\mathcal{A}(h) = \alpha_0 + \alpha_1 h + \dots + \alpha_k h^k + \mathcal{R}_{k+1}(h), \qquad
  |\mathcal{R}_{k+1}(h)| \le C_{k+1} h^{k+1},$$
is evaluated at $h$ and at $\delta h$, and the two values are combined to remove the leading error
term. If $\mathcal{A}$ approximates $\alpha_0$ to order $p$, then $\mathcal{B}(h) =
(\mathcal{A}(\delta h) - \delta^p \mathcal{A}(h))/(1 - \delta^p)$ approximates $\alpha_0$ to order
$p + 1$. Iteration gives the extrapolation table (9.34), and Property 9.2 states
$\mathcal{A}_{m,q} = \alpha_0 + O((\delta^m h)^{q+1})$. Romberg integration (Section 9.6.1) is the
table built on the composite trapezoidal formula with $2^m$ panels. Its expansion in $h_m^2$ is the
Euler–Maclaurin formula (Property 9.3), the recursion becomes (9.37), which for $\delta = 1/2$ is
the recursion with the factors $4^{q+1}$, and the entries converge at the order $h_s^{2(n+1)}$.

The backbone is `Numlib.Approximation.Extrapolation` (`Richardson.HasExpansion`, `Richardson.step`,
`Richardson.table`, `Romberg.table` and their theorems) together with
`Numlib.Analysis.SpecialFunctions.EulerMaclaurin`. All statements are about the sampled sequence
$A_m = \mathcal{A}(\delta^m h)$, which is what the algorithm (9.34) uses.

## Main definitions

* Equation (9.33), `QuarteroniSaccoSaleri.Chapter09.equation_9_33`: the expansion of the sampled
  sequence to order $k$.

## Main results

* Equation (9.33), `QuarteroniSaccoSaleri.Chapter09.equation_9_33_iff`: the expansion written out.
* Section 9.6, `QuarteroniSaccoSaleri.Chapter09.richardsonStep`: one extrapolation step raises the
  order from $p$ to $p + 1$, and $\tilde\alpha_i \neq 0$ if and only if $\alpha_i \neq 0$.
* Equation (9.34), `QuarteroniSaccoSaleri.Chapter09.equation_9_34`: the recursion of the
  extrapolation table.
* Property 9.2, `QuarteroniSaccoSaleri.Chapter09.property_9_2`: $\mathcal{A}_{m,q} = \alpha_0 +
  O((\delta^m h)^{q+1})$ for $q \le m$.
* Property 9.3, `QuarteroniSaccoSaleri.Chapter09.property_9_3`: the Euler–Maclaurin formula (9.36).
* Property 9.3, `QuarteroniSaccoSaleri.Chapter09.bernoulliNumber_eq`: the Bernoulli numbers of
  Mathlib agree with the zeta-series definition of the book.
* Equation (9.37), `QuarteroniSaccoSaleri.Chapter09.equation_9_37`: the Romberg recursion in its two
  forms.
* Section 9.6.1, `QuarteroniSaccoSaleri.Chapter09.rombergConvergence`: $\mathcal{A}_{m,n} = \int_a^b
  f + O(h_s^{2(n+1)})$.

## Conventions

* The value $\mathcal{A}(\delta^m h)$ is `A m` for a sequence `A : ℕ → ℝ`.
* As in Section 9.2, $f \in C^k([a, b])$ is `ContDiffOn ℝ k f U` on an open set
  $U \supseteq [a, b]$.
* The Bernoulli number $B_j$ is Mathlib's `bernoulli j : ℚ`, cast to `ℝ`.

## Deviations from the source

* **(9.33), (9.34) and (9.37)** (representation).
  `QuarteroniSaccoSaleri.Chapter09.equation_9_33` describes samples at $\delta^m h$. The table
  recurrences are total in their indices, while the source computes only the triangular part.
  `QuarteroniSaccoSaleri.Chapter09.equation_9_37` specializes $\delta=1/2$.
* **Property 9.3 and Romberg convergence** (reading). Smoothness is expressed on an open
  neighbourhood. `QuarteroniSaccoSaleri.Chapter09.rombergConvergence` gives an explicit uniform
  error bound in the valid part of the table.
* **Property 9.2** (reading). The source prints $\mathcal{A}_{m,n} = \alpha_0 + O((\delta^m
  h)^{n+1})$ for $m = 0, \dots, n$, but (9.34) defines $\mathcal{A}_{m,q}$ only for $m \ge q$. The
  library states $\mathcal{A}_{m,q} = \alpha_0 + O((\delta^m h)^{q+1})$ for $q \le m$. See
  `QuarteroniSaccoSaleri.Chapter09.property_9_2`.

## Not formalized

* **Examples 9.6 and 9.7.** They are numerical tables.
-/

open Set Filter Topology intervalIntegral
open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ}

/-! ### Richardson extrapolation -/

/-- **Equation (9.33)** of [quarteroni2000numerical], sampled at $h, \delta h, \delta^2 h, \dots$. A
sequence $A$, a ratio $\delta$, a step $h$, coefficients $\alpha_0, \alpha_1, \dots$, an order
$k$ and a constant $C$ satisfy the **expansion (9.33)** if for every $m$
$$A_m = \alpha_0 + \alpha_1 (\delta^m h) + \dots + \alpha_k (\delta^m h)^k +
  \mathcal{R}_{k+1}(\delta^m h), \qquad |\mathcal{R}_{k+1}(\delta^m h)| \le C (\delta^m
  h)^{k+1}.$$

The sequence is $A_m = \mathcal{A}(\delta^m h)$. The definition is the backbone's
`Richardson.HasExpansion A δ h α k C`.

**Reading.** Models sequence of samples at δ^m h rather than an arbitrary function of step size.
-/
def equation_9_33 (A : ℕ → ℝ) (δ h : ℝ) (α : ℕ → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  Richardson.HasExpansion A δ h α k C

/-- **Equation (9.33)** of [quarteroni2000numerical], written out. The expansion holds if and only
if for every $m$
$$\Bigl|A_m - \sum_{i=0}^{k} \alpha_i (\delta^m h)^i\Bigr| \le C (\delta^m h)^{k+1}.$$

**Reading.** Expands sampled error property as a uniform absolute inequality.
-/
theorem equation_9_33_iff (A : ℕ → ℝ) (δ h : ℝ) (α : ℕ → ℝ) (k : ℕ) (C : ℝ) :
    equation_9_33 A δ h α k C ↔
      ∀ m, |A m - ∑ i ∈ Finset.range (k + 1), α i * (δ ^ m * h) ^ i| ≤ C * (δ ^ m * h) ^ (k + 1) :=
  Iff.rfl

/-- **Section 9.6** of [quarteroni2000numerical], the effect of one extrapolation step. Let
$0 < \delta < 1$ and $h > 0$, let $A$ have the expansion (9.33) to order $k$ with the constant
$C$, let $1 \le p \le k$, and let $\alpha_i = 0$ for $1 \le i < p$, so that $\mathcal{A}$ is an
approximation of $\alpha_0$ of order $p$. Let
$$\mathcal{B}(\delta^m h) = \frac{A_{m+1} - \delta^p A_m}{1 - \delta^p}.$$
Then there is a constant $C'$ with $|\mathcal{B}(\delta^m h) - \alpha_0| \le C' (\delta^m
h)^{p+1}$ for every $m$. Moreover, for every $i \neq p$ the new coefficient $\tilde\alpha_i =
\alpha_i (\delta^i - \delta^p)/(1 - \delta^p)$ is nonzero if and only if $\alpha_i \neq 0$.

The value $\mathcal{B}(\delta^m h)$ is `Richardson.step A δ p m`. The case $p = 1$ is the first
display of the book, $\mathcal{B}(h) = \alpha_0 + \tilde\alpha_2 h^2 + \cdots$. The proof uses
the backbone's `Richardson.hasExpansion_step`, whose expansion has
$\tilde\alpha_1 = \dots = \tilde\alpha_p = 0$, and `Richardson.abs_sub_le_of_hasExpansion`.

**Reading.** Uses fixed sampled mesh, explicit missing low powers and remainder bound, and proves
preservation of coefficient nonvanishing away from eliminated power.
-/
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

/-- **Equation (9.34)** of [quarteroni2000numerical], the Richardson extrapolation table. For every
sequence $A$, every $\delta$ and all $m, q$, the entries $\mathcal{A}_{m,q}$ of the backbone's
`Richardson.table A δ m q` satisfy
$$\mathcal{A}_{m,0} = A_m, \qquad \mathcal{A}_{m,q+1} = \frac{\mathcal{A}_{m,q} - \delta^{q+1}
  \mathcal{A}_{m-1,q}}{1 - \delta^{q+1}}.$$

The book restricts the recursion to the triangle $m = q + 1, \dots, n$ and
$q = 0, \dots, n - 1$. The entries with $m < q$ have no meaning. The index $m - 1$ is truncated
subtraction on $\mathbb{N}$, so it is $0$ at $m = 0$.

**Generalization.** Extends table recurrence to arbitrary natural indices and real δ, with
saturating predecessor and total division.
-/
theorem equation_9_34 (A : ℕ → ℝ) (δ : ℝ) (m q : ℕ) :
    Richardson.table A δ m 0 = A m ∧
      Richardson.table A δ m (q + 1)
        = (Richardson.table A δ m q - δ ^ (q + 1) * Richardson.table A δ (m - 1) q)
          / (1 - δ ^ (q + 1)) :=
  ⟨rfl, rfl⟩

/-- **Property 9.2** of [quarteroni2000numerical], equation (9.35). Let $0 < \delta < 1$ and
$h > 0$, let $A$ have the expansion (9.33) to order $k$, and let $q \le k$. Then there is a
constant $C'$, independent of $m$, such that
$$|\mathcal{A}_{m,q} - \alpha_0| \le C' (\delta^m h)^{q+1} \qquad \text{for every } m \ge q.$$
So the first column converges at the rate $O(\delta^m h)$, and column $q$ converges $q$ times
faster.

**Reading.** The source prints $\mathcal{A}_{m,n} = \alpha_0 + O((\delta^m h)^{n+1})$ for
$m = 0, \dots, n$, but (9.34) does not define these entries for $m < n$. The statement here is
the one of Proposition 4.1 in the book of Comincioli (1995) that the source cites.

The proof is the backbone's `Richardson.exists_abs_table_sub_le`. -/
theorem property_9_2 {A : ℕ → ℝ} {δ h : ℝ} {α : ℕ → ℝ} {k : ℕ} {C : ℝ}
    (hA : equation_9_33 A δ h α k C) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) {q : ℕ}
    (hqk : q ≤ k) :
    ∃ C', ∀ m, q ≤ m → |Richardson.table A δ m q - α 0| ≤ C' * (δ ^ m * h) ^ (q + 1) :=
  Richardson.exists_abs_table_sub_le hA hδ0 hδ1 hh hqk

/-! ### Romberg integration -/

/-- **Property 9.3** of [quarteroni2000numerical], the Euler–Maclaurin formula (9.36). Let $a < b$,
let $k \ge 0$, let $f \in C^{2k+2}([a, b])$, let $m \ge 1$, and let $I_{1,m}(f)$ be the
composite trapezoidal formula (9.14) with $h_m = (b - a)/m$. Then there is $\eta \in (a, b)$
such that
$$I_{1,m}(f) = \int_a^b f(x)\,dx + \sum_{i=1}^{k} \frac{B_{2i}}{(2i)!} h_m^{2i}
  \bigl(f^{(2i-1)}(b) - f^{(2i-1)}(a)\bigr) + \frac{B_{2k+2}}{(2k+2)!} h_m^{2k+2} (b - a)
  f^{(2k+2)}(\eta),$$
where $B_{2j}$ are the Bernoulli numbers.

The Bernoulli numbers are Mathlib's `bernoulli`;
`QuarteroniSaccoSaleri.Chapter09.bernoulliNumber_eq` gives the definition of the book. The proof
is the backbone's `EulerMaclaurin.trapezoidSum_eq_integral_add_sum_add_mul`.

**Reading.** Exact Euler–Maclaurin coefficients and interior witness with open-neighborhood
regularity hypothesis.
-/
theorem property_9_3 (hab : a < b) {k : ℕ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * k + 2 : ℕ) : WithTop ℕ∞) f U) {m : ℕ} (hm : 1 ≤ m) :
    ∃ η ∈ Ioo a b, Quadrature.trapezoidSum f a ((b - a) / m) m
      = (∫ x in a..b, f x)
        + ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * ((b - a) / m) ^ (2 * i)
            * (iteratedDeriv (2 * i - 1) f b - iteratedDeriv (2 * i - 1) f a)
        + ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)! * ((b - a) / m) ^ (2 * k + 2) * (b - a)
            * iteratedDeriv (2 * k + 2) f η :=
  EulerMaclaurin.trapezoidSum_eq_integral_add_sum_add_mul hab hU hUab hf hm

/-- **Property 9.3** of [quarteroni2000numerical], the Bernoulli numbers. For every $j \ge 1$,
$$B_{2j} = (-1)^{j-1} \Bigl[\sum_{n=1}^{\infty} \frac{2}{(2n\pi)^{2j}}\Bigr] (2j)!,$$
which is the definition of the book, where $B_{2j}$ is Mathlib's `bernoulli (2 * j)`.

The sum over $n \ge 1$ is written as a sum over $n + 1$ with $n \in \mathbb{N}$. The proof is
the backbone's `bernoulli_eq_tsum_two_div_pow`, from Mathlib's `hasSum_zeta_nat`. -/
theorem bernoulliNumber_eq {j : ℕ} (hj : 1 ≤ j) :
    ((bernoulli (2 * j) : ℚ) : ℝ)
      = (-1) ^ (j - 1) * (∑' n : ℕ, 2 / (2 * ((n : ℝ) + 1) * Real.pi) ^ (2 * j)) * (2 * j)! := by
  rw [bernoulli_eq_tsum_two_div_pow hj]
  ring

/-- **Equation (9.37)** of [quarteroni2000numerical] and the Romberg algorithm. Let
$f : \mathbb{R} \to \mathbb{R}$, let $a, b \in \mathbb{R}$, and let $T(h_s) = I_{1,s}(f)$ be the
composite trapezoidal formula on $s = 2^m$ subintervals of width $h_s = (b - a)/2^m$. The
entries $\mathcal{A}_{m,q}$ of the Romberg table `Romberg.table f a b` satisfy
$\mathcal{A}_{m,0} = T((b - a)/2^m)$,
$$\mathcal{A}_{m,q+1} = \frac{\mathcal{A}_{m,q} - (1/2)^{2(q+1)} \mathcal{A}_{m-1,q}}{1 -
  (1/2)^{2(q+1)}} \qquad \text{and} \qquad \mathcal{A}_{m,q+1} = \frac{4^{q+1}
  \mathcal{A}_{m,q} - \mathcal{A}_{m-1,q}}{4^{q+1} - 1}.$$

The first recursion is (9.34) applied to the expansion (9.36) in the parameter $h_m^2$, with
$h = b - a$ and $\delta = 1/2$. The second is the form of the Romberg algorithm.

**Reading.** Specializes δ=1/2 and totalizes recurrence outside the triangular table.
-/
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

/-- **Section 9.6.1** of [quarteroni2000numerical], convergence of Romberg integration. Let $a < b$
and $f \in C^{2n+2}([a, b])$. Then there is a constant $C$ such that
$$\Bigl|\mathcal{A}_{m,n} - \int_a^b f(x)\,dx\Bigr| \le C h_s^{2(n+1)}, \qquad h_s = \frac{b -
  a}{2^m},$$
for every $m \ge n$.

The proof applies Property 9.2 to the Euler–Maclaurin expansion of Property 9.3 in the parameter
$h_m^2$. It is the backbone's `Romberg.exists_abs_table_sub_integral_le`.

**Reading.** Explicit remainder bound with open-neighborhood regularity and valid m≥n to justify
stated rate.
-/
theorem rombergConvergence (hab : a < b) {n : ℕ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ C, ∀ m, n ≤ m →
      |Romberg.table f a b m n - ∫ x in a..b, f x| ≤ C * ((b - a) / 2 ^ m) ^ (2 * (n + 1)) :=
  Romberg.exists_abs_table_sub_integral_le hab hU hUab hf

end QuarteroniSaccoSaleri.Chapter09
