/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 9.4: Composite Newton–Cotes formulae

This module formalizes Section 9.4 of [quarteroni2000numerical]. The interval $[a, b]$ is divided
into $m$ subintervals $T_j = [y_j, y_{j+1}]$ with $y_j = a + jH$ and $H = (b - a)/m$, and the closed
Newton–Cotes formula with $n + 1$ equally spaced nodes is used on each subinterval. The composite
formula (9.25) is $I_{n,m}(f) = \sum_j \sum_k \alpha_k^{(j)} f(x_k^{(j)})$ with
$\alpha_k^{(j)} = h w_k$ and $h = H/n$. Theorem 9.3 gives the error (9.26) for even $n$, and the
remark after it states the convergence $E_{n,m}(f) \to 0$ as $m \to \infty$. Property 9.1 gives the
convergence for a merely continuous integrand when the weights are nonnegative, with the bound
$2(b - a)\,\Omega(f; H)$ in terms of the modulus of continuity.

The backbone is `Numlib.Approximation.NewtonCotes`. It supplies the composite rule
`Quadrature.compositeNewtonCotes`, Theorem 9.3 with the corrected constant
(`Quadrature.exists_sub_compositeNewtonCotes_eq_of_even`), Property 9.1
(`Quadrature.tendsto_compositeNewtonCotes` and `Quadrature.abs_sub_compositeNewtonCotes_le`), and
the convergence for a smooth integrand without a sign hypothesis on the weights
(`Quadrature.tendsto_compositeNewtonCotes_of_contDiffOn`).

## Main definitions

* Property 9.1, `QuarteroniSaccoSaleri.Chapter09.modulusOfContinuity`: the modulus of continuity
  $\Omega(f; H)$ of $f$ on $[a, b]$.

## Main results

* Equation (9.25), `QuarteroniSaccoSaleri.Chapter09.equation_9_25`: the composite formula is the
  double sum of the book.
* Theorem 9.3, `QuarteroniSaccoSaleri.Chapter09.theorem_9_3_even`: the composite error (9.26) for
  even $n$, with the corrected constant.
* Theorem 9.3, `QuarteroniSaccoSaleri.Chapter09.theorem_9_3_tendsto_even`: for even $n$,
  $E_{n,m}(f) \to 0$ as $m \to \infty$.
* Theorem 9.3, `QuarteroniSaccoSaleri.Chapter09.theorem_9_3_tendsto_odd`: for odd $n$,
  $E_{n,m}(f) \to 0$ as $m \to \infty$.
* Property 9.1, `QuarteroniSaccoSaleri.Chapter09.property_9_1`: convergence for $f \in C^0([a, b])$
  when the closed weights are nonnegative.
* Property 9.1, `QuarteroniSaccoSaleri.Chapter09.property_9_1_midpoint`: convergence of the
  composite midpoint formula for $f \in C^0([a, b])$.
* Property 9.1, `QuarteroniSaccoSaleri.Chapter09.abs_sub_le_modulusOfContinuity`: the modulus of
  continuity bounds the change of $f$ over a distance at most $H$.
* Property 9.1, `QuarteroniSaccoSaleri.Chapter09.property_9_1_bound`: the error bound
  $2(b - a)\,\Omega(f; H)$.

## Conventions

* As in Section 9.2, $f \in C^k([a, b])$ is `ContDiffOn ℝ k f U` on an open set
  $U \supseteq [a, b]$, and $f^{(k)}$ is `iteratedDeriv k f`.
* The modulus of continuity $\Omega(f; H)$ is `QuarteroniSaccoSaleri.Chapter09.modulusOfContinuity f
  a b H`, the supremum of $|f(x) - f(y)|$ over $x \neq y$ in $[a, b]$ with $|x - y| \le H$, as the
  book defines it.

## Deviations from the source

* **Theorem 9.3, equation (9.26)** (correction). The source prints the constant $M_n/(n + 2)^{n+3}$.
  The correct constant is $M_n/n^{n+3}$. See `QuarteroniSaccoSaleri.Chapter09.theorem_9_3_even`.

## Not formalized

* **Theorem 9.3 for odd $n$, equation (9.27).** It is the sum over the panels of the error formula
  (9.20) for odd $n$, which is not formalized (see Section 9.3). The convergence remark for odd $n$
  does not need it and is formalized.
* **Example 9.4.** It is a numerical table.
-/

open Set Filter Topology intervalIntegral

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ}

/-! ### The composite formula (9.25) -/

/-- **Equation (9.25)** of [quarteroni2000numerical], the composite closed Newton–Cotes formula. For
all $n, m \in \mathbb{N}$, all $a, b$ and every $f$, let $H = (b - a)/m$, $h = H/n$,
$y_j = a + jH$ and $x_k^{(j)} = y_j + kh$. Then the composite formula on the $m$ subintervals
$T_j = [y_j, y_{j+1}]$ is
$$I_{n,m}(f) = \sum_{j=0}^{m-1} \sum_{k=0}^{n} \alpha_k^{(j)} f(x_k^{(j)}), \qquad
  \alpha_k^{(j)} = h w_k,$$
where the weights $\alpha_k^{(j)}$ do not depend on $T_j$.

The composite formula is `Quadrature.compositeNewtonCotes n f a b m`, and $w_k$ is
`Quadrature.newtonCotesWeight n k`. In Lean, division by zero gives zero, so the identity also
holds for $m = 0$ or $n = 0$. -/
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

/-- **Theorem 9.3** of [quarteroni2000numerical], even $n$, equation (9.26). Let $n \ge 2$ be even,
let $a < b$, let $m \ge 1$, let $H = (b - a)/m$, and let $f \in C^{n+2}([a, b])$. Then the error
of the composite closed Newton–Cotes formula is
$$E_{n,m}(f) = \int_a^b f(x)\,dx - I_{n,m}(f) = \frac{b - a}{(n + 2)!} \frac{M_n}{n^{n+3}}
  H^{n+2} f^{(n+2)}(\xi)$$
for some $\xi \in [a, b]$, where $M_n$ is the constant of Theorem 9.2.

**Correction.** The source prints $M_n/(n + 2)^{n+3}$ in place of $M_n/n^{n+3}$. The panel
spacing of the closed formula is $h = H/n$, and with $n^{n+3}$ the case $n = 2$ gives the
composite Simpson error $-(b - a)H^4/2880$ of Section 9.2.3
(`QuarteroniSaccoSaleri.Chapter09.compositeSimpsonError`).

The book concludes that the error is an infinitesimal of order $n + 2$ in $H$ and that the
degree of exactness is $n + 1$. The constant $M_n$ is `Quadrature.newtonCotesM n`. The proof is
the backbone's `Quadrature.exists_sub_compositeNewtonCotes_eq_of_even`: (9.19) on each
subinterval, and Theorem 9.1 with $u = f^{(n+2)}$ and $\delta_j = 1$. -/
theorem theorem_9_3_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) {m : ℕ} (hm : 1 ≤ m)
    (hU : IsOpen U) (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Icc a b, (∫ x in a..b, f x) - Quadrature.compositeNewtonCotes n f a b m
      = (b - a) / (n + 2).factorial * (Quadrature.newtonCotesM n / n ^ (n + 3))
        * ((b - a) / m) ^ (n + 2) * iteratedDeriv (n + 2) f ξ :=
  Quadrature.exists_sub_compositeNewtonCotes_eq_of_even hn hn0 hab hm hU hUab hf

/-- **Section 9.4** of [quarteroni2000numerical], convergence for even $n$. Let $n \ge 2$ be even,
let $a < b$, and let $f \in C^{n+2}([a, b])$. Then
$$\lim_{m \to \infty} I_{n,m}(f) = \int_a^b f(x)\,dx.$$

The book states that "for $n$ fixed, $E_{n,m}(f) \to 0$ as $m \to \infty$". The proof uses the
bound (9.26) with $M = \max |f^{(n+2)}|$ and $H^{n+2} \to 0$. -/
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

/-- **Section 9.4** of [quarteroni2000numerical], convergence for odd $n$. Let $n$ be odd, let
$a < b$, and let $f \in C^{n+1}([a, b])$. Then
$$\lim_{m \to \infty} I_{n,m}(f) = \int_a^b f(x)\,dx.$$

The book reads this from (9.27), which is not formalized. The backbone proves the convergence
from the $O(H^{n+1})$ bound that the Lagrange interpolation error gives for every $n$
(`Quadrature.tendsto_compositeNewtonCotes_of_contDiffOn`). Unlike Property 9.1, this needs no
sign hypothesis on the weights. -/
theorem theorem_9_3_tendsto_odd (hn : Odd n) (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) :
    Tendsto (fun m => Quadrature.compositeNewtonCotes n f a b m) atTop
      (𝓝 (∫ x in a..b, f x)) :=
  Quadrature.tendsto_compositeNewtonCotes_of_contDiffOn hn.pos hab hU hUab hf

/-! ### Property 9.1 -/

/-- **Property 9.1** of [quarteroni2000numerical], convergence. Let $n \ge 1$, assume that the
closed Newton–Cotes weights satisfy $w_k \ge 0$ for all $k$, let $a \le b$, and let
$f \in C^0([a, b])$. Then
$$\lim_{m \to \infty} I_{n,m}(f) = \int_a^b f(x)\,dx.$$

The book assumes that the weights of the composite formula (9.25) are nonnegative. For the
closed formulae these weights are $h w_k$, so the hypothesis is $w_k \ge 0$. The proof is the
backbone's `Quadrature.tendsto_compositeNewtonCotes`, a Riemann-sum argument. -/
theorem property_9_1 (hn : 1 ≤ n) (hw : ∀ k, 0 ≤ Quadrature.newtonCotesWeight n k) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun m => Quadrature.compositeNewtonCotes n f a b m) atTop
      (𝓝 (∫ x in a..b, f x)) :=
  Quadrature.tendsto_compositeNewtonCotes hn hw hab hf

/-- **Property 9.1** of [quarteroni2000numerical], the case $n = 0$. Let $a \le b$ and
$f \in C^0([a, b])$. Then the composite midpoint formula (9.7) with $m + 1$ panels of width
$(b - a)/(m + 1)$ converges to $\int_a^b f(x)\,dx$ as $m \to \infty$.

The composite midpoint formula is the composite form of the open formula with $n = 0$, whose
weight $w_0 = 2$ is positive. The proof is the backbone's `Quadrature.tendsto_midpointSum`. -/
theorem property_9_1_midpoint (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun m : ℕ => Quadrature.midpointSum f a ((b - a) / (m + 1)) (m + 1)) atTop
      (𝓝 (∫ x in a..b, f x)) :=
  Quadrature.tendsto_midpointSum hab hf (N := fun m => m + 1) (hs := fun m => (b - a) / (m + 1))
    (fun m => Nat.succ_pos m) (fun m => by push_cast; rfl)
    (by simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a))

/-- **Property 9.1** of [quarteroni2000numerical], the modulus of continuity. For
$f : \mathbb{R} \to \mathbb{R}$, an interval $[a, b]$ and $H \in \mathbb{R}$, the **modulus of
continuity** is
$$\Omega(f; H) = \sup \{|f(x) - f(y)| : x, y \in [a, b],\ x \neq y,\ |x - y| \le H\}.$$

The supremum is `sSup` on $\mathbb{R}$, which is $0$ for the empty set and for a set that is not
bounded above. -/
noncomputable def modulusOfContinuity (f : ℝ → ℝ) (a b H : ℝ) : ℝ :=
  sSup {r | ∃ x ∈ Icc a b, ∃ y ∈ Icc a b, x ≠ y ∧ |x - y| ≤ H ∧ r = |f x - f y|}

/-- Let $f \in C^0([a, b])$, let $x, y \in [a, b]$, and let $|x - y| \le H$. Then
$|f(x) - f(y)| \le \Omega(f; H)$.

The case $x = y$ is included, because $\Omega(f; H) \ge 0$. -/
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

/-- The modulus of continuity is nonnegative: $\Omega(f; H) \ge 0$ for all $f$, $a$, $b$ and $H$. -/
theorem modulusOfContinuity_nonneg (f : ℝ → ℝ) (a b H : ℝ) : 0 ≤ modulusOfContinuity f a b H :=
  Real.sSup_nonneg (by rintro r ⟨u, -, v, -, -, -, rfl⟩; exact abs_nonneg _)

/-- **Property 9.1** of [quarteroni2000numerical], the error bound. Let $n \ge 1$, assume that the
closed Newton–Cotes weights satisfy $w_k \ge 0$ for all $k$, let $a \le b$, let
$f \in C^0([a, b])$, let $m \ge 1$, and let $H = (b - a)/m$. Then
$$\Bigl|\int_a^b f(x)\,dx - I_{n,m}(f)\Bigr| \le 2(b - a)\,\Omega(f; H).$$

The backbone's `Quadrature.abs_sub_compositeNewtonCotes_le` proves the bound with the constant
$1$ in place of $2$. The bound of the book follows, because $\Omega(f; H) \ge 0$. -/
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
