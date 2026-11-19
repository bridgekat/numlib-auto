/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 6.3: Fixed-Point Iterations for Nonlinear Equations

This module formalizes Section 6.3 of [quarteroni2000numerical]. A root of a scalar equation is
computed as a fixed point $\alpha = \varphi(\alpha)$ of an iteration function
$\varphi : \mathbb{R} \to \mathbb{R}$, through the iteration $x^{(k+1)} = \varphi(x^{(k)})$. The
module states the convergence theorem for contractive iteration functions on an interval (Theorem
6.1) with the limit (6.18) of the error ratios, the asymptotic convergence rate (6.20), the local
convergence theorem of Ostrowski (Property 6.3), divergence when $|\varphi'(\alpha)| > 1$ (Remark
6.2), the undecided case $|\varphi'(\alpha)| = 1$ (Example 6.6), and the order of convergence
$p + 1$ when the first $p$ derivatives of $\varphi$ vanish at $\alpha$ (Property 6.4).

Section 6.3.1 applies these results to the chord method and to Newton's method of Section 6.2: the
derivative of the chord iteration function and the linear convergence of the chord method, the order
$2$ of Newton's method at a simple root, the linear convergence of Newton's method at a multiple
root (6.22), and the modified Newton method (6.23) with Exercise 6.2. The proofs specialize
`Numlib.Nonlinear.FixedPoint`, `Numlib.Nonlinear.Order` and `Numlib.Nonlinear.ScalarNewton`.

## Main definitions

* Equation (6.20), `QuarteroniSaccoSaleri.Chapter06.equation_6_20`: the asymptotic convergence rate
  $R = -\log|\varphi'(\alpha)|$.
* Section 6.3.1, `QuarteroniSaccoSaleri.Chapter06.chordIterationFunction`: the iteration function
  $\varphi_{\mathrm{chord}}$ of the chord method.
* Equation (6.23), `QuarteroniSaccoSaleri.Chapter06.equation_6_23`: the modified Newton method for a
  root of known multiplicity $m$.

## Main results

* Theorem 6.1, `QuarteroniSaccoSaleri.Chapter06.theorem_6_1`: a $C^1$ self-map of $[a, b]$ with
  $|\varphi'| \le K < 1$ has a unique fixed point, and every orbit in $[a, b]$ converges to it.
* Theorem 6.1, `QuarteroniSaccoSaleri.Chapter06.theorem_6_1_limit`: the limit (6.18) of the error
  ratios is $\varphi'(\alpha)$.
* Property 6.3, `QuarteroniSaccoSaleri.Chapter06.property_6_3`: if $|\varphi'(\alpha)| < 1$, the
  iteration converges from every starting point close to $\alpha$.
* Remark 6.2, `QuarteroniSaccoSaleri.Chapter06.remark_6_2`: if $|\varphi'(\alpha)| > 1$, no orbit
  that avoids $\alpha$ converges to $\alpha$.
* Example 6.6, `QuarteroniSaccoSaleri.Chapter06.example_6_6_tendsto`: the iteration of $x - x^3$
  converges to $0$ from every point of $[-1, 1]$.
* Example 6.6, `QuarteroniSaccoSaleri.Chapter06.example_6_6_not_tendsto`: the iteration of $x + x^3$
  converges to $0$ from no point $x^{(0)} \neq 0$.
* Property 6.4, `QuarteroniSaccoSaleri.Chapter06.property_6_4`: if $\varphi^{(i)}(\alpha) = 0$ for
  $1 \le i \le p$, the method has order $p + 1$ and the limit (6.21) holds.
* Section 6.3.1, `QuarteroniSaccoSaleri.Chapter06.chordIterationFunction_deriv`:
  $\varphi_{\mathrm{chord}}'(\alpha) = 1 - f'(\alpha)/q$, and its modulus is less than $1$ if and
  only if $0 < f'(\alpha)/q < 2$.
* Section 6.3.1, `QuarteroniSaccoSaleri.Chapter06.chord_tendsto`: under this condition the chord
  method converges linearly.
* Section 6.3.1, `QuarteroniSaccoSaleri.Chapter06.newtonIterationFunction_deriv`: at a simple root,
  $\varphi_{\mathrm{Newt}}'(\alpha) = 0$ and $\varphi_{\mathrm{Newt}}''(\alpha) =
  f''(\alpha)/f'(\alpha)$.
* Section 6.3.1, `QuarteroniSaccoSaleri.Chapter06.newton_order_two`: Newton's method has order $2$
  at a simple root.
* Equation (6.22), `QuarteroniSaccoSaleri.Chapter06.equation_6_22`: at a root of multiplicity
  $m > 1$, Newton's method converges linearly with factor $1 - 1/m$.
* Exercise 6.2, `QuarteroniSaccoSaleri.Chapter06.exercise_6_2`: the limit (6.22) holds for
  $m \ge 1$, and the modified Newton method (6.23) has order $2$.

## Implementation notes

* The fixed-point iteration is `φ^[k] x₀`, the $k$-th iterate of `φ`, and needs no definition of its
  own.
* An order of convergence is `QuarteroniSaccoSaleri.Chapter06.definition_6_1`, the sense of
  Definition 6.1.
* The hypothesis $\varphi \in C^1[a, b]$ of Theorem 6.1 is kept in the statement to match the
  source. The proof uses only the bound on the derivative within the interval.

## Deviations from the source

* **Reading.** The fixed-point error ratio limit is stated for orbits that do not hit the fixed
  point. See `QuarteroniSaccoSaleri.Chapter06.theorem_6_1_limit`.
* **Correction.** The rate is minus the logarithm of the absolute factor, correcting the printed
  sign. See `QuarteroniSaccoSaleri.Chapter06.equation_6_20`.
* **Generalization.** The local attraction theorem replaces continuous differentiability by
  differentiability near the fixed point. See `QuarteroniSaccoSaleri.Chapter06.property_6_3`.
* **Correction.** The repulsion conclusion excludes orbits landing exactly at the fixed point. See
  `QuarteroniSaccoSaleri.Chapter06.remark_6_2`.
* **Specialization.** For the plus-cube example the theorem rules out convergence to zero. See
  `QuarteroniSaccoSaleri.Chapter06.example_6_6_not_tendsto`.
* **Correction.** The vanishing derivative range starts at one, and the limiting ratio is
  conditional when order one is at issue. See `QuarteroniSaccoSaleri.Chapter06.property_6_4`.
* **Convention.** The chord derivative formula is extended to zero slopes by totalized division. See
  `QuarteroniSaccoSaleri.Chapter06.chordIterationFunction`,
  `QuarteroniSaccoSaleri.Chapter06.chordIterationFunction_deriv`.
* **Reading.** Chord convergence is local under the displayed derivative-ratio criterion. See
  `QuarteroniSaccoSaleri.Chapter06.chord_tendsto`.
* **Reading.** Newton's quadratic bound includes faster or finite convergence, and its signed ratio
  limit avoids exact hits. See `QuarteroniSaccoSaleri.Chapter06.newtonIterationFunction_deriv`,
  `QuarteroniSaccoSaleri.Chapter06.newton_order_two`.
* **Reading.** The Newton factor at a multiple root is formulated as a punctured limit with an
  accompanying local bound. See `QuarteroniSaccoSaleri.Chapter06.equation_6_22`.
* **Convention.** Modified Newton uses a supplied derivative and totalized division. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_23`.
* **Generalization.** Exercise 6.2 is allowed for multiplicity one as well as multiple roots. See
  `QuarteroniSaccoSaleri.Chapter06.exercise_6_2`.
* **Theorem 6.1, limit (6.18)** (reading). The limit of the error ratios is stated for orbits that
  never equal $\alpha$. See `QuarteroniSaccoSaleri.Chapter06.theorem_6_1_limit`.
* **Equation (6.20)** (typo). The source prints $R = -\log(1/|\varphi'(\alpha)|)$; the rate is
  $R = -\log|\varphi'(\alpha)|$. See `QuarteroniSaccoSaleri.Chapter06.equation_6_20`.
* **Property 6.4** (typo). The source prints the range $0 \le i \le p$ for the vanishing
  derivatives; the range is $1 \le i \le p$. See `QuarteroniSaccoSaleri.Chapter06.property_6_4`.
* **Property 6.4** (reading). The property presupposes convergence. For $p = 0$ only the limit
  (6.21) along a convergent orbit is stated, and the limit is stated for orbits that never equal
  $\alpha$. See `QuarteroniSaccoSaleri.Chapter06.property_6_4`.
* **Section 6.3.1, order of Newton's method** (generalization). The order $2$ and its constant
  $f''(\alpha)/(2 f'(\alpha))$ are proved for $f \in C^2$; the derivation through Property 6.4 needs
  $f \in C^3$. See `QuarteroniSaccoSaleri.Chapter06.newton_order_two`.
-/

open Filter Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

/-! ### Theorem 6.1 and its consequences -/

section Theorem61

variable {φ φ' : ℝ → ℝ} {a b : ℝ}

-- `φ ∈ C¹[a, b]` (the continuity `hφ'` of the derivative) is the book's hypothesis 2; the proof
-- uses only the derivative bound within the interval
-- (`exists_unique_fixedPoint_Icc_of_abs_deriv_le`).
set_option linter.unusedVariables false in
/-- **Theorem 6.1** of [quarteroni2000numerical] (convergence of fixed-point iterations). Let
$a \le b$, and let $\varphi : \mathbb{R} \to \mathbb{R}$ map $[a, b]$ into itself. Suppose that
$\varphi$ has at each $x \in [a, b]$ the derivative $\varphi'(x)$ within $[a, b]$, that
$\varphi'$ is continuous on $[a, b]$, and that there is $K < 1$ with $|\varphi'(x)| \le K$ for
all $x \in [a, b]$. Then $\varphi$ has exactly one fixed point $\alpha \in [a, b]$, and for
every $x^{(0)} \in [a, b]$ the sequence $x^{(k+1)} = \varphi(x^{(k)})$ converges to $\alpha$.

The second part is stated for every fixed point $\alpha \in [a, b]$, which by the first part is
the unique one. The continuity of $\varphi'$ is the hypothesis $\varphi \in C^1[a, b]$ of the
source; the proof does not use it. The proof specializes
`exists_unique_fixedPoint_Icc_of_abs_deriv_le` and `tendsto_iterate_Icc_of_abs_deriv_le`. -/
theorem theorem_6_1 (hab : a ≤ b) (hmaps : MapsTo φ (Icc a b) (Icc a b))
    (hφ : ∀ x ∈ Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x) (hφ' : ContinuousOn φ' (Icc a b))
    (hK : ∃ K < 1, ∀ x ∈ Icc a b, |φ' x| ≤ K) :
    (∃! α, α ∈ Icc a b ∧ φ α = α) ∧
      ∀ α, α ∈ Icc a b → φ α = α → ∀ x₀ ∈ Icc a b, Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  obtain ⟨K, hK1, hK⟩ := hK
  exact ⟨exists_unique_fixedPoint_Icc_of_abs_deriv_le hab hmaps hφ hK hK1,
    fun α hα hfix x₀ hx₀ => tendsto_iterate_Icc_of_abs_deriv_le hmaps hφ hK hK1 hα hfix hx₀⟩

/-- **Theorem 6.1** of [quarteroni2000numerical], the limit (6.18). Under the hypotheses of
`QuarteroniSaccoSaleri.Chapter06.theorem_6_1`, let $\alpha \in [a, b]$ be the fixed point of
$\varphi$, and let $x^{(0)} \in [a, b]$ be such that $x^{(k)} \neq \alpha$ for all $k$. Then
$$\lim_{k \to \infty} \frac{x^{(k+1)} - \alpha}{x^{(k)} - \alpha} = \varphi'(\alpha).$$

**Reading.** The source does not require that the orbit avoids $\alpha$. Without this condition
the quotient is $0/0$ from some index on.

At an endpoint $\alpha \in \{a, b\}$ the orbit approaches $\alpha$ from inside $[a, b]$, and
$\varphi'(\alpha)$ is the one-sided derivative within $[a, b]$.

**Reading.** The ratio limit requires that the orbit avoid the fixed point, since once it lands
there the real quotient is undefined.
-/
theorem theorem_6_1_limit (hab : a ≤ b) (hmaps : MapsTo φ (Icc a b) (Icc a b))
    (hφ : ∀ x ∈ Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x) (hφ' : ContinuousOn φ' (Icc a b))
    (hK : ∃ K < 1, ∀ x ∈ Icc a b, |φ' x| ≤ K) {α : ℝ} (hα : α ∈ Icc a b) (hfix : φ α = α)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hne : ∀ k, φ^[k] x₀ ≠ α) :
    Tendsto (fun k => (φ^[k + 1] x₀ - α) / (φ^[k] x₀ - α)) atTop (𝓝 (φ' α)) :=
  tendsto_sub_div_sub_of_hasDerivWithinAt (hφ α hα) hfix
    (fun k => Function.iterate_succ_apply' φ k x₀) (fun k => hmaps.iterate k hx₀) hne
    ((theorem_6_1 hab hmaps hφ hφ' hK).2 α hα hfix x₀ hx₀)

/-- **Equation (6.20)** of [quarteroni2000numerical]. The **asymptotic convergence rate** of the
fixed-point iteration with the asymptotic convergence factor $|\varphi'(\alpha)|$ is
$$R = -\log|\varphi'(\alpha)|.$$

**Typo.** The source prints $R = -\log(1/|\varphi'(\alpha)|)$, which is $\le 0$ for a convergent
method. The intended quantity, by analogy with the rate $R(B) = -\log \rho(B)$ of (4.5), is
$-\log|\varphi'(\alpha)|$.

The definition takes the derivative $\varphi'$ as a function. If $\varphi'(\alpha) = 0$, the
value is $0$, because `Real.log 0 = 0`.

**Correction.** The positive decay rate for a contractive nonzero factor is minus the logarithm of
its magnitude. The printed minus sign on the logarithm of the reciprocal reverses that rate. A zero
factor uses the totalized real logarithm.
-/
noncomputable def equation_6_20 (φ' : ℝ → ℝ) (α : ℝ) : ℝ := -Real.log |φ' α|

end Theorem61

section Ostrowski

variable {φ : ℝ → ℝ} {α : ℝ}

/-- **Property 6.3** of [quarteroni2000numerical] (Ostrowski's theorem). Let $\alpha$ be a fixed
point of $\varphi : \mathbb{R} \to \mathbb{R}$, let $\varphi$ be differentiable at every point
of a neighbourhood of $\alpha$, and let $|\varphi'(\alpha)| < 1$. Then there is $\delta > 0$
such that $x^{(k)} = \varphi^k(x^{(0)}) \to \alpha$ for every $x^{(0)}$ with
$|x^{(0)} - \alpha| < \delta$.

The source also assumes that $\varphi$ is continuous near $\alpha$, which follows from
differentiability. The proof specializes `tendsto_iterate_of_abs_deriv_lt_one`, which needs
differentiability at $\alpha$ only.

**Generalization.** Local convergence only needs the differentiability used at the fixed point, with
nearby differentiability harmlessly retained. The statement supplies a radius and all starting
points in that radius.
-/
theorem property_6_3 (hα : φ α = α) (hJ : ∀ᶠ x in 𝓝 α, DifferentiableAt ℝ φ x)
    (h : |deriv φ α| < 1) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ → Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) :=
  tendsto_iterate_of_abs_deriv_lt_one hα hJ.self_of_nhds.hasDerivAt h

/-- **Remark 6.2** of [quarteroni2000numerical]. Let $\alpha$ be a fixed point of
$\varphi : \mathbb{R} \to \mathbb{R}$, let $\varphi$ be differentiable at $\alpha$ with
$|\varphi'(\alpha)| > 1$, and let $x^{(0)}$ be such that the orbit
$x^{(k+1)} = \varphi(x^{(k)})$ satisfies $x^{(k)} \neq \alpha$ for all $k$. Then $x^{(k)}$ does
not converge to $\alpha$.

Near $\alpha$ the error grows at every step. The case $|\varphi'(\alpha)| = 1$ is undecided, as
Example 6.6 shows. The proof specializes `not_tendsto_iterate_of_one_lt_abs_deriv`.

**Correction.** A repelling derivative rules out asymptotic convergence for orbits avoiding the
fixed point. An orbit that lands exactly at the fixed point remains there.
-/
theorem remark_6_2 (hα : φ α = α) (hφ : DifferentiableAt ℝ φ α) (h : 1 < |deriv φ α|) {x₀ : ℝ}
    (hne : ∀ k, φ^[k] x₀ ≠ α) : ¬ Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) :=
  not_tendsto_iterate_of_one_lt_abs_deriv hα hφ.hasDerivAt h
    (fun k => Function.iterate_succ_apply' φ k x₀) hne

end Ostrowski

/-!
### Example 6.6: the case $|\varphi'(\alpha)| = 1$

The iteration functions $x - x^3$ and $x + x^3$ both have the fixed point $0$ with
$\varphi'(0) = 1$. The first iteration converges to $0$ and the second does not.
-/

section Example66

/-- The map $y \mapsto y - y^3$ maps $[0, 1]$ into $[0, 1]$. -/
private theorem sub_cube_mem_Icc {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : y - y ^ 3 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hy
  constructor <;> nlinarith [pow_le_one₀ h0 h1 (n := 2), pow_nonneg h0 2, pow_nonneg h0 3]

/-- For $|x| \le 1$, $|x - x^3| = |x| - |x|^3$. -/
private theorem abs_sub_cube {x : ℝ} (hx : |x| ≤ 1) : |x - x ^ 3| = |x| - |x| ^ 3 := by
  have h3 : |x| ^ 3 = |x ^ 3| := (abs_pow x 3).symm
  have h : x - x ^ 3 = x * (1 - x ^ 2) := by ring
  have hsq : x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg x) hx
  rw [h, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x ^ 2)]
  nlinarith [sq_abs x]

/-- **Example 6.6** of [quarteroni2000numerical], first half. Let $\varphi(x) = x - x^3$, which has
the fixed point $\alpha = 0$ with $\varphi'(0) = 1$. For every $x^{(0)} \in [-1, 1]$, the orbit
$x^{(k)} = \varphi^k(x^{(0)})$ satisfies $x^{(k)} \in (-1, 1)$ for all $k \ge 1$, and
$x^{(k)} \to 0$.

For $x^{(0)} = \pm 1$ the orbit is $0$ from the first step on. In general the convergence is
very slow. The absolute values $y_k = |x^{(k)}|$ satisfy $y_{k+1} = y_k - y_k^3 \in [0, 1]$, so
they decrease to a limit $L$ with $L = L - L^3$, hence $L = 0$. -/
theorem example_6_6_tendsto {x₀ : ℝ} (hx₀ : x₀ ∈ Icc (-1 : ℝ) 1) :
    (∀ k, 1 ≤ k → (fun x : ℝ => x - x ^ 3)^[k] x₀ ∈ Ioo (-1 : ℝ) 1) ∧
      Tendsto (fun k => (fun x : ℝ => x - x ^ 3)^[k] x₀) atTop (𝓝 0) := by
  set φ : ℝ → ℝ := fun x => x - x ^ 3 with hφ
  set y : ℕ → ℝ := fun k => |φ^[k] x₀| with hy
  have hx₀' : |x₀| ≤ 1 := abs_le.2 hx₀
  -- the recursion of the absolute values
  have hy_mem : ∀ k, y k ∈ Icc (0 : ℝ) 1 := by
    intro k
    induction k with
    | zero => exact ⟨abs_nonneg _, hx₀'⟩
    | succ k ih =>
      have : y (k + 1) = y k - y k ^ 3 := by
        simp only [hy, Function.iterate_succ_apply', hφ]
        exact abs_sub_cube ih.2
      rw [this]
      exact sub_cube_mem_Icc ih
  have hy_succ : ∀ k, y (k + 1) = y k - y k ^ 3 := fun k => by
    simp only [hy, Function.iterate_succ_apply', hφ]
    exact abs_sub_cube (hy_mem k).2
  have hanti : Antitone y := antitone_nat_of_succ_le fun k => by
    rw [hy_succ]
    have := (hy_mem k).1
    nlinarith [pow_nonneg this 3]
  have hbdd : BddBelow (range y) := ⟨0, by rintro _ ⟨k, rfl⟩; exact (hy_mem k).1⟩
  have hlimL : Tendsto y atTop (𝓝 (⨅ k, y k)) := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ k, y k with hL
  have hL0 : 0 ≤ L := le_ciInf fun k => (hy_mem k).1
  -- the limit satisfies `L = L - L ^ 3`
  have hL' : Tendsto (fun k => y (k + 1)) atTop (𝓝 (L - L ^ 3)) := by
    have := hlimL.sub (hlimL.pow 3)
    refine this.congr fun k => ?_
    simp [hy_succ]
  have hL'' : Tendsto (fun k => y (k + 1)) atTop (𝓝 L) := hlimL.comp (tendsto_add_atTop_nat 1)
  have hLeq : L = L - L ^ 3 := tendsto_nhds_unique hL'' hL'
  have hLzero : L = 0 := by
    have : L ^ 3 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  rw [hLzero] at hlimL
  refine ⟨fun k hk => ?_, ?_⟩
  · -- the orbit is in the open interval from the first step on
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : y (j + 1) < 1 := by
      rw [hy_succ]
      rcases (hy_mem j).1.lt_or_eq with h0 | h0
      · have := (hy_mem j).2
        nlinarith [pow_pos h0 3]
      · rw [← h0]; norm_num
    have := abs_lt.1 h1
    exact ⟨this.1, this.2⟩
  · exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa [hy] using hlimL)

/-- **Example 6.6** of [quarteroni2000numerical], second half. Let $\varphi(x) = x + x^3$, which has
the fixed point $\alpha = 0$ with $\varphi'(0) = 1$. For every $x^{(0)} \neq 0$, the orbit
$x^{(k)} = \varphi^k(x^{(0)})$ does not converge to $0$.

Since $|x + x^3| \ge |x|$, the orbit satisfies $|x^{(k)}| \ge |x^{(0)}| > 0$ for all $k$. In
fact the orbit diverges.

**Reading.** The source states divergence for the plus-cube map. This declaration rules out
convergence to zero for every nonzero initial value.
-/
theorem example_6_6_not_tendsto {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    ¬ Tendsto (fun k => (fun x : ℝ => x + x ^ 3)^[k] x₀) atTop (𝓝 0) := by
  set φ : ℝ → ℝ := fun x => x + x ^ 3 with hφ
  have hgrow : ∀ k, |x₀| ≤ |φ^[k] x₀| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans ?_
      rw [Function.iterate_succ_apply', hφ]
      simp only
      set z := φ^[k] x₀
      rw [show z + z ^ 3 = z * (1 + z ^ 2) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 + z ^ 2)]
      exact le_mul_of_one_le_right (abs_nonneg z) (by nlinarith [sq_nonneg z])
  intro hlim
  have hpos : 0 < |x₀| := abs_pos.2 hx₀
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (gt_mem_nhds hpos))
  have := hN N le_rfl
  simp only [sub_zero, Real.norm_eq_abs] at this
  exact absurd (hgrow N) (not_le.2 this)

end Example66

section Property64

variable {φ : ℝ → ℝ} {α : ℝ}

-- `φ^{(p+1)}(α) ≠ 0` is part of the book's statement; it makes the order exactly `p + 1` and is
-- not needed for the order bound or the limit.
set_option linter.unusedVariables false in
/-- **Property 6.4** of [quarteroni2000numerical]. Let $p \in \mathbb{N}$, let $\alpha$ be a fixed
point of $\varphi : \mathbb{R} \to \mathbb{R}$, let $\varphi$ be of class $C^{p+1}$ on a
neighbourhood of $\alpha$, and let $\varphi^{(i)}(\alpha) = 0$ for $1 \le i \le p$ and
$\varphi^{(p+1)}(\alpha) \neq 0$. Then:

* if $p \ge 1$, there is $\varepsilon > 0$ such that for every $x^{(0)}$ with
  $|x^{(0)} - \alpha| < \varepsilon$ the orbit $x^{(k)} = \varphi^k(x^{(0)})$ converges to
  $\alpha$ with order $p + 1$ in the sense of Definition 6.1;
* for every $x^{(0)}$ whose orbit converges to $\alpha$ and satisfies $x^{(k)} \neq \alpha$ for
  all $k$, the limit (6.21) holds: $$\lim_{k \to \infty} \frac{x^{(k+1)} - \alpha}{(x^{(k)} -
  \alpha)^{p+1}} = \frac{\varphi^{(p+1)}(\alpha)}{(p + 1)!}.$$

**Typo.** The source prints the range $0 \le i \le p$. The case $i = 0$ would require
$\varphi(\alpha) = 0$, so the range is $1 \le i \le p$.

**Reading.** The property presupposes that the method converges. For $p \ge 1$ convergence near
$\alpha$ is proved. For $p = 0$ only the limit is stated, and convergence is assumed, as in the
first line of the proof of the source. The limit needs an orbit that never equals $\alpha$,
which the source does not say.

The hypothesis $\varphi^{(p+1)}(\alpha) \neq 0$ is part of the statement of the source. It makes
the order exactly $p + 1$, and the proof of the order bound and of the limit does not use it.
The order is `QuarteroniSaccoSaleri.Chapter06.definition_6_1`. The proof specializes
`hasIterationOrder_of_iteratedDeriv_eq_zero` and `tendsto_sub_div_pow_of_iteratedDeriv_eq_zero`.

**Correction.** The derivative vanishing range starts at one, because the zeroth derivative is the
fixed-point value. The ratio is a limit for a convergent orbit that avoids the fixed point. Local
convergence follows for positive p, while p = 0 alone gives no local convergence guarantee.
-/
theorem property_6_4 {p : ℕ} (hφ : ContDiffAt ℝ (p + 1 : ℕ) φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i φ α = 0) (hp' : iteratedDeriv (p + 1) φ α ≠ 0) :
    (1 ≤ p → ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (fun k => φ^[k] x₀) α (p + 1)) ∧
      ∀ x₀, (∀ k, φ^[k] x₀ ≠ α) → Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) →
        Tendsto (fun k => (φ^[k + 1] x₀ - α) / (φ^[k] x₀ - α) ^ (p + 1)) atTop
          (𝓝 (iteratedDeriv (p + 1) φ α / (p + 1).factorial)) := by
  refine ⟨fun hp => ?_, fun x₀ hne hlim => ?_⟩
  · obtain ⟨ε, hε, h⟩ := hasIterationOrder_of_iteratedDeriv_eq_zero hp hφ hα hzero
    refine ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder ?_ ?_⟩
    · have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    · have := h x₀ hx₀
      simpa using this
  · exact tendsto_sub_div_pow_of_iteratedDeriv_eq_zero hφ hα hzero
      (fun k => Function.iterate_succ_apply' φ k x₀) hne hlim

end Property64

/-! ### Section 6.3.1: Convergence results for some fixed-point methods -/

section Chord631

variable {f : ℝ → ℝ} {a b α f' : ℝ}

/-- **Section 6.3.1** of [quarteroni2000numerical], the iteration function of the chord method. For
$f : \mathbb{R} \to \mathbb{R}$ and $a, b \in \mathbb{R}$, it is
$$\varphi_{\mathrm{chord}}(x) = x - \frac{b - a}{f(b) - f(a)} f(x).$$

Its iteration is the chord method `QuarteroniSaccoSaleri.Chapter06.chord`. If $f(b) = f(a)$, the
quotient is $0$ and $\varphi_{\mathrm{chord}}$ is the identity.

**Reading.** The slope and inverse are totalized. For nonzero chord slope the derivative and
contraction criterion agree with the formula in the source.
-/
noncomputable def chordIterationFunction (f : ℝ → ℝ) (a b : ℝ) (x : ℝ) : ℝ :=
  x - (b - a) / (f b - f a) * f x

/-- The chord iteration function $\varphi_{\mathrm{chord}}$ is the backbone step `Chord.step`
$x \mapsto x - f(x)/q$ with the slope $q = (f(b) - f(a))/(b - a)$. -/
theorem chordIterationFunction_eq (f : ℝ → ℝ) (a b : ℝ) :
    chordIterationFunction f a b = Chord.step f ((f b - f a) / (b - a)) := by
  funext x
  simp only [chordIterationFunction, Chord.step, div_div_eq_mul_div]
  ring

/-- The chord method is the fixed-point iteration of $\varphi_{\mathrm{chord}}$: for every $x^{(0)}$
and $k$, the $k$-th chord iterate `QuarteroniSaccoSaleri.Chapter06.chord` from $x^{(0)}$ is
$\varphi_{\mathrm{chord}}^k(x^{(0)})$. -/
theorem chord_eq_iterate (f : ℝ → ℝ) (a b x₀ : ℝ) (k : ℕ) :
    chord f a b x₀ k = (chordIterationFunction f a b)^[k] x₀ := by
  rw [chord, chordIterationFunction_eq]

/-- **Section 6.3.1** of [quarteroni2000numerical], the chord method. Let
$f : \mathbb{R} \to \mathbb{R}$ have the derivative $f'(\alpha)$ at a point $\alpha$, and let
$q = (f(b) - f(a))/(b - a)$. Then

* $\varphi_{\mathrm{chord}}$ has the derivative $\varphi_{\mathrm{chord}}'(\alpha) = 1 -
  f'(\alpha)/q$ at $\alpha$;
* if $f'(\alpha) = 0$, then $\varphi_{\mathrm{chord}}'(\alpha) = 1$;
* $|1 - f'(\alpha)/q| < 1$ if and only if $0 < f'(\alpha)/q < 2$.

The last condition says that $q$ has the sign of $f'(\alpha)$ and $|q| > |f'(\alpha)|/2$. In the
source $\alpha$ is the root of $f$; the statement holds at every point. The proof specializes
`Chord.hasDerivAt_step` and `Chord.abs_one_sub_div_lt_one_iff`.

**Reading.** The slope and inverse are totalized. For nonzero chord slope the derivative and
contraction criterion agree with the formula in the source.
-/
theorem chordIterationFunction_deriv (hf : HasDerivAt f f' α) :
    HasDerivAt (chordIterationFunction f a b) (1 - f' / ((f b - f a) / (b - a))) α ∧
      (f' = 0 → 1 - f' / ((f b - f a) / (b - a)) = 1) ∧
      (|1 - f' / ((f b - f a) / (b - a))| < 1 ↔
        0 < f' / ((f b - f a) / (b - a)) ∧ f' / ((f b - f a) / (b - a)) < 2) := by
  rw [chordIterationFunction_eq]
  exact ⟨Chord.hasDerivAt_step hf, fun h => by simp [h], Chord.abs_one_sub_div_lt_one_iff⟩

/-- **Section 6.3.1** of [quarteroni2000numerical], linear convergence of the chord method. Let
$f(\alpha) = 0$, let $f$ have the derivative $f'(\alpha)$ at $\alpha$, let
$q = (f(b) - f(a))/(b - a)$, and let $0 < f'(\alpha)/q < 2$. Then there is $\delta > 0$ such
that for every $x^{(0)}$ with $|x^{(0)} - \alpha| < \delta$ the chord iterates $x^{(k)}$:

* converge to $\alpha$;
* converge to $\alpha$ with order $1$ in the sense of Definition 6.1;
* satisfy, if $x^{(k)} \neq \alpha$ for all $k$, $$\lim_{k \to \infty} \frac{x^{(k+1)} -
  \alpha}{x^{(k)} - \alpha} = 1 - \frac{f'(\alpha)}{q}.$$

The convergence factor $|1 - f'(\alpha)/q|$ is $0$ in the case $f'(\alpha) = q$. The theorem is
Ostrowski's theorem for $\varphi_{\mathrm{chord}}$; the proof specializes
`Chord.tendsto_iterate` and `Chord.tendsto_sub_div_sub`.

**Reading.** The local convergence theorem uses the strict contraction criterion in the source and
gives an order-one bound even when the limiting ratio is zero. The ratio is stated for orbits
missing the root.
-/
theorem chord_tendsto (hα : f α = 0) (hf : HasDerivAt f f' α)
    (h0 : 0 < f' / ((f b - f a) / (b - a))) (h2 : f' / ((f b - f a) / (b - a)) < 2) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ →
      Tendsto (chord f a b x₀) atTop (𝓝 α) ∧ definition_6_1 (chord f a b x₀) α 1 ∧
        ((∀ k, chord f a b x₀ k ≠ α) →
          Tendsto (fun k => (chord f a b x₀ (k + 1) - α) / (chord f a b x₀ k - α)) atTop
            (𝓝 (1 - f' / ((f b - f a) / (b - a))))) := by
  set q := (f b - f a) / (b - a) with hq
  have hlt : |1 - f' / q| < 1 := Chord.abs_one_sub_div_lt_one_iff.2 ⟨h0, h2⟩
  obtain ⟨c, hc, hc1⟩ := exists_between hlt
  have hc0 : 0 < c := (abs_nonneg _).trans_lt hc
  obtain ⟨δ, hδ, hconv⟩ := Chord.tendsto_iterate hα hf h0 h2
  refine ⟨δ, hδ, fun x₀ hx₀ => ⟨hconv x₀ hx₀, ?_, fun hne => ?_⟩⟩
  · refine definition_6_1_of_convergesWithOrder le_rfl
      (convergesWithOrder_one_of_eventually_norm_sub_succ_le hc0 hc1 ?_)
    have hev := eventually_abs_sub_le_mul_of_hasDerivAt (by simp [Chord.step, hα])
      (Chord.hasDerivAt_step (q := q) hf) hc
    filter_upwards [(hconv x₀ hx₀).eventually hev] with k hk
    simpa [chord, Function.iterate_succ_apply', Real.norm_eq_abs] using hk
  · exact Chord.tendsto_sub_div_sub hα hf (fun k => Function.iterate_succ_apply' _ k x₀) hne
      (hconv x₀ hx₀)

end Chord631

section Newton631

variable {f : ℝ → ℝ} {α : ℝ}

/-- **Section 6.3.1** of [quarteroni2000numerical], Newton's method at a simple root. Let
$f(\alpha) = 0$, let $f$ be of class $C^2$ on a neighbourhood of $\alpha$, and let
$f'(\alpha) \neq 0$. Let $\varphi_{\mathrm{Newt}}(x) = x - f(x)/f'(x)$. Then
$\varphi_{\mathrm{Newt}}$ has the derivative $\varphi_{\mathrm{Newt}}'(\alpha) = 0$ at $\alpha$.
If moreover $f$ is of class $C^3$ on a neighbourhood of $\alpha$, then
$$\varphi_{\mathrm{Newt}}''(\alpha) = \frac{f''(\alpha)}{f'(\alpha)}.$$

The iteration function $\varphi_{\mathrm{Newt}}$ is `Newton.scalarStep f (deriv f)`. The proof
specializes `Newton.hasDerivAt_scalarStep` and `Newton.deriv2_scalarStep_root`.

**Reading.** At a smooth simple root, the quadratic bound permits vanishing second derivative and
finite termination. The signed quotient limit requires an orbit avoiding the root. The separate
second derivative identity assumes one additional derivative of the function.
-/
theorem newtonIterationFunction_deriv (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) :
    HasDerivAt (Newton.scalarStep f (deriv f)) 0 α ∧
      (ContDiffAt ℝ 3 f α →
        iteratedDeriv 2 (Newton.scalarStep f (deriv f)) α = iteratedDeriv 2 f α / deriv f α) := by
  refine ⟨?_, fun hf3 => Newton.deriv2_scalarStep_root hf3 hα hf'⟩
  have h := Newton.hasDerivAt_scalarStep (hf.differentiableAt (by norm_num)).hasDerivAt
    (hasDerivAt_deriv_of_contDiffAt_two hf) hf'
  rwa [hα, zero_mul, zero_div] at h

/-- **Section 6.2.2** of [quarteroni2000numerical], the order of Newton's method, which the source
proves in Section 6.3.1. Let $f(\alpha) = 0$, let $f$ be of class $C^2$ on a neighbourhood of
$\alpha$, and let $f'(\alpha) \neq 0$. Then:

* there is $\varepsilon > 0$ such that for every $x^{(0)}$ with
  $|x^{(0)} - \alpha| < \varepsilon$ the Newton iterates converge to $\alpha$ with order $2$ in
  the sense of Definition 6.1;
* for every $x^{(0)}$ whose Newton iterates converge to $\alpha$ and satisfy
  $x^{(k)} \neq \alpha$ for all $k$, $$\lim_{k \to \infty} \frac{x^{(k+1)} - \alpha}{(x^{(k)} -
  \alpha)^2} = \frac{f''(\alpha)}{2 f'(\alpha)}.$$

**Generalization.** The source obtains the order and the constant
$\varphi_{\mathrm{Newt}}''(\alpha)/2!$ from Property 6.4 with $p = 1$, which needs $f \in C^3$.
Here $f \in C^2$ is enough.

The Newton iterates are `QuarteroniSaccoSaleri.Chapter06.newton f (deriv f)`. The proof
specializes `Newton.hasIterationOrder_scalarStep_two` and
`Newton.tendsto_scalarStep_sub_div_sq`.

**Reading.** At a smooth simple root, the quadratic bound permits vanishing second derivative and
finite termination. The signed quotient limit requires an orbit avoiding the root. The separate
second derivative identity assumes one additional derivative of the function.
-/
theorem newton_order_two (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α) (hf' : deriv f α ≠ 0) :
    (∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (newton f (deriv f) x₀) α 2) ∧
      ∀ x₀, (∀ k, newton f (deriv f) x₀ k ≠ α) → Tendsto (newton f (deriv f) x₀) atTop (𝓝 α) →
        Tendsto (fun k => (newton f (deriv f) x₀ (k + 1) - α) / (newton f (deriv f) x₀ k - α) ^ 2)
          atTop (𝓝 (iteratedDeriv 2 f α / (2 * deriv f α))) := by
  refine ⟨?_, fun x₀ hne hlim => ?_⟩
  · obtain ⟨ε, hε, h⟩ := Newton.hasIterationOrder_scalarStep_two hα hf hf'
    exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder one_le_two (h x₀ hx₀)⟩
  · have := (Newton.tendsto_scalarStep_sub_div_sq hα hf hf').comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
    refine this.congr fun k => ?_
    simp [Function.comp, newton, Function.iterate_succ_apply']

/-- **Equation (6.22)** of [quarteroni2000numerical]. Let $m > 1$, let $f$ be of class $C^{m+1}$ on
a neighbourhood of $\alpha$, and let $\alpha$ be a root of $f$ of multiplicity $m$. Let
$\varphi_{\mathrm{Newt}}(x) = x - f(x)/f'(x)$. Then
$$\lim_{x \to \alpha,\ x \neq \alpha} \frac{\varphi_{\mathrm{Newt}}(x) - \alpha}{x - \alpha} =
  1 - \frac{1}{m},$$
and there is $\varepsilon > 0$ such that for every $x^{(0)}$ with
$|x^{(0)} - \alpha| < \varepsilon$ the Newton iterates converge to $\alpha$ with order $1$ in
the sense of Definition 6.1.

The limit is the meaning of $\varphi_{\mathrm{Newt}}'(\alpha) = 1 - 1/m$ in the source. Newton's
method is then no longer of order $2$, and converges linearly with factor $1 - 1/m$. The
multiplicity is `IsRootOfMultiplicity`: $f^{(i)}(\alpha) = 0$ for $i < m$ and
$f^{(m)}(\alpha) \neq 0$. The proof specializes
`Newton.tendsto_scalarStep_sub_div_of_isRootOfMultiplicity` and
`Newton.hasIterationOrder_scalarStep_one_of_isRootOfMultiplicity`.

**Reading.** The derivative at a multiple root is first expressed as a punctured limit for the
continuously extended Newton step. The theorem uses smoothness through order one above the
multiplicity and adds the consequent local order-one bound.
-/
theorem equation_6_22 {m : ℕ} (hm : 1 < m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (Newton.scalarStep f (deriv f) x - α) / (x - α)) (𝓝[≠] α)
        (𝓝 (1 - 1 / m)) ∧
      ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (newton f (deriv f) x₀) α 1 := by
  refine ⟨Newton.tendsto_scalarStep_sub_div_of_isRootOfMultiplicity (by omega) hf hα, ?_⟩
  obtain ⟨ε, hε, h⟩ := Newton.hasIterationOrder_scalarStep_one_of_isRootOfMultiplicity hm hf hα
  exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder le_rfl (h x₀ hx₀)⟩

/-- **Equation (6.23)** of [quarteroni2000numerical], the **modified Newton method** for a root of
known multiplicity $m$:
$$x^{(k+1)} = x^{(k)} - m \frac{f(x^{(k)})}{f'(x^{(k)})}.$$

The value at $k$ is the $k$-th iterate of `Newton.modifiedScalarStep f f' m` from $x^{(0)}$. The
derivative $f'$ is passed as a function.

**Reading.** The rule accepts a supplied derivative function and uses totalized division, fixing a
point when its denominator is zero.
-/
noncomputable def equation_6_23 (f f' : ℝ → ℝ) (m : ℕ) (x₀ : ℝ) (k : ℕ) : ℝ :=
  (Newton.modifiedScalarStep f f' m)^[k] x₀

/-- **Exercise 6.2** of [quarteroni2000numerical], which Section 6.3.1 cites for (6.22) and (6.23).
Let $m \ge 1$, let $f$ be of class $C^{m+1}$ on a neighbourhood of $\alpha$, and let $\alpha$ be
a root of $f$ of multiplicity $m$. Then
$$\lim_{x \to \alpha,\ x \neq \alpha} \frac{\varphi_{\mathrm{Newt}}(x) - \alpha}{x - \alpha} =
  1 - \frac{1}{m},$$
which is $0$ for $m = 1$, and there is $\varepsilon > 0$ such that for every $x^{(0)}$ with
$|x^{(0)} - \alpha| < \varepsilon$ the modified Newton method (6.23), with the exact derivative
of $f$, converges to $\alpha$ with order $2$ in the sense of Definition 6.1.

The hint of the exercise, $f(x) = (x - \alpha)^m h(x)$ with $h(\alpha) \neq 0$, is
`IsRootOfMultiplicity.exists_eq_pow_mul`. The proof of the order specializes
`Newton.hasIterationOrder_modifiedScalarStep_two`.

**Generalization.** The theorem states both conclusions using a punctured limit and a local order
bound, and also allows multiplicity one.
-/
theorem exercise_6_2 {m : ℕ} (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (Newton.scalarStep f (deriv f) x - α) / (x - α)) (𝓝[≠] α)
        (𝓝 (1 - 1 / m)) ∧
      ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (equation_6_23 f (deriv f) m x₀) α 2 := by
  refine ⟨Newton.tendsto_scalarStep_sub_div_of_isRootOfMultiplicity hm hf hα, ?_⟩
  obtain ⟨ε, hε, h⟩ := Newton.hasIterationOrder_modifiedScalarStep_two hm hf hα
  exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder one_le_two (h x₀ hx₀)⟩

end Newton631

end QuarteroniSaccoSaleri.Chapter06
