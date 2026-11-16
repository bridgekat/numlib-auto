/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 6.6: Post-Processing Techniques for Iterative Methods

This module formalizes Section 6.6 of [quarteroni2000numerical]. Aitken's $\Delta^2$ acceleration
(Section 6.6.1) estimates the factor $\varphi'(\alpha)$ of a fixed-point iteration
$x^{(k+1)} = \varphi(x^{(k)})$ by the increment ratio $\lambda^{(k)}$ of (6.33), and extrapolates
the iterates by the formula (6.36), written with differences in (6.37). Aitken's method is the
fixed-point iteration of the function $\varphi_\Delta$ of (6.38). It has order $2$ when
$\varphi'(\alpha) \neq 1$, and order $2p - 1$ when the iteration of $\varphi$ has order $p \ge 2$
(Property 6.7). Section 6.6.2 estimates the multiplicity of a root from the Newton iterates by
$m^{(k)} = 1 / (1 - \lambda^{(k)})$ (6.40), and uses this estimate in the adaptive Newton method
(6.39).

Exercise 6.5 (Steffensen's method) is in this module, because it is the concrete instance of
Property 6.7 for $p = 1$, and because the correct reading of the last clause of Property 6.7
concerns it. The proofs specialize `Numlib.Nonlinear.Order` and `Numlib.Nonlinear.ScalarNewton`.

## Main definitions

* Equation (6.33), `QuarteroniSaccoSaleri.Chapter06.equation_6_33`: the increment ratio
  $\lambda^{(k)}$.
* Equation (6.36), `QuarteroniSaccoSaleri.Chapter06.equation_6_36`: Aitken's extrapolation formula.
* Equation (6.38), `QuarteroniSaccoSaleri.Chapter06.equation_6_38`: the iteration function
  $\varphi_\Delta$ of Aitken's method.
* Exercise 6.5, `QuarteroniSaccoSaleri.Chapter06.steffensen`: Steffensen's method.
* Equation (6.40), `QuarteroniSaccoSaleri.Chapter06.equation_6_40`: the multiplicity estimate
  $m^{(k)} = 1 / (1 - \lambda^{(k)})$.
* Equation (6.39), `QuarteroniSaccoSaleri.Chapter06.equation_6_39`: the adaptive Newton method.

## Main results

* Equation (6.34), `QuarteroniSaccoSaleri.Chapter06.equation_6_34`: along a fixed-point orbit,
  $\lambda^{(k)} \to \varphi'(\alpha)$.
* Equation (6.37), `QuarteroniSaccoSaleri.Chapter06.equation_6_37`: Aitken's formula in the form
  $x^{(k)} - (\Delta x^{(k)})^2 / \Delta^2 x^{(k-1)}$.
* Section 6.6.1, `QuarteroniSaccoSaleri.Chapter06.equation_6_38_fixedPoints`: $\varphi_\Delta$ is
  continuous at $\alpha$ with $\varphi_\Delta(\alpha) = \alpha$ and $\varphi_\Delta'(\alpha) = 0$,
  and it has the fixed points of $\varphi$.
* Property 6.7, `QuarteroniSaccoSaleri.Chapter06.property_6_7_one`: if $\varphi'(\alpha) \neq 1$,
  Aitken's method has order $2$.
* Property 6.7, `QuarteroniSaccoSaleri.Chapter06.property_6_7_higher`: if the iteration of $\varphi$
  has order $p \ge 2$, Aitken's method has order $2p - 1$.
* Exercise 6.5, `QuarteroniSaccoSaleri.Chapter06.exercise_6_5`: Steffensen's method has order $2$ at
  a simple root.
* Property 6.7, `QuarteroniSaccoSaleri.Chapter06.property_6_7_multiple`: at a root of multiplicity
  $m \ge 2$, Steffensen's method converges linearly with factor $1 - 1/m$.
* Equation (6.40), `QuarteroniSaccoSaleri.Chapter06.equation_6_40_eq_div`: the second form of the
  multiplicity estimate.
* Section 6.6.2, `QuarteroniSaccoSaleri.Chapter06.equation_6_40_tendsto`: along the Newton iterates,
  $m^{(k)} \to m$.

## Implementation notes

* The source starts the increment ratio (6.33), Aitken's formula (6.36) and the estimate (6.40) at
  $k \ge 2$. The backbone's `aitkenRatio`, `aitkenExtrapolation` and `Newton.multiplicityEstimate`
  start at $k = 0$. The shifts are `QuarteroniSaccoSaleri.Chapter06.equation_6_33_eq`,
  `QuarteroniSaccoSaleri.Chapter06.equation_6_36_eq` and
  `QuarteroniSaccoSaleri.Chapter06.equation_6_40_eq`.
* An order of convergence is `QuarteroniSaccoSaleri.Chapter06.definition_6_1`, the sense of
  Definition 6.1.

## Deviations from the source

* **Equation (6.34)** (generalization). The source assumes linear convergence; the limit holds
  whenever $\varphi'(\alpha) \neq 1$. See `QuarteroniSaccoSaleri.Chapter06.equation_6_34`.
* **Equation (6.34)** (reading). The limit is stated for orbits that never equal $\alpha$. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_34`.
* **Property 6.7, case $p = 1$** (reading). An iteration of order $1$ for a simple zero is read as
  $\varphi(\alpha) = \alpha$, $\varphi \in C^2$ near $\alpha$ and $\varphi'(\alpha) \neq 1$. See
  `QuarteroniSaccoSaleri.Chapter06.property_6_7_one`.
* **Property 6.7, case $p \ge 2$** (generalization). The source assumes $\varphi \in C^{2p}$ near
  $\alpha$; $\varphi \in C^p$ is enough. See `QuarteroniSaccoSaleri.Chapter06.property_6_7_higher`.
* **Property 6.7, last clause** (correction). The source says that at a root of multiplicity
  $m \ge 2$ Aitken's method for a first-order method converges linearly with factor $1 - 1/m$. This
  is false, since $\varphi_\Delta'(\alpha) = 0$ whenever $\varphi'(\alpha) \neq 1$. The statement
  holds for Steffensen's method. See `QuarteroniSaccoSaleri.Chapter06.property_6_7_multiple`.
-/

open Filter Set Topology
open scoped fwdDiff

namespace QuarteroniSaccoSaleri.Chapter06

/-! ### Section 6.6.1: Aitken's acceleration -/

section Aitken

variable {φ : ℝ → ℝ} {α : ℝ}

/-- **Equation (6.33)** of [quarteroni2000numerical], the **increment ratio**
$$\lambda^{(k)} = \frac{x^{(k)} - x^{(k-1)}}{x^{(k-1)} - x^{(k-2)}}$$
of a real sequence $x^{(k)}$, for $k \ge 2$.

For $k < 2$ the subtractions of indices truncate at $0$, and the value is $0$. -/
noncomputable def equation_6_33 (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (x k - x (k - 1)) / (x (k - 1) - x (k - 2))

/-- The increment ratio (6.33) at $k + 2$ is the backbone's `aitkenRatio` at $k$. -/
theorem equation_6_33_eq (x : ℕ → ℝ) (k : ℕ) : equation_6_33 x (k + 2) = aitkenRatio x k := by
  simp [equation_6_33, aitkenRatio]

/-- **Equation (6.34)** of [quarteroni2000numerical]. Let $\varphi : \mathbb{R} \to \mathbb{R}$ be
differentiable at a fixed point $\alpha = \varphi(\alpha)$ with $\varphi'(\alpha) \neq 1$. Let
$x^{(k+1)} = \varphi(x^{(k)})$ for all $k$, with $x^{(k)} \to \alpha$ and $x^{(k)} \neq \alpha$
for all $k$. Then the increment ratios (6.33) satisfy
$$\lim_{k \to \infty} \lambda^{(k)} = \varphi'(\alpha).$$

**Generalization.** The derivation of the source assumes that the iteration converges linearly.
The condition $\varphi'(\alpha) \neq 1$ is enough; for Newton's method, $\varphi'(\alpha) = 0$
and the limit is $0$.

**Reading.** The source does not say that the orbit must avoid $\alpha$; without this condition
the ratios are $0/0$ from some index on.

The proof specializes `tendsto_aitkenRatio` with `tendsto_sub_div_sub_of_hasDerivAt`. -/
theorem equation_6_34 (hφ : DifferentiableAt ℝ φ α) (hα : φ α = α) (h1 : deriv φ α ≠ 1)
    {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) : Tendsto (equation_6_33 x) atTop (𝓝 (deriv φ α)) := by
  have h := tendsto_aitkenRatio hne (tendsto_sub_div_sub_of_hasDerivAt hφ.hasDerivAt hα hx hne hlim)
    h1
  rw [← tendsto_add_atTop_iff_nat 2]
  exact h.congr fun k => (equation_6_33_eq x k).symm

/-- **Equation (6.36)** of [quarteroni2000numerical], **Aitken's extrapolation formula**
$$\hat{x}^{(k)} = x^{(k)} - \frac{(x^{(k)} - x^{(k-1)})^2}{(x^{(k)} - x^{(k-1)}) - (x^{(k-1)} -
  x^{(k-2)})}$$
for a real sequence $x^{(k)}$ and $k \ge 2$.

For $k < 2$ the subtractions of indices truncate at $0$, and the value has no meaning. If the
denominator is $0$, the value is $x^{(k)}$, because division by $0$ gives $0$ in Lean. -/
noncomputable def equation_6_36 (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  x k - (x k - x (k - 1)) ^ 2 / ((x k - x (k - 1)) - (x (k - 1) - x (k - 2)))

/-- Aitken's formula (6.36) at $k + 2$ is the backbone's `aitkenExtrapolation` at $k$. -/
theorem equation_6_36_eq (x : ℕ → ℝ) (k : ℕ) :
    equation_6_36 x (k + 2) = aitkenExtrapolation x k := by
  simp [equation_6_36, aitkenExtrapolation]

/-- **Equation (6.37)** of [quarteroni2000numerical], the $\Delta^2$ form of Aitken's formula. Let
$x^{(k)}$ be a real sequence and $k \ge 2$. With $\Delta x^{(k)} = x^{(k)} - x^{(k-1)}$ and
$\Delta^2 x^{(k)} = \Delta x^{(k+1)} - \Delta x^{(k)}$,
$$\hat{x}^{(k)} = x^{(k)} - \frac{(\Delta x^{(k)})^2}{\Delta^2 x^{(k-1)}}.$$

The source uses backward differences. The statement uses Mathlib's forward difference `fwdDiff`
with step $1$: its value at $k - 1$ is $\Delta x^{(k)}$, and the value of its second iterate at
$k - 2$ is $\Delta^2 x^{(k-1)}$. The proof specializes `aitkenExtrapolation_eq_sub_div_fwdDiff`. -/
theorem equation_6_37 (x : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) :
    equation_6_36 x k = x k - (Δ_[1] x (k - 1)) ^ 2 / (Δ_[1]^[2] x (k - 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [equation_6_36_eq, aitkenExtrapolation_eq_sub_div_fwdDiff]
  simp

/-- **Equation (6.38)** of [quarteroni2000numerical], the **iteration function of Aitken's method**
$$\varphi_\Delta(x) = \frac{x \varphi(\varphi(x)) - \varphi(x)^2}{\varphi(\varphi(x)) - 2
  \varphi(x) + x},$$
with $\varphi_\Delta(x) = x$ where the denominator vanishes. Aitken's method is the fixed-point
iteration $x^{(k+1)} = \varphi_\Delta(x^{(k)})$ of Program 55.

The definition is the backbone's `aitkenIterationFunction`. The value $x$ where the denominator
vanishes makes every fixed point of $\varphi$, where the quotient is $0/0$, a fixed point of
$\varphi_\Delta$. -/
noncomputable def equation_6_38 (φ : ℝ → ℝ) : ℝ → ℝ := aitkenIterationFunction φ

/-- **Section 6.6.1** of [quarteroni2000numerical], the two remarks after (6.38). Let
$\varphi : \mathbb{R} \to \mathbb{R}$ be differentiable at a fixed point
$\alpha = \varphi(\alpha)$ with $\varphi'(\alpha) \neq 1$. Then:

* $\varphi_\Delta(x) \to \alpha$ as $x \to \alpha$;
* $\varphi_\Delta$ has the derivative $\varphi_\Delta'(\alpha) = 0$ at $\alpha$;
* $\varphi_\Delta(\alpha) = \alpha$;
* for every $x$ with $\varphi(\varphi(x)) - 2 \varphi(x) + x \neq 0$, $\varphi_\Delta(x) = x$ if
  and only if $\varphi(x) = x$.

The first item is the L'Hôpital argument of the source, and the last item says that, where the
denominator does not vanish, $\varphi_\Delta$ and $\varphi$ have the same fixed points. The
proof specializes `hasDerivAt_aitkenIterationFunction_zero`,
`aitkenIterationFunction_apply_self` and `aitkenIterationFunction_eq_self_iff`. -/
theorem equation_6_38_fixedPoints (hφ : DifferentiableAt ℝ φ α) (hα : φ α = α)
    (h1 : deriv φ α ≠ 1) :
    Tendsto (equation_6_38 φ) (𝓝 α) (𝓝 α) ∧ HasDerivAt (equation_6_38 φ) 0 α ∧
      equation_6_38 φ α = α ∧
      ∀ x, φ (φ x) - 2 * φ x + x ≠ 0 → (equation_6_38 φ x = x ↔ φ x = x) := by
  have hd := hasDerivAt_aitkenIterationFunction_zero hφ.hasDerivAt hα h1
  refine ⟨?_, hd, aitkenIterationFunction_apply_self hα,
    fun x hx => aitkenIterationFunction_eq_self_iff hx⟩
  have := hd.continuousAt.tendsto
  rwa [aitkenIterationFunction_apply_self hα] at this

/-- **Property 6.7** of [quarteroni2000numerical], the case $p = 1$. Let $\alpha$ be a fixed point
of $\varphi : \mathbb{R} \to \mathbb{R}$, let $\varphi$ be of class $C^2$ on a neighbourhood of
$\alpha$, and let $\varphi'(\alpha) \neq 1$. Then there is $\varepsilon > 0$ such that for every
$x^{(0)}$ with $|x^{(0)} - \alpha| < \varepsilon$ the iterates $\varphi_\Delta^k(x^{(0)})$ of
Aitken's method converge to $\alpha$ with order $2$ in the sense of Definition 6.1.

**Reading.** The source assumes a fixed-point iteration of order $1$ for a simple zero $\alpha$.
This is read as $\varphi(\alpha) = \alpha$, $\varphi \in C^2$ near $\alpha$ and
$\varphi'(\alpha) \neq 1$. Nothing more is assumed, so the conclusion holds "even if the
fixed-point method is not" convergent, as the source says.

The proof specializes `hasIterationOrder_aitkenIterationFunction_two`. The asymptotic constant
is $\varphi'(\alpha) \varphi''(\alpha) / (2 (\varphi'(\alpha) - 1))$, by
`tendsto_aitkenIterationFunction_sub_div_sq`. -/
theorem property_6_7_one (hφ : ContDiffAt ℝ 2 φ α) (hα : φ α = α) (h1 : deriv φ α ≠ 1) :
    ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (fun k => (equation_6_38 φ)^[k] x₀) α 2 := by
  obtain ⟨ε, hε, h⟩ := hasIterationOrder_aitkenIterationFunction_two hφ hα h1
  exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder one_le_two (h x₀ hx₀)⟩

/-- **Property 6.7** of [quarteroni2000numerical], the case $p \ge 2$. Let $p \ge 2$, let $\alpha$
be a fixed point of $\varphi : \mathbb{R} \to \mathbb{R}$, let $\varphi$ be of class $C^p$ on a
neighbourhood of $\alpha$, and let $\varphi^{(i)}(\alpha) = 0$ for $1 \le i < p$ and
$\varphi^{(p)}(\alpha) \neq 0$, so that the iteration of $\varphi$ has order $p$ by Property
6.4. Then there is $\varepsilon > 0$ such that for every $x^{(0)}$ with
$|x^{(0)} - \alpha| < \varepsilon$ the iterates of Aitken's method converge to $\alpha$ with
order $2p - 1$ in the sense of Definition 6.1.

**Generalization.** The source assumes $\varphi \in C^{2p}$ on a neighbourhood of $\alpha$;
$\varphi \in C^p$ is enough.

The source states this case without proof, after Isaacson and Keller. The proof specializes
`hasIterationOrder_aitkenIterationFunction_of_iteratedDeriv_eq_zero`. -/
theorem property_6_7_higher {p : ℕ} (hp : 2 ≤ p) (hφ : ContDiffAt ℝ p φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i < p → iteratedDeriv i φ α = 0) (hp' : iteratedDeriv p φ α ≠ 0) :
    ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε,
      definition_6_1 (fun k => (equation_6_38 φ)^[k] x₀) α (2 * p - 1) := by
  obtain ⟨ε, hε, h⟩ :=
    hasIterationOrder_aitkenIterationFunction_of_iteratedDeriv_eq_zero hp hφ hα hzero hp'
  refine ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder ?_ (h x₀ hx₀)⟩
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

end Aitken

/-! ### Exercise 6.5: Steffensen's method, and the last clause of Property 6.7 -/

section Steffensen

variable {f : ℝ → ℝ} {α : ℝ}

/-- **Exercise 6.5** of [quarteroni2000numerical], **Steffensen's method**:
$$x^{(k+1)} = x^{(k)} - \frac{f(x^{(k)})}{\phi(x^{(k)})}, \qquad \phi(x) = \frac{f(x + f(x)) -
  f(x)}{f(x)}.$$

The value at $k$ is the $k$-th iterate of the backbone's `steffensenStep` from $x^{(0)}$. Where
$f(x) = 0$ the step returns $x$, because division by $0$ gives $0$ in Lean. -/
noncomputable def steffensen (f : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) : ℝ := (steffensenStep f)^[k] x₀

/-- **Exercise 6.5** of [quarteroni2000numerical]. Let $f(\alpha) = 0$, let $f$ be of class $C^2$ on
a neighbourhood of $\alpha$, and let $f'(\alpha) \neq 0$. Then there is $\varepsilon > 0$ such
that for every $x^{(0)}$ with $|x^{(0)} - \alpha| < \varepsilon$ the iterates of Steffensen's
method converge to $\alpha$ with order $2$ in the sense of Definition 6.1.

Steffensen's method is Aitken's method for the iteration function $x + f(x)$, by
`steffensenStep_eq_aitkenIterationFunction`. The proof specializes
`hasIterationOrder_steffensenStep_two`. -/
theorem exercise_6_5 (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α) (hf' : deriv f α ≠ 0) :
    ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (steffensen f x₀) α 2 := by
  obtain ⟨ε, hε, h⟩ := hasIterationOrder_steffensenStep_two hα hf hf'
  exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder one_le_two (h x₀ hx₀)⟩

/-- **Property 6.7** of [quarteroni2000numerical], the last clause. Let $m \ge 2$, let $f$ be of
class $C^{m+1}$ on a neighbourhood of $\alpha$, and let $\alpha$ be a root of $f$ of
multiplicity $m$. Let $\psi$ be the step of Steffensen's method. Then
$$\lim_{x \to \alpha,\ x \neq \alpha} \frac{\psi(x) - \alpha}{x - \alpha} = 1 - \frac{1}{m},$$
and for every $x^{(0)}$ whose Steffensen iterates converge to $\alpha$ and satisfy
$x^{(k)} \neq \alpha$ for all $k$,
$$\lim_{k \to \infty} \frac{x^{(k+1)} - \alpha}{x^{(k)} - \alpha} = 1 - \frac{1}{m}.$$

**Correction.** The source says: "if $\alpha$ has multiplicity $m \ge 2$ and the method is
first-order convergent, then Aitken's method converges linearly with factor $C = 1 - 1/m$". This
is false as printed: for every $\varphi$ differentiable at $\alpha$ with
$\varphi'(\alpha) \neq 1$, $\varphi_\Delta'(\alpha) = 0$ by
`QuarteroniSaccoSaleri.Chapter06.equation_6_38_fixedPoints`, so Aitken's method converges
superlinearly. The statement of Isaacson and Keller that the source paraphrases concerns the
iteration function $\varphi(x) = x + f(x)$, whose derivative at a multiple root is $1$. Aitken's
method for this $\varphi$ is Steffensen's method, and the statement here is the one for
Steffensen's method.

The step $\psi$ is `steffensenStep f`. The proof specializes
`tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity`. -/
theorem property_6_7_multiple {m : ℕ} (hm : 2 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (steffensenStep f x - α) / (x - α)) (𝓝[≠] α) (𝓝 (1 - 1 / m)) ∧
      ∀ x₀, (∀ k, steffensen f x₀ k ≠ α) → Tendsto (steffensen f x₀) atTop (𝓝 α) →
        Tendsto (fun k => (steffensen f x₀ (k + 1) - α) / (steffensen f x₀ k - α)) atTop
          (𝓝 (1 - 1 / m)) := by
  have h := tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity hm hf hα
  refine ⟨h, fun x₀ hne hlim => ?_⟩
  have := h.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
  refine this.congr fun k => ?_
  simp [Function.comp, steffensen, Function.iterate_succ_apply']

end Steffensen

/-! ### Section 6.6.2: Techniques for multiple roots -/

section MultipleRoots

variable {f : ℝ → ℝ} {α : ℝ}

/-- **Equation (6.40)** of [quarteroni2000numerical], the **multiplicity estimate**
$$m^{(k)} = \frac{1}{1 - \lambda^{(k)}},$$
with $\lambda^{(k)}$ the increment ratio (6.33) of a real sequence $x^{(k)}$.

If $\lambda^{(k)} = 1$, the value is $0$, because division by $0$ gives $0$ in Lean. -/
noncomputable def equation_6_40 (x : ℕ → ℝ) (k : ℕ) : ℝ := 1 / (1 - equation_6_33 x k)

/-- The multiplicity estimate (6.40) at $k + 2$ is the backbone's `Newton.multiplicityEstimate` at
$k$. -/
theorem equation_6_40_eq (x : ℕ → ℝ) (k : ℕ) :
    equation_6_40 x (k + 2) = Newton.multiplicityEstimate x k := by
  rw [equation_6_40, Newton.multiplicityEstimate, equation_6_33_eq]

/-- **Equation (6.40)** of [quarteroni2000numerical], the second form. Let $x^{(k)}$ be a real
sequence, let $k \ge 2$, and let $x^{(k-1)} - x^{(k-2)} \neq 0$. Then
$$m^{(k)} = \frac{x^{(k-1)} - x^{(k-2)}}{2 x^{(k-1)} - x^{(k)} - x^{(k-2)}}.$$

The proof specializes `Newton.multiplicityEstimate_eq`. -/
theorem equation_6_40_eq_div (x : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) (h : x (k - 1) - x (k - 2) ≠ 0) :
    equation_6_40 x k = (x (k - 1) - x (k - 2)) / (2 * x (k - 1) - x k - x (k - 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [equation_6_40_eq, Newton.multiplicityEstimate_eq x j (by simpa using h)]
  simp

/-- **Section 6.6.2** of [quarteroni2000numerical], "$m^{(k)}$ tends to $m$ as $k \to \infty$". Let
$m \ge 1$, let $f$ be of class $C^{m+1}$ on a neighbourhood of $\alpha$, and let $\alpha$ be a
root of $f$ of multiplicity $m$. Let $x^{(k+1)} = x^{(k)} - f(x^{(k)}) / f'(x^{(k)})$ for all
$k$, with $x^{(k)} \to \alpha$ and $x^{(k)} \neq \alpha$ for all $k$. Then the estimates (6.40)
satisfy
$$\lim_{k \to \infty} m^{(k)} = m.$$

The limit follows from (6.34), since $\varphi_{\mathrm{Newt}}'(\alpha) = 1 - 1/m$ by (6.22). The
proof specializes `Newton.tendsto_multiplicityEstimate`. -/
theorem equation_6_40_tendsto {m : ℕ} (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) {x : ℕ → ℝ}
    (hx : ∀ k, x (k + 1) = Newton.scalarStep f (deriv f) (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) : Tendsto (equation_6_40 x) atTop (𝓝 m) := by
  rw [← tendsto_add_atTop_iff_nat 2]
  exact (Newton.tendsto_multiplicityEstimate hm hf hα hx hne hlim).congr
    fun k => (equation_6_40_eq x k).symm

/-- **Equation (6.39)** of [quarteroni2000numerical], the **adaptive Newton method**
$$x^{(k+1)} = x^{(k)} - m^{(k)} \frac{f(x^{(k)})}{f'(x^{(k)})}, \qquad m^{(k)} =
  \frac{x^{(k-1)} - x^{(k-2)}}{2 x^{(k-1)} - x^{(k)} - x^{(k-2)}},$$
with $m^{(k)}$ the estimate (6.40) from the last three iterates $x^{(k-2)}, x^{(k-1)}, x^{(k)}$.
It starts from three iterates $x_0, x_1, x_2$, which Program 56 produces by two steps of
Newton's method.

The value at $k$ is the last component of the $k$-th iterate of the backbone's
`Newton.adaptiveStep` on triples, from $(x_0, x_1, x_2)$; so the value at $0$ is $x_2$. Where
the denominator of $m^{(k)}$ vanishes, $m^{(k)} = 0$, because division by $0$ gives $0$ in Lean;
Program 56 instead keeps the previous estimate. This is a definition only: the source proves
nothing about the adaptive method. -/
noncomputable def equation_6_39 (f f' : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) (k : ℕ) : ℝ :=
  ((Newton.adaptiveStep f f')^[k] (x₀, x₁, x₂)).2.2

end MultipleRoots

end QuarteroniSaccoSaleri.Chapter06
