/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Nonlinear.Bisection
import Numlib.Nonlinear.Secant
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Basics

/-!
# Quarteroni, Sacco and Saleri, Section 6.2: A geometric approach to rootfinding

This module formalizes Section 6.2 of [quarteroni2000numerical], the rootfinding methods that follow
from a geometric construction. The bisection method (Section 6.2.1) halves an interval $[a, b]$ with
$f(a) f(b) < 0$ at each step, keeping the half on which $f$ changes sign; Property 6.1 gives a root
in $(a, b)$, and after $k$ steps the midpoint is within $(b - a)/2^k$ of a root (6.8)–(6.9). The
methods of Section 6.2.2 replace $f$ by a straight line: the chord method (6.12) with the fixed
slope $(f(b) - f(a))/(b - a)$, the secant method (6.13)–(6.14) through the last two iterates, which
converges with order $(1 + \sqrt 5)/2$ (Property 6.2), the regula falsi method (6.15) through the
last iterate and the last earlier iterate of opposite sign, which converges linearly, and Newton's
method (6.16) with the tangent. Each method is defined as the book writes it and identified with its
counterpart in `Numlib.Nonlinear.Bisection`, `Numlib.Nonlinear.Secant`,
`Numlib.Nonlinear.ScalarNewton` and `Numlib.Nonlinear.Newton`. The convergence results for the chord
and Newton methods, which the source defers to Section 6.3.1, are in
`NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section03`.

## Main definitions

* Section 6.2.1, `QuarteroniSaccoSaleri.Chapter06.bisectionInterval` and
  `QuarteroniSaccoSaleri.Chapter06.bisection`: the intervals $I_k = [a^{(k)}, b^{(k)}]$ and the
  midpoints $x^{(k)}$ of the bisection method.
* Equation (6.12), `QuarteroniSaccoSaleri.Chapter06.chord`: the chord method.
* Equations (6.13)–(6.14), `QuarteroniSaccoSaleri.Chapter06.secant`: the secant method.
* Equation (6.15), `QuarteroniSaccoSaleri.Chapter06.regulaFalsi`: the regula falsi method.
* Equation (6.16), `QuarteroniSaccoSaleri.Chapter06.newton`: Newton's method.

## Main results

* Property 6.1, `QuarteroniSaccoSaleri.Chapter06.property_6_1`: a continuous $f$ on $[a, b]$ with
  $f(a) f(b) < 0$ has a zero in $(a, b)$.
* Equation (6.8), `QuarteroniSaccoSaleri.Chapter06.equation_6_8`: $|I_k| = (b - a)/2^k$, the
  intervals are nested, and $f(a^{(k)}) f(b^{(k)}) \le 0$.
* Section 6.2.1, `QuarteroniSaccoSaleri.Chapter06.bisection_tendsto`: the bisection method converges
  to a root $\alpha \in (a, b)$ with $|x^{(k)} - \alpha| \le (b - a)/2^k$.
* Equation (6.9), `QuarteroniSaccoSaleri.Chapter06.equation_6_9`:
  $|x^{(m)} - \alpha| \le \varepsilon$ as soon as $m \ge \log_2(b - a) - \log_2 \varepsilon$.
* Equation (6.12), `QuarteroniSaccoSaleri.Chapter06.chord_succ` and
  `QuarteroniSaccoSaleri.Chapter06.chord_eq_chordIterate`: the chord recurrence, and its
  identification with the Banach-space chord method.
* Equation (6.14), `QuarteroniSaccoSaleri.Chapter06.secant_succ`: the secant recurrence.
* Property 6.2, `QuarteroniSaccoSaleri.Chapter06.property_6_2`: near a simple root with
  $f''(\alpha) \neq 0$, the secant method converges with order $(1 + \sqrt 5)/2$.
* Section 6.2.2, `QuarteroniSaccoSaleri.Chapter06.regulaFalsi_mem_uIcc`: the regula falsi iterates
  stay in the starting interval.
* Section 6.2.2, `QuarteroniSaccoSaleri.Chapter06.regulaFalsi_order_one`: the regula falsi method
  converges with order $1$.
* Equation (6.16), `QuarteroniSaccoSaleri.Chapter06.newton_succ` and
  `QuarteroniSaccoSaleri.Chapter06.newton_eq_iterate`: the Newton recurrence, and its identification
  with the Banach-space Newton method.

## Deviations from the source

* **Convention.** Bisection retains the lower interval at an exact midpoint root and permits a zero
  endpoint product. See `QuarteroniSaccoSaleri.Chapter06.bisectionInterval`,
  `QuarteroniSaccoSaleri.Chapter06.bisection`, `QuarteroniSaccoSaleri.Chapter06.equation_6_8`.
* **Reading.** The iteration count gives a sufficient guarantee for the prescribed error. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_9`.
* **Convention.** Chord, secant and Newton use totalized division, and Newton accepts the derivative
  as an argument. See `QuarteroniSaccoSaleri.Chapter06.chord`,
  `QuarteroniSaccoSaleri.Chapter06.chord_succ`, `QuarteroniSaccoSaleri.Chapter06.secant`,
  `QuarteroniSaccoSaleri.Chapter06.secant_succ`, `QuarteroniSaccoSaleri.Chapter06.newton`,
  `QuarteroniSaccoSaleri.Chapter06.newton_succ`.
* **Correction.** The secant order theorem requires a simple root and distinct nearby starting
  points away from the root. See `QuarteroniSaccoSaleri.Chapter06.property_6_2`.
* **Convention.** False position retains exact roots and uses totalized division. See
  `QuarteroniSaccoSaleri.Chapter06.regulaFalsi`.
* **Specialization.** The stated false-position guarantee assumes a unique smooth simple root in a
  continuous sign bracket. See `QuarteroniSaccoSaleri.Chapter06.regulaFalsi_order_one`.
* **Bisection, Section 6.2.1** (reading). The tie $f(x^{(k)}) = 0$, which the prose leaves open,
  follows Program 46 ($b^{(k+1)} := x^{(k)}$), and the sign property is
  $f(a^{(k)}) f(b^{(k)}) \le 0$, since the source's $< 0$ fails at an exact hit. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_8`.
* **Property 6.2** (correction). The source does not list the hypothesis $f'(\alpha) \neq 0$, which
  is needed: at a multiple root the secant method converges only linearly. See
  `QuarteroniSaccoSaleri.Chapter06.property_6_2`.
* **Property 6.2** (reading). The two initial values are taken distinct and different from $\alpha$,
  since a start at $\alpha$ stops the method at once. See
  `QuarteroniSaccoSaleri.Chapter06.property_6_2`.
-/

open Filter Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

/-! ### Section 6.2.1: the bisection method -/

section Bisection

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **Property 6.1** of [quarteroni2000numerical] (theorem of zeros for continuous functions). Let
$a \le b$ and let $f$ be continuous on $[a, b]$ with $f(a) f(b) < 0$. Then $f$ has a zero
$\alpha \in (a, b)$. -/
theorem property_6_1 (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b < 0) :
    ∃ α ∈ Ioo a b, f α = 0 :=
  exists_eq_zero_Ioo_of_mul_neg hab hf h

/-- **Section 6.2.1** of [quarteroni2000numerical], the intervals of the bisection method. For
$f : \mathbb{R} \to \mathbb{R}$ and $a, b \in \mathbb{R}$, the $k$-th value is the pair of
endpoints $(a^{(k)}, b^{(k)})$ of the interval $I_k$, starting from $I_0 = [a, b]$.

This is the backbone's `Bisection.bracket`.

**Reading.** When the midpoint is an exact root, the algorithm retains the lower interval and hence
retains the root as its right endpoint. Interval width and nesting are stated with a nonpositive
endpoint product.
-/
noncomputable def bisectionInterval (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ × ℝ :=
  Bisection.bracket f a b k

/-- **Section 6.2.1** of [quarteroni2000numerical], the bisection sequence. The $k$-th iterate is
the midpoint $$x^{(k)} = \frac{a^{(k)} + b^{(k)}}{2}$$ of $I_k$, and $I_{k+1}$ is the half of
$I_k$ on which $f$ changes sign. If $f(x^{(k)}) = 0$, then $b^{(k+1)} = x^{(k)}$, as in
Program 46.

This is the backbone's `Bisection.iterate`.

**Reading.** When the midpoint is an exact root, the algorithm retains the lower interval and hence
retains the root as its right endpoint. Interval width and nesting are stated with a nonpositive
endpoint product.
-/
noncomputable def bisection (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ :=
  Bisection.iterate f a b k

/-- **Equation (6.8)** of [quarteroni2000numerical]. Let $a \le b$ and $f(a) f(b) \le 0$. Then for
every $k$, the interval $I_k$ of the bisection method has the length $$|I_k| = b^{(k)} -
a^{(k)} = \frac{b - a}{2^k},$$ the intervals are nested, $I_{k+1} \subseteq I_k$, and
$f(a^{(k)}) f(b^{(k)}) \le 0$.

**Reading.** The source states the sign property as $f(a^{(k)}) f(b^{(k)}) < 0$, which fails as
soon as an iterate is an exact root. The tie $f(x^{(k)}) = 0$ is resolved as in Program 46.

The proof specializes `Bisection.bracket_sub`, `Bisection.bracket_nested` and
`Bisection.bracket_mul_nonpos`.

**Reading.** When the midpoint is an exact root, the algorithm retains the lower interval and hence
retains the root as its right endpoint. Interval width and nesting are stated with a nonpositive
endpoint product.
-/
theorem equation_6_8 (hab : a ≤ b) (h : f a * f b ≤ 0) (k : ℕ) :
    (bisectionInterval f a b k).2 - (bisectionInterval f a b k).1 = (b - a) / 2 ^ k ∧
      Icc (bisectionInterval f a b (k + 1)).1 (bisectionInterval f a b (k + 1)).2 ⊆
        Icc (bisectionInterval f a b k).1 (bisectionInterval f a b k).2 ∧
      f (bisectionInterval f a b k).1 * f (bisectionInterval f a b k).2 ≤ 0 :=
  ⟨Bisection.bracket_sub f a b k, Bisection.bracket_nested hab k, Bisection.bracket_mul_nonpos h k⟩

/-- **Section 6.2.1** of [quarteroni2000numerical], global convergence of bisection. Let $a \le b$
and let $f$ be continuous on $[a, b]$ with $f(a) f(b) < 0$. Then there is a root
$\alpha \in (a, b)$ of $f$ such that the bisection iterates satisfy $$|e^{(k)}| = |x^{(k)} -
\alpha| \le \frac{b - a}{2^k} \quad \text{for all } k,$$ and hence $x^{(k)} \to \alpha$.

The bound is the one of the source; the backbone proves the sharper bound $(b - a)/2^{k+1}$. The
proof specializes `Bisection.exists_tendsto_iterate`, whose root lies in the open interval
because $f(a) \neq 0$ and $f(b) \neq 0$. -/
theorem bisection_tendsto (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b < 0) :
    ∃ α ∈ Ioo a b, f α = 0 ∧ (∀ k, |bisection f a b k - α| ≤ (b - a) / 2 ^ k) ∧
      Tendsto (bisection f a b) atTop (𝓝 α) := by
  obtain ⟨α, hα, hfα, hlim, -, hbound⟩ := Bisection.exists_tendsto_iterate hab hf h.le
  have hfa : f a ≠ 0 := fun h0 => by simp [h0] at h
  have hfb : f b ≠ 0 := fun h0 => by simp [h0] at h
  refine ⟨α, ⟨lt_of_le_of_ne hα.1 fun heq => hfa (heq ▸ hfα),
    lt_of_le_of_ne hα.2 fun heq => hfb (heq.symm ▸ hfα)⟩, hfα, fun k => ?_, hlim⟩
  refine (hbound k).trans ?_
  have : 0 ≤ b - a := sub_nonneg.2 hab
  rw [pow_succ, ← div_div]
  exact half_le_self (by positivity)

/-- **Equation (6.9)** of [quarteroni2000numerical], the number of iterations. Let $a \le b$ and let
$f$ be continuous on $[a, b]$ with $f(a) f(b) < 0$. Then there is a root $\alpha \in (a, b)$ of
$f$ such that for every tolerance $\varepsilon > 0$ and every $m$ with $$m \ge \log_2(b - a) -
\log_2 \varepsilon,$$ the bisection iterate satisfies $|x^{(m)} - \alpha| \le \varepsilon$.

The proof specializes `Bisection.abs_iterate_sub_le_of_le_logb`, which needs only
$\log_2((b - a)/\varepsilon) \le m + 1$.

**Reading.** The logarithmic bound is sufficient to certify the target error, which can already be
smaller at an earlier iteration.
-/
theorem equation_6_9 (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b < 0) :
    ∃ α ∈ Ioo a b, f α = 0 ∧ ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      Real.logb 2 (b - a) - Real.logb 2 ε ≤ m → |bisection f a b m - α| ≤ ε := by
  obtain ⟨α, hα, hfα, hlim, hcount⟩ := Bisection.abs_iterate_sub_le_of_le_logb hab hf h.le
  have hfa : f a ≠ 0 := fun h0 => by simp [h0] at h
  have hfb : f b ≠ 0 := fun h0 => by simp [h0] at h
  have hab' : a < b := lt_of_le_of_ne hab fun heq => by subst heq; exact hfa (by nlinarith)
  refine ⟨α, ⟨lt_of_le_of_ne hα.1 fun heq => hfa (heq ▸ hfα),
    lt_of_le_of_ne hα.2 fun heq => hfb (heq.symm ▸ hfα)⟩, hfα, fun m ε hε hm => ?_⟩
  refine hcount m ε hε ?_
  rw [Real.logb_div (sub_ne_zero.2 hab'.ne') hε.ne']
  linarith

end Bisection

/-! ### Section 6.2.2: the chord, secant, regula falsi and Newton methods -/

section Chord

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **Equation (6.12)** of [quarteroni2000numerical], the chord method. For
$f : \mathbb{R} \to \mathbb{R}$, $a, b \in \mathbb{R}$ and a starting value $x^{(0)}$, the
iterates are $$x^{(k+1)} = x^{(k)} - \frac{b - a}{f(b) - f(a)}\, f(x^{(k)}).$$

Each step is `Chord.step` with the fixed slope $q = (f(b) - f(a))/(b - a)$. If $q = 0$, the step
is the identity, by the convention that division by zero gives zero.

**Reading.** The recurrences use totalized division, so a zero denominator makes the current iterate
stationary for that step. Newton's rule takes a supplied derivative function and agrees with the
source when that function is the actual derivative.
-/
noncomputable def chord (f : ℝ → ℝ) (a b x₀ : ℝ) (k : ℕ) : ℝ :=
  (Chord.step f ((f b - f a) / (b - a)))^[k] x₀

/-- The chord method (6.12) of [quarteroni2000numerical] satisfies the recurrence of the source:
$$x^{(k+1)} = x^{(k)} - \frac{b - a}{f(b) - f(a)}\, f(x^{(k)}).$$

**Reading.** The recurrences use totalized division, so a zero denominator makes the current iterate
stationary for that step. Newton's rule takes a supplied derivative function and agrees with the
source when that function is the actual derivative.
-/
theorem chord_succ (f : ℝ → ℝ) (a b x₀ : ℝ) (k : ℕ) :
    chord f a b x₀ (k + 1) = chord f a b x₀ k - (b - a) / (f b - f a) * f (chord f a b x₀ k) := by
  rw [chord, Function.iterate_succ_apply', Chord.step, div_div_eq_mul_div, chord]
  ring

/-- Let $A : \mathbb{R} \to \mathbb{R}$ be an invertible continuous linear map with
$A(1) = (f(b) - f(a))/(b - a)$. Then the chord method (6.12) of [quarteroni2000numerical] is the
Banach-space chord method `Newton.chordIterate` with the frozen derivative $A$. -/
theorem chord_eq_chordIterate (A : ℝ ≃L[ℝ] ℝ) (hA : A 1 = (f b - f a) / (b - a)) (x₀ : ℝ)
    (k : ℕ) : chord f a b x₀ k = Newton.chordIterate f A x₀ k := by
  rw [chord, Newton.chordIterate, funext (Chord.step_eq_chordStep A hA)]

end Chord

section Secant

variable {f : ℝ → ℝ} {α : ℝ}

/-- **Equations (6.13)–(6.14)** of [quarteroni2000numerical], the secant method. From the two
initial values $x^{(-1)}$ and $x^{(0)}$, the iterates are $$x^{(k+1)} = x^{(k)} -
\frac{x^{(k)} - x^{(k-1)}}{f(x^{(k)}) - f(x^{(k-1)})}\, f(x^{(k)}),$$ where the slope $q_k$ of
(6.13) is the divided difference $f[x^{(k-1)}, x^{(k)}]$.

The arguments are `xm1`, `x₀` and `k`, for $x^{(-1)}$, $x^{(0)}$ and the iterate $x^{(k)}$. If
$f(x^{(k)}) = f(x^{(k-1)})$, the step stops at $x^{(k)}$, by the convention that division by
zero gives zero. This is the backbone's `Secant.iterate`.

**Reading.** The recurrences use totalized division, so a zero denominator makes the current iterate
stationary for that step. Newton's rule takes a supplied derivative function and agrees with the
source when that function is the actual derivative.
-/
noncomputable def secant (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) : ℝ :=
  Secant.iterate f xm1 x₀ k

/-- The secant method (6.14) of [quarteroni2000numerical] satisfies the recurrence of the source for
the iterates $x^{(k+2)}$, $k \ge 0$: $$x^{(k+2)} = x^{(k+1)} - \frac{x^{(k+1)} -
x^{(k)}}{f(x^{(k+1)}) - f(x^{(k)})}\, f(x^{(k+1)}).$$

The proof uses `Secant.iterate_add_two`. The first step, from $x^{(-1)}$ and $x^{(0)}$, is
`Secant.iterate_one`.

**Reading.** The recurrences use totalized division, so a zero denominator makes the current iterate
stationary for that step. Newton's rule takes a supplied derivative function and agrees with the
source when that function is the actual derivative.
-/
theorem secant_succ (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) :
    secant f xm1 x₀ (k + 2) = secant f xm1 x₀ (k + 1) -
      (secant f xm1 x₀ (k + 1) - secant f xm1 x₀ k) /
        (f (secant f xm1 x₀ (k + 1)) - f (secant f xm1 x₀ k)) * f (secant f xm1 x₀ (k + 1)) :=
  Secant.iterate_add_two f xm1 x₀ k

/-- **Property 6.2** of [quarteroni2000numerical]. Let $f$ be twice continuously differentiable at a
root $\alpha$, with $f'(\alpha) \neq 0$ and $f''(\alpha) \neq 0$. Then there is
$\varepsilon > 0$ such that for all initial values $x^{(-1)}, x^{(0)} \in (\alpha - \varepsilon,
\alpha + \varepsilon)$ with $x^{(-1)} \neq x^{(0)}$, $x^{(-1)} \neq \alpha$ and
$x^{(0)} \neq \alpha$, the secant sequence (6.14) converges to $\alpha$ with order $$p =
\frac{1 + \sqrt 5}{2}$$ in the sense of Definition 6.1.

**Correction.** The source does not list the hypothesis $f'(\alpha) \neq 0$. It is needed: at a
multiple root the secant method converges only linearly.

**Reading.** The source does not restrict the initial values. The theorem takes them distinct
and different from $\alpha$, since a start at $\alpha$ stops the method at once.

The source assumes $f \in C^2(J)$ on a neighbourhood $J$ of $\alpha$; the theorem needs this
smoothness only at $\alpha$, as `ContDiffAt ℝ 2 f α`. The proof specializes
`Secant.exists_ball_convergesWithOrder_goldenRatio`.

**Correction.** The local order theorem requires a simple root in addition to the nonzero second
derivative. It takes distinct starting points near the root, neither already equal to the root.
-/
theorem property_6_2 (hf : ContDiffAt ℝ 2 f α) (hα : f α = 0) (hf' : deriv f α ≠ 0)
    (hf'' : iteratedDeriv 2 f α ≠ 0) :
    ∃ ε > 0, ∀ xm1 ∈ Ioo (α - ε) (α + ε), ∀ x₀ ∈ Ioo (α - ε) (α + ε), xm1 ≠ x₀ → xm1 ≠ α →
      x₀ ≠ α → definition_6_1 (secant f xm1 x₀) α Real.goldenRatio := by
  obtain ⟨ε, hε, h⟩ := Secant.exists_ball_convergesWithOrder_goldenRatio hα hf hf' hf''
  refine ⟨ε, hε, fun xm1 hxm1 x₀ hx₀ hne h1 h2 => ?_⟩
  rw [← Real.ball_eq_Ioo] at hxm1 hx₀
  exact definition_6_1_of_convergesWithOrder Real.one_lt_goldenRatio.le
    (h xm1 hxm1 x₀ hx₀ hne h1 h2)

end Secant

section RegulaFalsi

variable {f : ℝ → ℝ} {xm1 x₀ : ℝ}

/-- **Equation (6.15)** of [quarteroni2000numerical], the regula falsi method. From a bracketing
pair of initial values $x^{(-1)}$, $x^{(0)}$, each step is the secant step through $x^{(k)}$ and
the latest earlier iterate $x^{(k')}$ with $f(x^{(k')}) f(x^{(k)}) < 0$: $$x^{(k+1)} = x^{(k)} -
\frac{x^{(k)} - x^{(k')}}{f(x^{(k)}) - f(x^{(k')})}\, f(x^{(k)}).$$

The iterate $x^{(k)}$ is the value at `k`. This is the backbone's `RegulaFalsi.iterate`.

**Reading.** A zero endpoint is retained by the implementation and division is totalized. Its
bracket state gives the preceding opposite-sign iterate on the strict-sign domain.
-/
noncomputable def regulaFalsi (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) : ℝ :=
  RegulaFalsi.iterate f xm1 x₀ k

/-- **Section 6.2.2** of [quarteroni2000numerical]: "Unlike the secant method, the iterates
generated by (6.15) are all contained within the starting interval $[x^{(-1)}, x^{(0)}]$." If
$f(x^{(0)}) f(x^{(-1)}) < 0$, then every regula falsi iterate lies in the closed interval with
the endpoints $x^{(-1)}$ and $x^{(0)}$.

The interval is `Set.uIcc`, so the endpoints can be in either order. The proof specializes
`RegulaFalsi.iterate_mem_uIcc`. -/
theorem regulaFalsi_mem_uIcc (h : f x₀ * f xm1 < 0) (k : ℕ) :
    regulaFalsi f xm1 x₀ k ∈ uIcc xm1 x₀ :=
  RegulaFalsi.iterate_mem_uIcc h k

/-- **Section 6.2.2** of [quarteroni2000numerical], the linear convergence of the regula falsi
method. Let $f$ be continuous on the closed interval with the endpoints $x^{(-1)}$ and
$x^{(0)}$, with $f(x^{(0)}) f(x^{(-1)}) < 0$. Let $\alpha$ be the only zero of $f$ in this
interval, and let $f$ be twice continuously differentiable at $\alpha$ with $f'(\alpha) \neq 0$.
Then the regula falsi iterates converge to $\alpha$ with order $1$ in the sense of Definition
6.1.

The source quotes this claim ("the Regula Falsi method … has linear convergence order") from
Ralston and Rabinowitz without proof. The theorem does not need $f''(\alpha) \neq 0$, which the
classical argument through an eventually fixed endpoint would use. The proof specializes
`RegulaFalsi.tendsto_iterate` and `RegulaFalsi.convergesWithOrder_one_iterate`.

**Reading.** The linear convergence claim assumes a continuous function, opposite endpoint signs,
and a unique simple root with local twice continuous differentiability. The order conclusion is an
upper error bound as in Definition 6.1.
-/
theorem regulaFalsi_order_one (hf : ContinuousOn f (uIcc xm1 x₀)) (h : f x₀ * f xm1 < 0) {α : ℝ}
    (huniq : ∀ y ∈ uIcc xm1 x₀, f y = 0 → y = α) (hC : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) :
    Tendsto (regulaFalsi f xm1 x₀) atTop (𝓝 α) ∧ definition_6_1 (regulaFalsi f xm1 x₀) α 1 :=
  ⟨RegulaFalsi.tendsto_iterate hf h huniq,
    definition_6_1_of_convergesWithOrder le_rfl
      (RegulaFalsi.convergesWithOrder_one_iterate hf h huniq hC hf')⟩

end RegulaFalsi

section Newton

/-- **Equation (6.16)** of [quarteroni2000numerical], Newton's method. For
$f, f' : \mathbb{R} \to \mathbb{R}$ and a starting value $x^{(0)}$, the iterates are
$$x^{(k+1)} = x^{(k)} - \frac{f(x^{(k)})}{f'(x^{(k)})}.$$

The derivative $f'$ is an argument, as the argument `dfun` of Program 50; the theorems about the
method take $f'$ = `deriv f`. Each step is the backbone's `Newton.scalarStep`. If
$f'(x^{(k)}) = 0$, the step is the identity, by the convention that division by zero gives zero.

**Reading.** The recurrences use totalized division, so a zero denominator makes the current iterate
stationary for that step. Newton's rule takes a supplied derivative function and agrees with the
source when that function is the actual derivative.
-/
noncomputable def newton (f f' : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) : ℝ :=
  (Newton.scalarStep f f')^[k] x₀

/-- Newton's method (6.16) of [quarteroni2000numerical] satisfies the recurrence of the source:
$$x^{(k+1)} = x^{(k)} - \frac{f(x^{(k)})}{f'(x^{(k)})}.$$

**Reading.** The recurrences use totalized division, so a zero denominator makes the current iterate
stationary for that step. Newton's rule takes a supplied derivative function and agrees with the
source when that function is the actual derivative.
-/
theorem newton_succ (f f' : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) :
    newton f f' x₀ (k + 1) = newton f f' x₀ k - f (newton f f' x₀ k) / f' (newton f f' x₀ k) := by
  rw [newton, Function.iterate_succ_apply']
  rfl

/-- Newton's method (6.16) of [quarteroni2000numerical] is the Banach-space Newton method
`Newton.iterate` with the derivative $x \mapsto f'(x)\, \mathrm{id}$.

The proof uses `Newton.scalarStep_eq_step`. -/
theorem newton_eq_iterate (f f' : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) :
    newton f f' x₀ k = Newton.iterate f (fun x => f' x • ContinuousLinearMap.id ℝ ℝ) x₀ k := by
  rw [newton, Newton.iterate, funext (Newton.scalarStep_eq_step f f')]

end Newton

end QuarteroniSaccoSaleri.Chapter06
