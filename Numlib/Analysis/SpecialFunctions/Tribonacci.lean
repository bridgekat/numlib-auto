/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.NumberTheory.Real.Tribonacci`, beside
`Mathlib.NumberTheory.Real.GoldenRatio`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# The tribonacci constant

The **tribonacci constant** $T \approx 1.8393$ is the real root of $x^3 = x^2 + x + 1$. It is the
growth rate of the tribonacci numbers, which satisfy $T_{n+3} = T_{n+2} + T_{n+1} + T_n$, in the
same way as the golden ratio `Real.goldenRatio` is the growth rate of the Fibonacci numbers. It is
the order of convergence of Muller's method (`Numlib.Nonlinear.Secant`; [quarteroni2000numerical],
§6.4.3, which prints it as $p \simeq 1.84$), as the golden ratio is the order of the secant method.

This file defines $T$ by the intermediate value theorem on $[1, 2]$, and proves that
$T^3 = T^2 + T + 1$, that $1.83 < T < 1.84$, and that $T$ is the only root of the cubic in
$[1, \infty)$.

## Main definitions

* `Real.tribonacci`: the tribonacci constant $T$.

## Main results

* `Real.tribonacci_pow_three`: $T^3 = T^2 + T + 1$.
* `Real.one_lt_tribonacci`, `Real.tribonacci_lt_two`: $1 < T < 2$.
* `Real.tribonacci_le_iff`: for $x \ge 1$, $T \le x$ if and only if $x^3 - x^2 - x - 1 \ge 0$.
* `Real.tribonacci_unique`: $T$ is the only real root of $x^3 = x^2 + x + 1$ with $x \ge 1$.
* `Real.lt_tribonacci_1_83`, `Real.tribonacci_lt_1_84`: $1.83 < T < 1.84$.

## Implementation notes

* Mathlib has the golden ratio but not the tribonacci constant.
* The constant is defined by the intermediate value theorem and not by a closed form. Cardano's
  expression $T = \bigl(1 + \sqrt[3]{19 + 3\sqrt{33}} + \sqrt[3]{19 - 3\sqrt{33}}\bigr)/3$ is of no
  use in computations with $T$.
* Users need only the cubic `Real.tribonacci_pow_three` and the bounds `Real.one_lt_tribonacci` and
  `Real.tribonacci_lt_two`. `Real.tribonacci_le_iff` turns any numerical comparison with $T$ into
  one `norm_num` call on the cubic.
-/

open Set

namespace Real

/-- The function $x \mapsto x^3 - x^2 - x - 1$ is strictly increasing on $[1, \infty)$.

For $1 \le a < b$, the increment is $(b - a)(a^2 + ab + b^2 - a - b - 1)$, and $a^2 + ab + b^2 -
a - b - 1 = b(b - 1) + a(b - 1) + (a^2 - 1)$ is positive. -/
theorem strictMonoOn_cubic_sub : StrictMonoOn (fun x : ℝ => x ^ 3 - x ^ 2 - x - 1) (Ici 1) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  change a ^ 3 - a ^ 2 - a - 1 < b ^ 3 - b ^ 2 - b - 1
  have key : 0 < a ^ 2 + a * b + b ^ 2 - a - b - 1 := by nlinarith
  nlinarith [mul_pos (sub_pos.2 hab) key]

/-- The cubic $x^3 - x^2 - x - 1$ has a root in $[1, 2]$, because it takes the value $-2$ at $1$ and
the value $1$ at $2$. -/
theorem exists_root_cubic_sub : ∃ x : ℝ, x ∈ Icc (1 : ℝ) 2 ∧ x ^ 3 - x ^ 2 - x - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - x - 1) (Icc 1 2) := by fun_prop
  have h := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont
  have hmem : (0 : ℝ) ∈ Icc ((1 : ℝ) ^ 3 - 1 ^ 2 - 1 - 1) ((2 : ℝ) ^ 3 - 2 ^ 2 - 2 - 1) := by
    norm_num
  obtain ⟨x, hx, hx0⟩ := h hmem
  exact ⟨x, hx, hx0⟩

/-- The **tribonacci constant** $T \approx 1.8393$: a real root in $[1, 2]$ of the cubic
$x^3 = x^2 + x + 1$. It is the analogue for the tribonacci numbers
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$ of `Real.goldenRatio` for the Fibonacci numbers, and the
order of convergence of Muller's method ([quarteroni2000numerical], §6.4.3).

The root is chosen by the intermediate value theorem on $[1, 2]$. `Real.tribonacci_unique` shows
that the choice is forced. -/
noncomputable def tribonacci : ℝ := exists_root_cubic_sub.choose

/-- The tribonacci constant lies in $[1, 2]$. -/
theorem tribonacci_mem_Icc : tribonacci ∈ Icc (1 : ℝ) 2 := exists_root_cubic_sub.choose_spec.1

/-- **The defining cubic** of the tribonacci constant: $T^3 = T^2 + T + 1$. -/
theorem tribonacci_pow_three : tribonacci ^ 3 = tribonacci ^ 2 + tribonacci + 1 := by
  have := exists_root_cubic_sub.choose_spec.2
  rw [tribonacci]
  linarith

/-- The tribonacci constant satisfies $1 < T$, because the cubic $x^3 - x^2 - x - 1$ is $-2$ at $1$.
-/
theorem one_lt_tribonacci : 1 < tribonacci := by
  rcases lt_or_eq_of_le tribonacci_mem_Icc.1 with h | h
  · exact h
  · exact absurd tribonacci_pow_three (by rw [← h]; norm_num)

/-- The tribonacci constant satisfies $T < 2$, because the cubic $x^3 - x^2 - x - 1$ is $1$ at $2$.
-/
theorem tribonacci_lt_two : tribonacci < 2 := by
  rcases lt_or_eq_of_le tribonacci_mem_Icc.2 with h | h
  · exact h
  · exact absurd tribonacci_pow_three (by rw [h]; norm_num)

/-- **Comparison with the tribonacci constant is evaluation of the cubic**: for $x \ge 1$,
$$T \le x \iff x^3 - x^2 - x - 1 \ge 0.$$

This is `Real.strictMonoOn_cubic_sub` at the root $T$. -/
theorem tribonacci_le_iff {x : ℝ} (hx : 1 ≤ x) : tribonacci ≤ x ↔ 0 ≤ x ^ 3 - x ^ 2 - x - 1 := by
  rw [← strictMonoOn_cubic_sub.le_iff_le (mem_Ici.2 one_lt_tribonacci.le) (mem_Ici.2 hx)]
  constructor
  · intro h; linarith [tribonacci_pow_three]
  · intro h; linarith [tribonacci_pow_three]

/-- **The tribonacci constant is the only root of the cubic in $[1, \infty)$**: if $x \ge 1$ and
$x^3 = x^2 + x + 1$, then $x = T$. -/
theorem tribonacci_unique {x : ℝ} (hx : 1 ≤ x) (h : x ^ 3 = x ^ 2 + x + 1) : x = tribonacci := by
  refine le_antisymm ?_ ((tribonacci_le_iff hx).2 (by linarith))
  by_contra hlt
  push Not at hlt
  have := strictMonoOn_cubic_sub (mem_Ici.2 one_lt_tribonacci.le) (mem_Ici.2 hx) hlt
  simp only at this
  linarith [tribonacci_pow_three]

/-- The tribonacci constant satisfies $T < 1.84$. This is the value that [quarteroni2000numerical],
§6.4.3, prints as $p \simeq 1.84$. -/
theorem tribonacci_lt_1_84 : tribonacci < 1.84 := by
  refine lt_of_le_of_ne ((tribonacci_le_iff (by norm_num)).2 (by norm_num)) fun h => ?_
  have h3 := tribonacci_pow_three
  rw [h] at h3
  norm_num at h3

/-- The tribonacci constant satisfies $1.83 < T$. -/
theorem lt_tribonacci_1_83 : 1.83 < tribonacci :=
  not_le.1 fun h => by have := (tribonacci_le_iff (by norm_num)).1 h; norm_num at this

end Real
