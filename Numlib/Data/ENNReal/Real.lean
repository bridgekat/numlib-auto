/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Basic.ENNReal.Real`, beside `ENNReal.toReal_mono`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Basic.ENNReal.Real

/-!
# The real value of a finite exponent

An exponent of the $L^p$ theory is an extended nonnegative real number $p \in [0, \infty]$. This
module proves that a finite exponent with $1 \le p$ has real value at least $1$: if $1 \le p$ and
$p \neq \infty$, then $1 \le \operatorname{toReal}(p)$, where
$\operatorname{toReal}(p) \in \mathbb{R}$ is the Lean term `ENNReal.toReal p`.

## Main results

* `ENNReal.one_le_toReal_of_ne_top`: if $1 \le p$ and $p \neq \infty$, then
  $1 \le \operatorname{toReal}(p)$.

## Implementation notes

* The hypothesis $1 \le p$ is an instance argument `Fact (1 ≤ p)`, the form in which the $L^p$ API
  of Mathlib takes it.
-/

open scoped ENNReal

/-- Let $p \in [0, \infty]$ satisfy $1 \le p$ and $p \neq \infty$. Then the real value of $p$ is at
least $1$: $$1 \le \operatorname{toReal}(p).$$

The real value $\operatorname{toReal}(p)$ is `ENNReal.toReal p`. The hypothesis $1 \le p$ is the
instance argument `Fact (1 ≤ p)`. -/
theorem ENNReal.one_le_toReal_of_ne_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    1 ≤ p.toReal := by
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono hp Fact.out
