/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`, beside `deriv_comp_add_const`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The derivatives of a periodic function are periodic

Let $F$ be a real normed space, and let $f \colon \mathbb{R} \to F$ be periodic with period $T$,
that is $f(x + T) = f(x)$ for all $x$. Then the derivative $f'$ and every iterated derivative
$f^{(n)}$ are periodic with period $T$. The proof uses `deriv_comp_add_const`. Mathlib has no
periodicity lemma for `deriv`.

## Main results

* `Function.Periodic.deriv`: the derivative of a periodic function is periodic.
* `Function.Periodic.iteratedDeriv`: every iterated derivative of a periodic function is periodic.
-/

namespace Function.Periodic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let $f \colon \mathbb{R} \to F$ be periodic with period $T$. Then its derivative $f'$ is
periodic with period $T$.

The derivative is Mathlib's `deriv`, which is $0$ at points where $f$ is not differentiable, so
no differentiability is assumed. -/
theorem deriv {f : ℝ → F} {T : ℝ} (h : Function.Periodic f T) :
    Function.Periodic (_root_.deriv f) T := by
  intro x
  have hfun : (fun y => f (y + T)) = f := funext h
  have := deriv_comp_add_const f T x
  rw [hfun] at this
  exact this.symm

/-- Let $f \colon \mathbb{R} \to F$ be periodic with period $T$. Then for every $n \in \mathbb{N}$
the iterated derivative $f^{(n)}$ is periodic with period $T$. -/
theorem iteratedDeriv {f : ℝ → F} {T : ℝ} (h : Function.Periodic f T) (n : ℕ) :
    Function.Periodic (_root_.iteratedDeriv n f) T := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

end Function.Periodic
