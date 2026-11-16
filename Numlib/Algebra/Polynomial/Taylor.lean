/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Polynomial.Taylor`, beside `Polynomial.taylor_apply`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Taylor expansion of a rescaled polynomial

Let $q$ be a polynomial over a commutative semiring, and let $s, l$ be scalars. The Taylor expansion
of $q(sX)$ about $l$ is the Taylor expansion of $q$ about $sl$, rescaled by $X \mapsto sX$. This is
the coefficient identity behind the rescaling $f(sa)$ of the primary functional calculus.

## Main results

* `Polynomial.taylor_comp_C_mul_X`: the Taylor expansion of $q(sX)$ about $l$ is the Taylor
  expansion of $q$ about $sl$, evaluated at $sX$.
-/

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- **Taylor expansion of a rescaled polynomial**. Let $R$ be a commutative semiring, let
$q \in R[X]$ and $s, l \in R$. Then the Taylor expansion of $q(sX)$ about $l$ is the Taylor
expansion of $q$ about $sl$, with $X$ replaced by $sX$:
$$q\bigl(s(X + l)\bigr) = \bigl(q(X + sl)\bigr)\big|_{X = sX}.$$

The Taylor expansion of $p$ about $l$ is `Polynomial.taylor l p`, the polynomial $p(X + l)$. -/
theorem taylor_comp_C_mul_X (q : R[X]) (s l : R) :
    taylor l (q.comp (C s * X)) = (taylor (s * l) q).comp (C s * X) := by
  simp only [taylor_apply, comp_assoc, mul_comp, C_comp, X_comp, add_comp]
  congr 1
  rw [map_mul]
  ring

end Polynomial
