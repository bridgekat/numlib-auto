/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Polynomial.Taylor`, beside `Polynomial.taylor_apply`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Taylor expansion of a rescaled polynomial

`Polynomial.taylor_comp_C_mul_X`: expanding `q(s X)` about `l` is expanding `q` about `s l` and
rescaling, `taylor l (q.comp (C s * X)) = (taylor (s * l) q).comp (C s * X)`. It is the
coefficient identity behind the rescaling `f(s a)` of the primary functional calculus.
-/

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- **Taylor expansion of a rescaled polynomial**: the expansion of `q(s X)` about `l` is the
expansion of `q` about `s l`, rescaled. -/
theorem taylor_comp_C_mul_X (q : R[X]) (s l : R) :
    taylor l (q.comp (C s * X)) = (taylor (s * l) q).comp (C s * X) := by
  simp only [taylor_apply, comp_assoc, mul_comp, C_comp, X_comp, add_comp]
  congr 1
  rw [map_mul]
  ring

end Polynomial
