/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Complex.Polynomial.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The complex roots of a real polynomial

`Polynomial.roots_map_algebraMap_conj`: the complex roots of a real polynomial, counted with
multiplicity, are closed under complex conjugation.
-/

namespace Polynomial

/-- **The roots of the complexification of a real polynomial are closed under conjugation**, with
multiplicities. -/
theorem roots_map_algebraMap_conj (p : ℝ[X]) :
    (p.map (algebraMap ℝ ℂ)).roots.map (starRingEnd ℂ) = (p.map (algebraMap ℝ ℂ)).roots := by
  rw [roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
    (splits_iff_card_roots.1 (IsAlgClosed.splits _)), Polynomial.map_map]
  congr 2
  exact RingHom.ext fun x => by simp

end Polynomial
