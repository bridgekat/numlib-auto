/-
Upstreaming candidate: general material with no numerical-analysis-specific content.
Natural home: `Mathlib.Analysis.Matrix`.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Mathlib.Analysis.Matrix.PosDef

/-!
# Actual extreme eigenvalues of a Hermitian matrix

Finite infima and suprema of the actual eigenvalues give their extreme values
and exact quadratic-form bounds on the induced Euclidean operator.
-/

open scoped ComplexOrder
namespace Matrix.IsHermitian
variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)

/-- The smallest eigenvalue of a Hermitian matrix on a finite nonempty index type, defined as the
  finite infimum of its actual eigenvalues. -/
noncomputable def leastEigenvalue : ℝ := Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues
/-- The largest eigenvalue of a Hermitian matrix on a finite nonempty index type, defined as the
  finite supremum of its actual eigenvalues. -/
noncomputable def greatestEigenvalue : ℝ := Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues

/-- Every actual eigenvalue is at least the smallest eigenvalue. -/
theorem leastEigenvalue_le (i : ι) : hA.leastEigenvalue ≤ hA.eigenvalues i :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- Every actual eigenvalue is at most the largest eigenvalue. -/
theorem le_greatestEigenvalue (i : ι) : hA.eigenvalues i ≤ hA.greatestEigenvalue :=
  Finset.le_sup' _ (Finset.mem_univ i)

/-- The smallest eigenvalue does not exceed the largest eigenvalue. -/
theorem leastEigenvalue_le_greatest : hA.leastEigenvalue ≤ hA.greatestEigenvalue := by
  classical
  exact (hA.leastEigenvalue_le (Classical.arbitrary ι)).trans
    (hA.le_greatestEigenvalue (Classical.arbitrary ι))

/-- Positive definiteness makes the smallest actual eigenvalue positive. -/
theorem leastEigenvalue_pos (hpos : A.PosDef) : 0 < hA.leastEigenvalue := by
  apply (Finset.lt_inf'_iff _).mpr
  intro i hi
  exact hpos.eigenvalues_pos i

/-- The actual Hermitian Euclidean operator has its quadratic form bounded by its true smallest
  and largest eigenvalues. -/
theorem isSymmetricBoundedBy_extrema :
    (toEuclideanLin A).IsSymmetricBoundedBy hA.leastEigenvalue hA.greatestEigenvalue :=
  hA.isSymmetricBoundedBy_toEuclideanLin (fun i => ⟨hA.leastEigenvalue_le i,
    hA.le_greatestEigenvalue i⟩)

end Matrix.IsHermitian
