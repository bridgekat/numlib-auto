import Numlib.Analysis.Calculus.IteratedDeriv.RightMinimum
import Mathlib.Tactic

/-!
# The first nonvanishing jet at a local minimum

A negative first nonzero derivative would give a negative continuous factor in
the local Taylor factorization. Positive displacements then contradict local
minimality. The argument uses only finite smoothness at the point.
-/

namespace ScalarOptimality
open Filter

/-- At a local minimum, vanishing lower positive-order derivatives force the next actual
derivative to be nonnegative. -/
theorem iteratedDeriv_nonneg_of_isLocalMin {g : ℝ → ℝ} {n : ℕ} {a : ℝ}
    (hn : 0 < n) (hg : ContDiffAt ℝ n g a) (hmin : IsLocalMin g a)
    (hzero : ∀ i, 0 < i → i < n → iteratedDeriv i g a = 0) :
    0 ≤ iteratedDeriv n g a :=
  iteratedDeriv_nonneg_of_right_min hn hg
    (hmin.filter_mono nhdsWithin_le_nhds) hzero
end ScalarOptimality
