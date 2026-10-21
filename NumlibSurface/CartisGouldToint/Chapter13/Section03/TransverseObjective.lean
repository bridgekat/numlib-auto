import NumlibSurface.CartisGouldToint.Chapter02.Section01
import NumlibSurface.CartisGouldToint.Chapter13.Section01
import Numlib.Optimization.TransverseObjective

/-!
# Global source hypotheses for the transverse objective

The fixed positive objective satisfies the actual source smoothness assumption,
including Lipschitz values and full derivative tensors through order two.
No execution, termination, or complexity assertion is made here.
-/

namespace CartisGouldToint.Chapter13.Section03.ARqpEDATransverse
open Optimization.TransverseObjective

/-- The fixed objective satisfies f.D0pL for degree two with a common constant four. -/
theorem smoothness : Section01.ImplicitSmoothness objective 2 := by
  refine ⟨contDiff_objective, ?_⟩
  intro i hi
  refine ⟨4, by norm_num, ?_⟩
  intro x y
  simpa [dist_eq_norm] using (lipschitz_jets i hi).dist_le_mul x y

/-- Zero is a global source lower bound for the actual objective. -/
theorem boundedBelow : Chapter02.Section01.assumption_f_Bb objective := by
  rw [Chapter02.Section01.assumption_f_Bb_iff]
  exact ⟨0, objective_nonneg⟩

end CartisGouldToint.Chapter13.Section03.ARqpEDATransverse
