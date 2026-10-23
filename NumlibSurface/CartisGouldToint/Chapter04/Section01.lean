import Numlib.Analysis.Calculus.TaylorModel

/-!
# Taylor models for high-order regularization

The Taylor polynomial used in Chapter 4 and throughout the later high-order algorithms is the
finite sum of iterated Fréchet derivatives with their factorial normalization.
-/

namespace CartisGouldToint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The degree-`p` Taylor model `T_{f,p}(x,s)` of equation (4.1.1). The vector-valued form also
provides the component Taylor models used in composite optimization. -/
noncomputable def taylorModel (f : E → F) (p : ℕ) (x s : E) : F :=
  TaylorModel.eval f p x s

@[simp] theorem taylorModel_zero (f : E → F) (p : ℕ) (x : E) :
    taylorModel f p x 0 = f x := TaylorModel.eval_zero _ _ _

/-- The decrease in the Taylor model relative to zero displacement. -/
noncomputable def taylorDecrement (f : E → ℝ) (p : ℕ) (x s : E) : ℝ :=
  taylorModel f p x 0 - taylorModel f p x s

end CartisGouldToint
