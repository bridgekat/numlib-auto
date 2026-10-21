import Numlib.Optimization.PartiallySeparable
import Numlib.Analysis.Matrix.ToEuclideanLin
import NumlibSurface.CartisGouldToint.Chapter01.Section03

/-!
# Chapter 5, Section 2: partially separable problems

The element dimensions may differ. The finite objective and its actual Taylor polynomial
retain the same restrictions, with invariance along each restriction's kernel.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section02

variable {n m : ℕ} (ni : Fin m → ℕ)
  (U : ∀ i, Matrix (Fin (ni i)) (Fin n) ℝ)
  (f : ∀ i, EuclideanSpace ℝ (Fin (ni i)) → ℝ)

/-- The finite element objective (5.2.1). Low element dimension is useful but not required
for the exact representation or its derivative identities. -/
def partiallySeparableObjective (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Optimization.PartiallySeparable.objective
    (fun i => (Matrix.toEuclideanLin (U i)).toContinuousLinearMap) f x

/-- The objective evaluates as the displayed sum over element restrictions. -/
@[simp] theorem partiallySeparableObjective_apply (x : EuclideanSpace ℝ (Fin n)) :
    partiallySeparableObjective ni U f x = ∑ i, f i (Matrix.toEuclideanLin (U i) x) := rfl

/-- Each element function is invariant along its matrix restriction kernel. -/
theorem element_add_of_mem_ker (i : Fin m) (x v : EuclideanSpace ℝ (Fin n))
    (hv : Matrix.toEuclideanLin (U i) v = 0) :
    f i (Matrix.toEuclideanLin (U i) (x + v)) = f i (Matrix.toEuclideanLin (U i) x) :=
  Optimization.PartiallySeparable.element_add_of_mem_ker
    (Matrix.toEuclideanLin (U i)).toContinuousLinearMap (f i) x v hv

/-- The source Taylor model decomposes exactly as (5.2.2). -/
theorem taylorModel_partiallySeparableObjective {p : ℕ}
    (hf : ∀ i, ContDiff ℝ p (f i)) (x s : EuclideanSpace ℝ (Fin n)) :
    Chapter01.Section03.taylorModel (partiallySeparableObjective ni U f) p x s =
      ∑ i, Chapter01.Section03.taylorModel (f i) p
        (Matrix.toEuclideanLin (U i) x) (Matrix.toEuclideanLin (U i) s) :=
  Optimization.PartiallySeparable.taylorModel_objective
    (fun i => (Matrix.toEuclideanLin (U i)).toContinuousLinearMap) f hf x s

end CartisGouldToint.Chapter05.Section02
