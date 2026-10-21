import Numlib.Optimization.ExplicitTrustRegion

/-!
# Exact certified value and derivative oracles

An exact objective oracle satisfies the known unit absolute-error interface for every
point and every positive request. No smoothness hypothesis is needed to define its
actual Fréchet derivative tensors.
-/

noncomputable section
namespace Optimization.ExplicitTrustRegion.Oracle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Return the exact objective value and every actual derivative tensor, independently
of all requested accuracies. -/
def exact (f : E → ℝ) (q : ℕ) : Oracle f q where
  value x _ := f x
  derivative x _ i := iteratedFDeriv ℝ i f x
  value_accuracy _ _ hh := by simpa using hh.le
  derivative_accuracy _ _ hh _ hi := by simpa using (hh _ hi).le

/-- The exact value oracle returns the actual objective for any accuracy request. -/
@[simp] theorem exact_value (f : E → ℝ) (q : ℕ) (x : E) (h : ℝ) :
    (exact f q).value x h = f x := rfl

/-- The exact derivative oracle returns every actual tensor for any request vector. -/
@[simp] theorem exact_derivative (f : E → ℝ) (q : ℕ) (x : E) (h : ℕ → ℝ) (i : ℕ) :
    (exact f q).derivative x h i = iteratedFDeriv ℝ i f x := rfl

end Optimization.ExplicitTrustRegion.Oracle
