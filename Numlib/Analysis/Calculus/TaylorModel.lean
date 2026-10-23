import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Finite Taylor models from derivative tensors

`TaylorModel.ofJet` evaluates a finite jet using Mathlib's formal multilinear series partial
sum. It applies to approximate derivative tensors as well as exact derivatives.
`TaylorModel.eval` specializes the coefficients to the iterated Fréchet derivatives of a map.
The codomain may be any real normed space, including the residual space of a composite model.
-/

namespace TaylorModel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The degree-`p` polynomial specified by the derivative tensors `A`, including the constant
coefficient. Each tensor is divided by the factorial of its order. -/
noncomputable def ofJet (A : FormalMultilinearSeries ℝ E F) (p : ℕ) (s : E) : F :=
  FormalMultilinearSeries.partialSum (fun i => ((i.factorial : ℝ)⁻¹) • A i) (p + 1) s

/-- Finite sum characterization of a polynomial specified by a derivative jet. -/
theorem ofJet_eq_sum (A : FormalMultilinearSeries ℝ E F) (p : ℕ) (s : E) :
    ofJet A p s = ∑ i ∈ Finset.range (p + 1),
      ((i.factorial : ℝ)⁻¹) • A i (fun _ => s) := by
  simp only [ofJet, FormalMultilinearSeries.partialSum,
    smul_apply]

/-- At zero only the constant tensor contributes to a finite jet polynomial. -/
@[simp] theorem ofJet_zero (A : FormalMultilinearSeries ℝ E F) (p : ℕ) :
    ofJet A p 0 = A 0 (fun _ => 0) := by
  rw [ofJet_eq_sum, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    have hz : A i (fun _ => (0 : E)) = 0 :=
      (A i).map_coord_zero ⟨0, Nat.pos_of_ne_zero hi⟩ rfl
    rw [hz, smul_zero]
  · simp

/-- The Taylor model of degree `p` at `x`, evaluated at displacement `s`. -/
noncomputable def eval (f : E → F) (p : ℕ) (x s : E) : F :=
  ofJet (ftaylorSeries ℝ f x) p s

/-- Finite sum characterization of the Taylor model. -/
theorem eval_eq_sum (f : E → F) (p : ℕ) (x s : E) :
    eval f p x s = ∑ i ∈ Finset.range (p + 1),
      ((i.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ i f x (fun _ => s) :=
  ofJet_eq_sum _ _ _

/-- A Taylor model agrees with the function at zero displacement. -/
@[simp] theorem eval_zero (f : E → F) (p : ℕ) (x : E) : eval f p x 0 = f x := by
  simp [eval, ftaylorSeries]

/-- The decrease of the degree-`p` Taylor model relative to zero displacement. -/
noncomputable def decrement (f : E → ℝ) (p : ℕ) (x s : E) : ℝ :=
  eval f p x 0 - eval f p x s

/-- Subtraction of the constant coefficient gives the usual Taylor decrement. -/
theorem decrement_eq (f : E → ℝ) (p : ℕ) (x s : E) :
    decrement f p x s = f x - eval f p x s := by
  simp [decrement]

@[simp] theorem decrement_zero (f : E → ℝ) (p : ℕ) (x : E) :
    decrement f p x 0 = 0 := by
  simp [decrement]

end TaylorModel
