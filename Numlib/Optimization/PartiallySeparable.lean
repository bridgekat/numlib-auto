import Numlib.Optimization.RegularizedTaylorModel
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Finite sums through linear restrictions

Element functions may live on different normed spaces. Their Taylor polynomials inherit the
same finite-sum structure, and each element is invariant along its restriction kernel.
-/

noncomputable section
namespace Optimization.PartiallySeparable

variable {ι E G : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]

/-- A finite sum of element functions evaluated on their own linear restrictions. -/
def objective {Y : Type*} [AddCommMonoid Y]
    (U : ∀ i, E →L[ℝ] F i) (f : ∀ i, F i → Y) (x : E) : Y :=
  ∑ i, f i (U i x)

/-- The finite element representation is its defining evaluation rule. -/
@[simp] theorem objective_apply {Y : Type*} [AddCommMonoid Y]
    (U : ∀ i, E →L[ℝ] F i) (f : ∀ i, F i → Y) (x : E) :
    objective U f x = ∑ i, f i (U i x) := rfl

/-- An element does not change when its argument moves along the restriction kernel. -/
theorem element_add_of_mem_ker {Y : Type*} (U : E →L[ℝ] G) (f : G → Y) (x v : E)
    (hv : v ∈ LinearMap.ker U.toLinearMap) : f (U (x + v)) = f (U x) := by
  rw [map_add, show U v = 0 from hv, add_zero]

/-- The actual derivative tensors decompose as pulled-back element tensors. -/
theorem iteratedFDeriv_objective (U : ∀ i, E →L[ℝ] F i) (f : ∀ i, F i → G)
    {p j : ℕ} (hf : ∀ i, ContDiff ℝ p (f i)) (hj : j ≤ p) (x : E) :
    iteratedFDeriv ℝ j (objective U f) x =
      ∑ i, (iteratedFDeriv ℝ j (f i) (U i x)).compContinuousLinearMap (fun _ => U i) := by
  change iteratedFDeriv ℝ j (fun y => ∑ i, f i (U i y)) x = _
  rw [iteratedFDeriv_fun_sum_apply (f := fun i y => f i (U i y))
    (u := Finset.univ) (n := j) (x := x) (fun i _ =>
      (((hf i).of_le (by exact_mod_cast hj)).comp (U i).contDiff).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  exact (U i).iteratedFDeriv_comp_right (hf i) x (by exact_mod_cast hj)

/-- Taylor modeling commutes with finite partial separability. -/
theorem taylorModel_objective (U : ∀ i, E →L[ℝ] F i) (f : ∀ i, F i → G)
    {p : ℕ} (hf : ∀ i, ContDiff ℝ p (f i)) (x s : E) :
    RegularizedTaylorModel.taylorModel (objective U f) p x s =
      ∑ i, RegularizedTaylorModel.taylorModel (f i) p (U i x) (U i s) := by
  unfold RegularizedTaylorModel.taylorModel
  calc
    _ = ∑ j ∈ Finset.range (p + 1), (j.factorial : ℝ)⁻¹ •
        (∑ i, (iteratedFDeriv ℝ j (f i) (U i x)).compContinuousLinearMap
          (fun _ => U i)) (fun _ => s) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjp : j ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [iteratedFDeriv_objective U f hf hjp]
    _ = _ := by
      simp only [sum_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply, Finset.smul_sum]
      rw [Finset.sum_comm]

end Optimization.PartiallySeparable
