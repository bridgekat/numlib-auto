import Numlib.Analysis.Calculus.IteratedFDerivSymmetry
import Numlib.Analysis.InnerProductSpace.SymmetricMultilinear

/-!
# Norms of symmetric derivative tensors

Finite smoothness makes actual iterated derivatives invariant under permutations. For scalar
maps on finite-dimensional real inner product spaces, their diagonal norms and the diagonal
norms of their differences therefore equal the genuine multilinear operator norms.
-/

namespace ContDiffAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ} {f : E → F} {x : E}

/-- The actual highest derivative of a finitely smooth map is a symmetric multilinear map. -/
theorem isSymmetric_iteratedFDeriv (hf : ContDiffAt ℝ p f x) :
    (iteratedFDeriv ℝ p f x).IsSymmetric :=
  hf.iteratedFDeriv_comp_perm_of_nat

end ContDiffAt

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {p : ℕ} {f g : E → ℝ} {x y : E}

/-- Banach's equality for an actual positive-order derivative of a finitely smooth scalar map. -/
theorem ContDiffAt.diagonalNorm_iteratedFDeriv_eq_norm (hf : ContDiffAt ℝ p f x) (hp : 0 < p) :
    (iteratedFDeriv ℝ p f x).diagonalNorm = ‖iteratedFDeriv ℝ p f x‖ :=
  ContinuousMultilinearMap.diagonalNorm_eq_norm_of_isSymmetric _ hp
    hf.isSymmetric_iteratedFDeriv

/-- The difference of actual symmetric derivatives has the same diagonal and operator norms. -/
theorem diagonalNorm_iteratedFDeriv_sub_eq_norm (hf : ContDiffAt ℝ p f x)
    (hg : ContDiffAt ℝ p g y) (hp : 0 < p) :
    (iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p g y).diagonalNorm =
      ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p g y‖ := by
  apply ContinuousMultilinearMap.diagonalNorm_eq_norm_of_isSymmetric _ hp
  intro σ v
  change iteratedFDeriv ℝ p f x (v ∘ σ) - iteratedFDeriv ℝ p g y (v ∘ σ) = _
  rw [hf.iteratedFDeriv_comp_perm_of_nat, hg.iteratedFDeriv_comp_perm_of_nat]
  rfl

end Inner
