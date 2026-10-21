import Numlib.Optimization.AdaptiveInverseIteration
import Numlib.Eigen.MetricInverseBatches
import NumlibSurface.CartisGouldToint.Chapter09.Section03

/-!
# Chapter 9, Section 3: the potential hard-case inverse iteration

Algorithm 9.3.1 is an actual recursive inverse/Rayleigh computation, with every allowed
batch length, damping, and exponent choice. Energy transport proves that its inner iterations
solve the original matrix system and use the original metric normalization. The required
lowest-eigenspace component is measured in the metric inner product, as required for a
general positive definite metric. The convergence claim of Theorem 9.3.1 remains separate.
-/

noncomputable section
open scoped InnerProductSpace
open Optimization.AdaptiveInverseIteration
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter09.Section03
variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- Nonzero metric-orthogonal projection onto the complete lowest generalized eigenspace. -/
def hasLowestComponent (hH : H.IsSymm) (hM : M.PosDef)
    (z : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ i, (∀ j, secularEigenvalues hH hM i ≤ secularEigenvalues hH hM j) ∧
    ((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl).repr
      (hM.isPreconditioner_toEuclideanLin.toEnergy z) i ≠ 0

/-- The component condition exposes a lowest spectral index with a nonzero coordinate. -/
@[simp] theorem hasLowestComponent_iff (hH : H.IsSymm) (hM : M.PosDef)
    (z : EuclideanSpace ℝ (Fin n)) :
    hasLowestComponent hH hM z ↔
      ∃ i, (∀ j, secularEigenvalues hH hM i ≤ secularEigenvalues hH hM j) ∧
        ((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl).repr
          (hM.isPreconditioner_toEuclideanLin.toEnergy z) i ≠ 0 := Iff.rfl

/-- The actual metric eigenbasis coordinate is the metric inner product, not the Euclidean
inner product with the generalized eigenvector. -/
theorem lowestCoordinate_eq_metricInner (hH : H.IsSymm) (hM : M.PosDef)
    (z : EuclideanSpace ℝ (Fin n)) (i) :
    ((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl).repr
      (hM.isPreconditioner_toEuclideanLin.toEnergy z) i =
      inner ℝ (Matrix.toEuclideanLin M (secularEigenvector hH hM i)) z := by
  rw [OrthonormalBasis.repr_apply_apply]
  change inner ℝ
    (hM.isPreconditioner_toEuclideanLin.toEnergy (secularEigenvector hH hM i))
    (hM.isPreconditioner_toEuclideanLin.toEnergy z) = _
  rfl

/-- Actual outer states, transported back from the ordinary energy-space computation. -/
noncomputable def hardCaseIterate (hM : M.PosDef) (lambda : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice) (k : ℕ) :
    State (EuclideanSpace ℝ (Fin n)) :=
  let s := iterate (secularHessian H hM)
    ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c k
  ⟨s.shift, hM.isPreconditioner_toEuclideanLin.toEnergy.symm s.vector⟩

/-- Initialization preserves the given shift and vector exactly. -/
@[simp] theorem hardCaseIterate_zero (hM : M.PosDef) (lambda : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice) :
    hardCaseIterate (H := H) hM lambda z c 0 = ⟨lambda, z⟩ := by
  simp [hardCaseIterate]

/-- Algorithm 9.3.1: a legal initial greater-region shift and metric-unit estimate with a
lowest-eigenspace component, followed by the actual recursively computed inverse/Rayleigh
states. As in the existing inverse iteration, inverse and normalization are totalized;
regularity hypotheses below identify the genuine matrix solves. -/
def algorithm_9_3_1 (hH : H.IsSymm) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (target : ℝ → ℝ) (p : Parameters)
    (lambda : ℝ) (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice)
    (s : ℕ → State (EuclideanSpace ℝ (Fin n))) : Prop :=
  lambda ∈ (CartisGouldToint.Chapter08.Section03.secularRegions g H M target).2.2.1 ∧
    weightedNorm M z = 1 ∧ hasLowestComponent hH hM z ∧
    (∀ k, (c k).Legal p) ∧ s = hardCaseIterate (H := H) hM lambda z c

/-- Every source execution has exactly the explicitly generated state stream. -/
theorem algorithm_9_3_1_states {hH : H.IsSymm} {hM : M.PosDef}
    {g : EuclideanSpace ℝ (Fin n)} {target : ℝ → ℝ} {p : Parameters}
    {lambda : ℝ} {z : EuclideanSpace ℝ (Fin n)} {c : ℕ → Choice}
    {s : ℕ → State (EuclideanSpace ℝ (Fin n))}
    (h : algorithm_9_3_1 hH hM g target p lambda z c s) :
    s = hardCaseIterate (H := H) hM lambda z c := h.2.2.2.2

/-- The source state computes the requested actual metric inverse batch. -/
theorem hardCaseIterate_vector_succ (hM : M.PosDef) (lambda : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice) (k : ℕ) :
    (hardCaseIterate (H := H) hM lambda z c (k + 1)).vector =
      Krylov.metricInverseBatch hM.isPreconditioner_toEuclideanLin
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
        (hardCaseIterate (H := H) hM lambda z c k).shift
        (hardCaseIterate (H := H) hM lambda z c k).vector (c k).count := by
  simp [hardCaseIterate, iterate_succ, Krylov.metricInverseBatch]

/-- The source shift update uses the original Hessian quadratic form of the new vector. -/
theorem hardCaseIterate_shift_succ (hM : M.PosDef) (lambda : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice) (k : ℕ) :
    (hardCaseIterate (H := H) hM lambda z c (k + 1)).shift =
      let v := (hardCaseIterate (H := H) hM lambda z c (k + 1)).vector;
      let rho := inner ℝ v (Matrix.toEuclideanLin H v);
      -rho + (c k).damping * ((hardCaseIterate (H := H) hM lambda z c k).shift + rho) ^
        (c k).exponent := by
  let v := (hardCaseIterate (H := H) hM lambda z c (k + 1)).vector
  have he := Krylov.inner_energyHessian_toEnergy hM.isPreconditioner_toEuclideanLin
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) v
  change inner ℝ (hM.isPreconditioner_toEuclideanLin.toEnergy v)
    (secularHessian H hM (hM.isPreconditioner_toEuclideanLin.toEnergy v)) =
    inner ℝ v ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).toLinearMap v) at he
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at he
  simp only [v, hardCaseIterate, LinearEquiv.apply_symm_apply] at he
  simpa only [hardCaseIterate, iterate_succ, update_shift, update_vector] using
    congrArg (fun r : ℝ => -r + (c k).damping *
      ((iterate (secularHessian H hM)
        ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c k).shift + r) ^
          (c k).exponent) he

/-- Every finite regular prefix retains the source metric-unit normalization. -/
theorem hardCaseIterate_weightedNorm (hM : M.PosDef) (lambda : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice) (hz : weightedNorm M z = 1)
    (k : ℕ) (hreg : ∀ j < k, IsUnit (secularHessian H hM +
      (hardCaseIterate (H := H) hM lambda z c j).shift • 1)) :
    weightedNorm M (hardCaseIterate (H := H) hM lambda z c k).vector = 1 := by
  rw [weightedNorm_eq_energyNorm]
  change ‖hM.isPreconditioner_toEuclideanLin.toEnergy
    (hardCaseIterate (H := H) hM lambda z c k).vector‖ = 1
  simp only [hardCaseIterate, LinearEquiv.apply_symm_apply]
  apply norm_iterate_vector
  · simpa only [WithEnergy.norm_equiv, ← weightedNorm_eq_energyNorm] using hz
  · exact hreg

/-- The required component in the lowest generalized eigenspace survives every regular
finite prefix, even when the lowest eigenvalue is repeated. -/
theorem hardCaseIterate_hasLowestComponent (hH : H.IsSymm) (hM : M.PosDef)
    (lambda : ℝ) (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice)
    (hz : hasLowestComponent hH hM z) (k : ℕ)
    (hreg : ∀ j < k, ∀ i, (hardCaseIterate (H := H) hM lambda z c j).shift +
      secularEigenvalues hH hM i ≠ 0) :
    hasLowestComponent hH hM (hardCaseIterate (H := H) hM lambda z c k).vector := by
  obtain ⟨i, hi, hz⟩ := hz
  refine ⟨i, hi, ?_⟩
  simp only [hardCaseIterate, LinearEquiv.apply_symm_apply]
  exact repr_iterate_vector_ne_zero (secularHessian_isSymmetric hH hM)
    ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c hz k hreg

end CartisGouldToint.Chapter09.Section03
