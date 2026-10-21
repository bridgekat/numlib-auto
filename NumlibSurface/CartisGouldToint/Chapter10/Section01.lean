import Numlib.Optimization.KrylovSubproblem
import Numlib.Krylov.PreconditionedLanczos
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Chapter 10, Section 1: quadratic subproblems in Krylov spaces

Arbitrary basis matrices give the exact reduced gradient, Hessian, and metric. The reduced
objectives and feasible sets agree with the original subspace problems. Preconditioned
Lanczos is specified by its actual residual recurrence with explicit cached matrix products
and a breakdown test before normalization.
-/

noncomputable section
open scoped InnerProductSpace
open Set Metric
open CartisGouldToint.Chapter08.Section01
namespace CartisGouldToint.Chapter10.Section01
variable {n k : ℕ}

/-- The reduced gradient, Hessian, and scaling matrix associated with a basis matrix. -/
structure ReducedQuadraticData (k : ℕ) where
  gradient : EuclideanSpace ℝ (Fin k)
  hessian : Matrix (Fin k) (Fin k) ℝ
  metric : Matrix (Fin k) (Fin k) ℝ

/-- The source subspace problems (10.1.1)–(10.1.6), with all three actual compressed
coefficients. Injectivity is needed only to call the columns a basis, not for model equality. -/
def subspaceQuadraticProblems (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ) :
    ReducedQuadraticData k :=
  ⟨Matrix.toEuclideanLin S.transpose g, S.transpose * H * S, S.transpose * M * S⟩

/-- The arbitrary-basis quadratic reduction preserves the actual objective values. -/
theorem subspaceQuadraticProblems_quadratic (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ)
    (s : EuclideanSpace ℝ (Fin k)) :
    quadraticModel (subspaceQuadraticProblems g H M S).gradient
      (subspaceQuadraticProblems g H M S).hessian s =
      quadraticModel g H (Matrix.toEuclideanLin S s) := by
  simp only [subspaceQuadraticProblems, quadraticModel, Matrix.toEuclideanLin_mul_apply]
  have hs : S.transpose = S.conjTranspose := by simp
  rw [hs, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]

/-- The compressed metric preserves the source norm, including singular basis matrices. -/
theorem subspaceQuadraticProblems_norm (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ)
    (s : EuclideanSpace ℝ (Fin k)) :
    weightedNorm (subspaceQuadraticProblems g H M S).metric s =
      weightedNorm M (Matrix.toEuclideanLin S s) := by
  simp only [subspaceQuadraticProblems, weightedNorm, Matrix.toEuclideanLin_mul_apply]
  have hs : S.transpose = S.conjTranspose := by simp
  rw [hs, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-- The radial regularized reduction also preserves every actual objective value. -/
theorem subspaceQuadraticProblems_regularized (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ)
    (sigma r : ℝ) (s : EuclideanSpace ℝ (Fin k)) :
    regularizedModel (subspaceQuadraticProblems g H M S).gradient
      (subspaceQuadraticProblems g H M S).hessian
      (subspaceQuadraticProblems g H M S).metric sigma r s =
      regularizedModel g H M sigma r (Matrix.toEuclideanLin S s) := by
  rw [regularizedModel, regularizedModel, subspaceQuadraticProblems_quadratic,
    subspaceQuadraticProblems_norm]

/-- The source trust-region subproblem restricted to the represented subspace. -/
def trustRegionSubspaceMinimizer (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ)
    (delta : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  s ∈ Set.range (Matrix.toEuclideanLin S) ∧ weightedNorm M s ≤ delta ∧
    IsMinOn (quadraticModel g H)
      {x | x ∈ Set.range (Matrix.toEuclideanLin S) ∧ weightedNorm M x ≤ delta} s

/-- The source regularized subproblem restricted to the represented subspace. -/
def regularizedSubspaceMinimizer (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ)
    (sigma r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  s ∈ Set.range (Matrix.toEuclideanLin S) ∧
    IsMinOn (regularizedModel g H M sigma r) (Set.range (Matrix.toEuclideanLin S)) s

/-- The reduced feasible ball maps exactly onto the original subspace feasible ball. -/
theorem image_reduced_feasible (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ) (delta : ℝ) :
    Matrix.toEuclideanLin S ''
      {t | weightedNorm (subspaceQuadraticProblems g H M S).metric t ≤ delta} =
      {x | x ∈ Set.range (Matrix.toEuclideanLin S) ∧ weightedNorm M x ≤ delta} := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, rfl⟩, by simpa only [Set.mem_ofPred_eq, subspaceQuadraticProblems_norm] using hs⟩
  · rintro ⟨⟨s, rfl⟩, hs⟩
    exact ⟨s, by simpa only [Set.mem_ofPred_eq, subspaceQuadraticProblems_norm] using hs, rfl⟩

/-- Actual trust-region minimizers correspond under the arbitrary basis reduction. -/
theorem trustRegionSubspaceMinimizer_iff (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ)
    (delta : ℝ) (s : EuclideanSpace ℝ (Fin k)) :
    trustRegionSubspaceMinimizer g H M S delta (Matrix.toEuclideanLin S s) ↔
      trustRegionMinimizer (subspaceQuadraticProblems g H M S).gradient
        (subspaceQuadraticProblems g H M S).hessian (subspaceQuadraticProblems g H M S).metric
        delta s := by
  have hi := isMinOn_image_iff (quadraticModel g H) (Matrix.toEuclideanLin S)
    {t | weightedNorm (subspaceQuadraticProblems g H M S).metric t ≤ delta} s
  rw [image_reduced_feasible] at hi
  simp only [Function.comp_def, ← subspaceQuadraticProblems_quadratic g H M S] at hi
  simp only [trustRegionSubspaceMinimizer, Set.mem_range_self, true_and, trustRegionMinimizer,
    subspaceQuadraticProblems_norm]
  exact and_congr_right fun _ => by simpa only [subspaceQuadraticProblems_norm] using hi

/-- Actual regularized minimizers correspond under the arbitrary basis reduction. -/
theorem regularizedSubspaceMinimizer_iff (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin k) ℝ)
    (sigma r : ℝ) (s : EuclideanSpace ℝ (Fin k)) :
    regularizedSubspaceMinimizer g H M S sigma r (Matrix.toEuclideanLin S s) ↔
      regularizedMinimizer (subspaceQuadraticProblems g H M S).gradient
        (subspaceQuadraticProblems g H M S).hessian (subspaceQuadraticProblems g H M S).metric
        sigma r s := by
  simpa only [regularizedSubspaceMinimizer, Set.mem_range_self, true_and,
    regularizedMinimizer, Set.image_univ, Function.comp_def,
    ← subspaceQuadraticProblems_regularized g H M S sigma r] using
    isMinOn_image_iff (regularizedModel g H M sigma r) (Matrix.toEuclideanLin S) Set.univ s

/-- The preconditioned Krylov space uses the existing Krylov construction verbatim. -/
def preconditionedKrylovSpace (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (j : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Krylov.subspace (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
    (Matrix.toEuclideanLin M⁻¹ g) j

/-- The source Krylov spaces are nested. -/
theorem preconditionedKrylovSpace_mono (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) : Monotone (preconditionedKrylovSpace g H M) :=
  Krylov.subspace_mono _ _

/-- A zero gradient has grade zero; no normalization step is needed. -/
theorem preconditionedKrylovSpace_grade_zero (H M : Matrix (Fin n) (Fin n) ℝ) :
    Krylov.grade (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
      (Matrix.toEuclideanLin M⁻¹ (0 : EuclideanSpace ℝ (Fin n))) = 0 := by simp

/-- The source grade is at most the ambient dimension. -/
theorem preconditioned_grade_le (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) :
    Krylov.grade (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
      (Matrix.toEuclideanLin M⁻¹ g) ≤ n := by
  simpa using Krylov.grade_le_finrank
    (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H) (Matrix.toEuclideanLin M⁻¹ g)

/-- At the grade the existing Krylov construction reaches its full invariant subspace. -/
theorem preconditionedKrylovSpace_at_grade (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) :
    preconditionedKrylovSpace g H M
      (Krylov.grade (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
        (Matrix.toEuclideanLin M⁻¹ g)) =
      Krylov.fullSubspace (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
        (Matrix.toEuclideanLin M⁻¹ g) :=
  Krylov.subspace_grade_eq_fullSubspace _ _

/-- Algorithm 10.1.1 as a literal preconditioned Lanczos execution. The source's one-based
index `k` is canonical index `k-1`. The finite budget is the ambient dimension; breakdown is
checked before dividing by the coefficient. Both matrix products are actual cached oracles. -/
abbrev algorithm_10_1_1 (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ)
    (states : ℕ → Krylov.PreconditionedLanczos.State (EuclideanSpace ℝ (Fin n)))
    (trials : ℕ → Krylov.PreconditionedLanczos.Trial (EuclideanSpace ℝ (Fin n))) (N : ℕ) :=
  Krylov.PreconditionedLanczos.Execution (Matrix.toEuclideanLin H)
    (Matrix.toEuclideanLin M⁻¹) g states trials n N

/-- Active source iterations normalize their primal vector in the genuine SPD metric. -/
theorem algorithm_10_1_1_primal_norm {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    {states : ℕ → Krylov.PreconditionedLanczos.State (EuclideanSpace ℝ (Fin n))}
    {trials : ℕ → Krylov.PreconditionedLanczos.Trial (EuclideanSpace ℝ (Fin n))}
    {N i : ℕ} (h : algorithm_10_1_1 g H M states trials N) (hi : i < N) :
    weightedNorm M (trials i).primal = 1 := by
  have hg : (Krylov.PreconditionedLanczos.evaluate (Matrix.toEuclideanLin H)
      (Matrix.toEuclideanLin M⁻¹) (states i)).gamma ≠ 0 := by
    rw [← h.oracle i hi]
    exact h.active i hi
  have hn := Krylov.PreconditionedLanczos.norm_primal_eq_one
    hM.isPreconditioner_toEuclideanLin (Matrix.toEuclideanLin H) (states i) hg
  rw [h.oracle i hi, weightedNorm_eq_energyNorm]
  exact hn

/-- The literal breakdown test is a zero residual, so the initial zero gradient cannot
force a normalization by zero. -/
theorem algorithm_10_1_1_breakdown_iff (H M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) (s : Krylov.PreconditionedLanczos.State (EuclideanSpace ℝ (Fin n))) :
    (Krylov.PreconditionedLanczos.evaluate (Matrix.toEuclideanLin H)
      (Matrix.toEuclideanLin M⁻¹) s).gamma = 0 ↔ s.residual = 0 :=
  Krylov.PreconditionedLanczos.gamma_eq_zero_iff hM.isPreconditioner_toEuclideanLin _ _

/-- The full generalized eigenspace at the hard-case cutoff, including every vector when
the lowest generalized eigenvalue is repeated. -/
def hardCaseEigenspace {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (hM : M.PosDef) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (Matrix.toEuclideanLin H + Chapter08.Section02.secularThreshold hH hM •
    Matrix.toEuclideanLin M).ker

/-- A dual gradient orthogonal to the full hard-case eigenspace makes every Krylov vector
metric-orthogonal to it. Its whole dimension is missing from the maximum possible grade. -/
theorem krylovMissesHardCaseEigenspace {H M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hg : ∀ v ∈ hardCaseEigenspace hH hM, ⟪g, v⟫_ℝ = 0) :
    (∀ j, ∀ s ∈ preconditionedKrylovSpace g H M j,
      ∀ v ∈ hardCaseEigenspace hH hM, ⟪Matrix.toEuclideanLin M s, v⟫_ℝ = 0) ∧
    Krylov.grade (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
      (Matrix.toEuclideanLin M⁻¹ g) ≤ n - Module.finrank ℝ (hardCaseEigenspace hH hM) := by
  have hv : ∀ v ∈ hardCaseEigenspace hH hM,
      Matrix.toEuclideanLin H v = (-Chapter08.Section02.secularThreshold hH hM) •
        Matrix.toEuclideanLin M v := by
    intro v hv
    change Matrix.toEuclideanLin H v + Chapter08.Section02.secularThreshold hH hM •
      Matrix.toEuclideanLin M v = 0 at hv
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hv
  have horth := Optimization.KrylovSubproblem.fullSubspace_le_metric_orthogonal
    hH.isSymmetric_toEuclideanLin hM.isPreconditioner_toEuclideanLin
    (hardCaseEigenspace hH hM) (-Chapter08.Section02.secularThreshold hH hM) hv hg
  have hdim := Optimization.KrylovSubproblem.grade_add_finrank_le_of_metric_orthogonal
    hH.isSymmetric_toEuclideanLin hM.isPreconditioner_toEuclideanLin
    (hardCaseEigenspace hH hM) (-Chapter08.Section02.secularThreshold hH hM) hv hg
  constructor
  · intro j s hs v hv
    have hs' := horth (Krylov.subspace_le_fullSubspace _ _ j hs)
    have hz := (((hardCaseEigenspace hH hM).map (Matrix.toEuclideanLin M)).mem_orthogonal' s).mp
      hs' (Matrix.toEuclideanLin M v) ⟨v, hv, rfl⟩
    rw [hM.isSymmetricCoercive_toEuclideanLin.isSymmetric]
    exact hz
  · have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    rw [hn] at hdim
    omega

end CartisGouldToint.Chapter10.Section01
