import Numlib.Optimization.HigherOrder
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Nonlinear optimization and optimality conditions

The unconstrained optimality conditions of Theorem 1.1.1 and all valid necessary clauses of
Theorem 1.1.2, with the radial feasible displacements from (1.1.7). Derivatives are the actual
Fréchet derivatives of the objective. A curried Hessian is the bilinear form corresponding to
the symmetric Hessian matrix, so its kernel is expressed as a zero covector. The trilinear
third derivative is evaluated on three copies of the direction.

The printed converse of Theorem 1.1.2 requires a correction for general convex feasible sets
and is deliberately kept separate from its necessary clauses.
-/

open Filter Topology Metric Set

namespace CartisGouldToint.Chapter01.Section01

/-- Theorem 1.1.1: first-, second-, and third-order necessary conditions and the strict
second-order sufficient condition for unconstrained Euclidean minimization.
The Hessian and third derivative are expressed as curried Fréchet derivatives. -/
theorem theorem_1_1_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (ContDiff ℝ 1 f → IsLocalMin f x → gradient f x = 0) ∧
    (ContDiff ℝ 2 f → IsLocalMin f x →
      ∀ d, 0 ≤ fderiv ℝ (fderiv ℝ f) x d d) ∧
    (ContDiff ℝ 3 f → IsLocalMin f x →
      ∀ d, fderiv ℝ (fderiv ℝ f) x d = 0 →
        fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x d d d = 0) ∧
    (ContDiff ℝ 2 f → gradient f x = 0 →
      (∀ d, d ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x d d) →
      ∃ δ > 0, ∀ y ∈ ball x δ, y ≠ x → f x < f y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ hmin
    simp [gradient, hmin.fderiv_eq_zero]
  · intro hf hmin d
    have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    exact Descent.nonneg_apply_apply_of_isLocalMin hmin
      (Eventually.of_forall fun y => (hf.differentiable (by norm_num) y).hasFDerivAt)
      (hf'.differentiable (by norm_num) x).hasFDerivAt d
  · intro hf hmin d hd
    have hf' : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have hf'' : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) :=
      hf'.fderiv_right (by norm_num)
    apply Descent.third_apply_apply_apply_eq_zero_of_isLocalMin hmin
      (Eventually.of_forall fun y => (hf.differentiable (by norm_num) y).hasFDerivAt)
      (Eventually.of_forall fun y => (hf'.differentiable (by norm_num) y).hasFDerivAt)
      (hf''.differentiable (by norm_num) x).hasFDerivAt d
    simp [hd]
  · intro hf hcrit hpos
    apply Descent.isLocalMin_of_posDef_second hf _ hpos
    simpa only [gradient, EmbeddingLike.map_eq_zero_iff] using hcrit


/-- The radial feasible displacements in (1.1.7). -/
def feasibleDisplacements {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) := {d | x + d ∈ C}

@[simp] theorem mem_feasibleDisplacements {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {x d : EuclideanSpace ℝ (Fin n)} : d ∈ feasibleDisplacements C x ↔ x + d ∈ C := Iff.rfl

/-- The valid necessary clauses of Theorem 1.1.2. Closedness is not needed for necessity.
Regularity is assumed only on the open neighborhood `S` of the feasible set. -/
theorem theorem_1_1_2_necessary {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {C S : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hC : Convex ℝ C) (hS : IsOpen S) (hCS : C ⊆ S) (hx : x ∈ C)
    (hmin : IsLocalMinOn f C x) :
    (ContDiffOn ℝ 1 f S → ∀ d ∈ feasibleDisplacements C x, 0 ≤ fderiv ℝ f x d) ∧
    (ContDiffOn ℝ 2 f S → ∀ d ∈ feasibleDisplacements C x,
      fderiv ℝ f x d = 0 → 0 ≤ fderiv ℝ (fderiv ℝ f) x d d) ∧
    (ContDiffOn ℝ 3 f S → ∀ d ∈ feasibleDisplacements C x,
      fderiv ℝ f x d = 0 → fderiv ℝ (fderiv ℝ f) x d d = 0 →
        0 ≤ fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x d d d) := by
  have hxS : x ∈ S := hCS hx
  have hSnhds : S ∈ 𝓝 x := hS.mem_nhds hxS
  refine ⟨?_, ?_, ?_⟩
  · intro hf d hd
    have h := Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn hC hx hmin
      (hf.differentiableOn (by norm_num) x hxS |>.differentiableAt hSnhds).hasFDerivAt
      (x + d) hd
    simpa using h
  · intro hf d hd hcrit
    have hf' : ContDiffOn ℝ 1 (fderiv ℝ f) S := hf.fderiv_of_isOpen hS (by norm_num)
    apply Descent.nonneg_apply_apply_of_isLocalMinOn hC hx hd hmin _ _ hcrit
    · filter_upwards [hSnhds] with y hy
      exact (hf.differentiableOn (by norm_num) y hy
        |>.differentiableAt (hS.mem_nhds hy)).hasFDerivAt
    · exact (hf'.differentiableOn (by norm_num) x hxS |>.differentiableAt hSnhds).hasFDerivAt
  · intro hf d hd hcrit hcrit'
    have hf' : ContDiffOn ℝ 2 (fderiv ℝ f) S := hf.fderiv_of_isOpen hS (by norm_num)
    have hf'' : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ f)) S :=
      hf'.fderiv_of_isOpen hS (by norm_num)
    apply Descent.nonneg_third_apply_apply_apply_of_isLocalMinOn hC hx hd hmin _ _ _ hcrit hcrit'
    · filter_upwards [hSnhds] with y hy
      exact (hf.differentiableOn (by norm_num) y hy
        |>.differentiableAt (hS.mem_nhds hy)).hasFDerivAt
    · filter_upwards [hSnhds] with y hy
      exact (hf'.differentiableOn (by norm_num) y hy
        |>.differentiableAt (hS.mem_nhds hy)).hasFDerivAt
    · exact (hf''.differentiableOn (by norm_num) x hxS |>.differentiableAt hSnhds).hasFDerivAt
end CartisGouldToint.Chapter01.Section01
