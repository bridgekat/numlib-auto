/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Complex.ContourIntegral
import Mathlib.Analysis.Matrix.Normed

/-!
# §4.9. Resolvent representations

The Riesz projection associated with selected eigenvalues is the sum of their spectral
idempotents. A positively oriented contour enclosing those eigenvalues represents the
projection by a normalized integral of the resolvent.

## Main definitions

* `LiesenStrakos.rieszProjection` selects the spectral idempotents for the given eigenvalues.

## Main results

* `LiesenStrakos.theorem_4_9_1` is the contour formula for the Riesz projection.
* `LiesenStrakos.spectral_idempotents_4_9_7` gives the pairwise orthogonality and resolution
  of the identity.

## Conventions

* Positive orientation and enclosure are expressed by winding integrals equal to one at
  the selected eigenvalues and zero at the remaining eigenvalues.
* The parametrization is a finite concatenation of continuously differentiable paths
  (`Path.IsPiecewiseC1`).

## Deviations from the source

* **Equations (4.9.2) and (4.9.7)** (generalization). The spectral sum uses only eigenvalues,
  and spectral idempotents are zero elsewhere.
* **Theorem 4.9.1** (reading). The contour is piecewise $C^1$, and the eigenvalues are
  selected by winding indices. The same formula permits self-intersecting contours with
  the specified indices. See `LiesenStrakos.theorem_4_9_1`.
-/

open scoped Real Matrix.Norms.Operator
open Complex

namespace LiesenStrakos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The projection in (4.9.2) of [liesen2013krylov] onto the sum of the selected generalized
eigenspaces along the sum of the remaining generalized eigenspaces.

**Generalization.** Selected scalars outside the spectrum contribute nothing. -/
noncomputable def rieszProjection (A : Matrix ι ι ℂ) (s : Finset ℂ) : Matrix ι ι ℂ := by
  classical
  exact ∑ w ∈ (minpoly ℂ A).roots.toFinset.filter (· ∈ s), spectralIdempotent A w

/-- **Theorem 4.9.1** of [liesen2013krylov].
If a piecewise $C^1$ loop avoids the spectrum and winds once around each selected eigenvalue and
zero times around the others, the normalized contour integral of $(zI-A)^{-1}$ is the
Riesz projection for that selection.

**Reading.** The source uses a simple, positively oriented closed curve and leaves the
regularity for the integral implicit. The statement assumes piecewise $C^1$ regularity and
uses the winding index at each eigenvalue to encode enclosure. These winding hypotheses
also allow contours with self-intersections. -/
theorem theorem_4_9_1 (A : Matrix ι ι ℂ) (s : Finset ℂ) {z₀ : ℂ} (γ : Path z₀ z₀)
    (hγ : γ.IsPiecewiseC1)
    (havoid : ∀ t ∈ unitInterval, γ.extend t ∉ (minpoly ℂ A).roots)
    (hwind : ∀ w ∈ (minpoly ℂ A).roots, complexPathIndex γ w = if w ∈ s then 1 else 0) :
    (2 * π * I)⁻¹ • complexLineIntegral γ (fun z => Ring.inverse (algebraMap ℂ _ z - A)) =
      rieszProjection A s := by
  classical
  rw [complexLineIntegral_resolvent (Algebra.IsIntegral.isIntegral A) γ hγ havoid,
    rieszProjection, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  rw [hwind w (Multiset.mem_toFinset.mp hw)]
  split_ifs <;> simp

/-- **Equation (4.9.7)** of [liesen2013krylov].
Distinct spectral idempotents multiply to zero and their sum is the identity.

**Generalization.** The pairwise product statement includes values outside the spectrum, where
the spectral idempotent is zero. -/
theorem spectral_idempotents_4_9_7 (A : Matrix ι ι ℂ) :
    (∀ u v : ℂ, u ≠ v → spectralIdempotent A u * spectralIdempotent A v = 0) ∧
      (∑ u ∈ (minpoly ℂ A).roots.toFinset, spectralIdempotent A u) = 1 := by
  classical
  have ha : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  exact ⟨fun u v h => by rw [spectralIdempotent_mul_spectralIdempotent ha hs, ite_eq_right h],
    sum_spectralIdempotent ha hs⟩

end LiesenStrakos
