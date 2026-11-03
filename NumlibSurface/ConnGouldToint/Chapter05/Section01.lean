import Numlib.Krylov.Preconditioned
import Numlib.Krylov.Singular
import Numlib.Optimization.Subproblem.Model

/-!
# Conjugate gradients

Section 5.1 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter05

open Krylov
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic objective (5.1.1) with linear term `c` and Hessian `H`. -/
noncomputable abbrev quadraticObjective (c : E) (H : E →L[ℝ] E) : E → ℝ :=
  Subproblem.quadModel c H

/-- Algorithm 5.1.2. The state of the conjugate gradient recurrence. The library
stores the residual `-gₖ` in place of the gradient `gₖ`. -/
noncomputable abbrev algorithm_5_1_2 (H : E →ₗ[ℝ] E) (c x₀ : E) (k : ℕ) : CG.State E :=
  CG.iterate H (-c) x₀ k

/-- Algorithm 5.1.4. The state of the preconditioned conjugate gradient recurrence.
The library stores the residual `-gₖ` and evaluates the preconditioned gradient
through the given inverse when needed. -/
noncomputable abbrev algorithm_5_1_4 (H Minv : E →ₗ[ℝ] E) (c x₀ : E) (k : ℕ) : PCG.State E :=
  PCG.iterate H Minv (-c) x₀ k

/-- Theorem 5.1.6. Conjugate gradients reach the exact solution in at most the
number of distinct eigenvalues. The finite set may also contain extra values, in
which case its cardinality is still an upper bound on the number of steps. -/
theorem theorem_5_1_6 [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetricCoercive) {c x₀ xstar : E} (hstar : H xstar = -c)
    (S : Finset ℝ) (hS : ∀ μ, Module.End.HasEigenvalue H μ → μ ∈ S) :
    (algorithm_5_1_2 H c x₀ S.card).x = xstar := by
  have hmem : -c - H x₀ ∈ LinearMap.range H :=
    ⟨xstar - x₀, by rw [map_sub, hstar]⟩
  have hgrade := Lanczos.grade_le_card_eigenvalues_of_mem_range hH.isSymmetric
    (fun μ _ hμ => hS μ hμ) hmem
  have happly := (CG.isGalerkinIterate (-c) x₀ hH S.card).apply_eq_of_grade_le hgrade
  exact hH.isCoercive.injective (happly.trans hstar.symm)

/-- Theorem 5.1.7. The energy-norm error of the conjugate gradient iteration satisfies the
Chebyshev bound for a positive spectral interval. The ratio of the endpoints is the spectral
condition number when the endpoints are the extreme eigenvalues. The product form includes
the case of an exact initial iterate. -/
theorem theorem_5_1_7 {H : E →ₗ[ℝ] E} {c x₀ xstar : E} (hstar : H xstar = -c)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hH : H.IsSymmetricBoundedBy lmin lmax) (k : ℕ) :
    energyNorm H ((algorithm_5_1_2 H c x₀ k).x - xstar) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ k *
        energyNorm H (x₀ - xstar) := by
  rw [energyNorm_sub_comm H _ xstar, energyNorm_sub_comm H x₀ xstar]
  exact IsGalerkinIterate.energyNorm_error_le hl hll hH
    (CG.isGalerkinIterate (-c) x₀ (hH.isSymmetricCoercive hl) k) hstar

/-- Corollary 5.1.8. Preconditioned conjugate gradients obey the same energy-norm error
bound, with the interval given by the generalized eigenvalues of the pair `(H, M)`.
Taking the endpoints to be the extreme generalized eigenvalues gives the spectral
condition number of `M⁻¹ H`. -/
theorem corollary_5_1_8 {H M Minv : E →ₗ[ℝ] E} (hM : IsPreconditioner M Minv)
    (hH : H.IsSymmetric) {c x₀ xstar : E} (hstar : H xstar = -c)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hmin : ∀ x : E, lmin * ⟪M x, x⟫ ≤ ⟪H x, x⟫)
    (hmax : ∀ x : E, ⟪H x, x⟫ ≤ lmax * ⟪M x, x⟫) (k : ℕ) :
    energyNorm H ((algorithm_5_1_4 H Minv c x₀ k).x - xstar) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ k *
        energyNorm H (x₀ - xstar) := by
  rw [energyNorm_sub_comm H _ xstar, energyNorm_sub_comm H x₀ xstar]
  exact PCG.energyNorm_error_le hM hH hl hll hmin hmax hstar k

/-- Corollary 5.1.9. Preconditioned conjugate gradients reach the exact solution in
at most the number of distinct eigenvalues of the preconditioned operator. -/
theorem corollary_5_1_9 [FiniteDimensional ℝ E] {H M Minv : E →ₗ[ℝ] E}
    (hM : IsPreconditioner M Minv) (hH : H.IsSymmetric)
    {l : ℝ} (hl : 0 < l) (hlo : ∀ x : E, l * ⟪M x, x⟫ ≤ ⟪H x, x⟫)
    {c x₀ xstar : E} (hstar : H xstar = -c)
    (S : Finset ℝ) (hS : ∀ μ, Module.End.HasEigenvalue (Minv ∘ₗ H) μ → μ ∈ S) :
    (algorithm_5_1_4 H Minv c x₀ S.card).x = xstar := by
  let B := hM.energyEnd (Minv ∘ₗ H)
  have hB : B.IsSymmetricCoercive := hM.isSymmetricCoercive_energyEnd H hH hl hlo
  have hS' (μ : ℝ) (hμ : Module.End.HasEigenvalue B μ) : μ ∈ S := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    obtain ⟨u, rfl⟩ := hM.toEnergy.surjective v
    have hu : u ≠ 0 := by
      intro hu
      exact (Module.End.hasEigenvector_iff.mp hv).2 (by simp [hu])
    have heq := hv.apply_eq_smul
    change hM.energyEnd (Minv ∘ₗ H) (hM.toEnergy u) = μ • hM.toEnergy u at heq
    rw [IsPreconditioner.energyEnd_apply, ← map_smul] at heq
    have huv : Module.End.HasEigenvector (Minv ∘ₗ H) μ u :=
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hM.toEnergy.injective heq), hu⟩
    exact hS μ (Module.End.hasEigenvalue_of_hasEigenvector huv)
  have hstar' : B (hM.toEnergy xstar) = -hM.toEnergy (Minv c) := by
    simp [B, LinearMap.comp_apply, hstar]
  have h := theorem_5_1_6 hB hstar' S hS' (x₀ := hM.toEnergy x₀)
  apply hM.toEnergy.injective
  rw [PCG.toEnergy_iterate_x H Minv (-c) x₀ hM S.card]
  simpa only [B, map_neg] using h

end ConnGouldToint.Chapter05
