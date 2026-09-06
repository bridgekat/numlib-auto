import Numlib.Krylov.CG
import Numlib.Krylov.CR
import Numlib.LinearSolve.Perturbation

/-!
# Monotonicity properties of Krylov iterates on SPD systems (Fong–Saunders)

Specification-level versions of Fong–Saunders[^fong-saunders] Thm 2.3–2.5 and Thm 3.1: for *any*
sequence of minimal-residual Krylov iterates of a symmetric coercive system (MINRES, CR, GMRES, …)
started at `x₀ = 0`, `‖x_k‖` is nondecreasing, `‖x* - x_k‖` and `‖x* - x_k‖_A` are nonincreasing,
and the normwise relative backward error is nonincreasing. Proved by identifying the iterates with
the CR iterates (`CR.isMinResIterate` + uniqueness) and using the sign lemma of `CR.lean`.

The same argument run through the CG iterates gives the Galerkin counterparts, which hold on the
same SPD systems but are older: `‖x_k‖` is nondecreasing from `x₀ = 0`, due to
Steihaug[^steihaug] and tabulated as the CG column of Fong–Saunders Table 5.1, and `‖x* - x_k‖`
is nonincreasing, Hestenes–Stiefel[^hestenes-stiefel] Thm 6:3.

## References

[^fong-saunders]: David Chin-Lung Fong and Michael Saunders, *CG versus MINRES: an empirical
  comparison*, SQU Journal for Science 17 (2012), 44–62.
[^steihaug]: Trond Steihaug, *The conjugate gradient method and trust regions in large scale
  optimization*, SIAM Journal on Numerical Analysis 20 (1983), 626–637.
[^hestenes-stiefel]: Magnus R. Hestenes and Eduard Stiefel, *Methods of conjugate gradients for
  solving linear systems*, Journal of Research of the National Bureau of Standards 49 (1952),
  409–436.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive) {b : E}

namespace Krylov.IsMinResIterate

include hA

set_option linter.unusedSectionVars false in
/-- Minimal-residual iterates of an SPD system coincide with the CR iterates. -/
theorem eq_CR_iterate {x₀ : E} {k : ℕ} {x : E} (hx : IsMinResIterate A b x₀ k x) :
    x = (CR.iterate A b x₀ k).x := by
  obtain ⟨y, -, huniq⟩ :=
    existsUnique_isMinResIterate_of_injective hA.isCoercive.injective b x₀ k
  exact (huniq x hx).trans (huniq _ (CR.isMinResIterate b x₀ hA k)).symm

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.3: `‖x_k‖` is nondecreasing (`x₀ = 0`). -/
theorem norm_monotone {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b 0 k (x k)) :
    Monotone fun k => ‖x k‖ := by
  have h : ∀ k, x k = (CR.iterate A b 0 k).x := fun k => eq_CR_iterate hA (hx k)
  simpa only [h] using CR.norm_iterate_monotone b hA

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.4: `‖x* - x_k‖` is nonincreasing. -/
theorem norm_error_antitone {x₀ : E} {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b x₀ k (x k))
    {xstar : E} (hstar : A xstar = b) : Antitone fun k => ‖xstar - x k‖ := by
  have h : ∀ k, x k = (CR.iterate A b x₀ k).x := fun k => eq_CR_iterate hA (hx k)
  simpa only [h] using CR.norm_error_antitone b x₀ hA hstar

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.5: `‖x* - x_k‖_A` is nonincreasing. -/
theorem energyNorm_error_antitone {x₀ : E} {x : ℕ → E}
    (hx : ∀ k, IsMinResIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - x k) := by
  have h : ∀ k, x k = (CR.iterate A b x₀ k).x := fun k => eq_CR_iterate hA (hx k)
  simpa only [h] using CR.energyNorm_error_antitone b x₀ hA hstar

omit hA [FiniteDimensional 𝕜 E] in
/-- Choi, *Iterative Methods for Singular Linear Equations and Least-Squares Problems*,
Lemma 2.20: for minimal-residual iterates from `x₀ = 0`, `‖A x_k‖` is nondecreasing in `k`.
Indeed `A x_k ∈ A 𝒦_k` while `r_k = b - A x_k ⟂ A 𝒦_k`, so `‖A x_k‖² = ‖b‖² - ‖r_k‖²`, and
`‖r_k‖` is nonincreasing (`Krylov.IsMinResIterate.norm_residual_antitone`).  Neither symmetry
nor coercivity of `A` is used. -/
theorem norm_apply_monotone {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b 0 k (x k)) :
    Monotone fun k => ‖A (x k)‖ := by
  have key : ∀ k, ‖A (x k)‖ ^ 2 + ‖b - A (x k)‖ ^ 2 = ‖b‖ ^ 2 := by
    intro k
    have hmem : A (x k) ∈ (subspace A (b - A 0) k).map A :=
      Submodule.mem_map_of_mem (by simpa using (hx k).mem)
    have h0 : inner 𝕜 (A (x k)) (b - A (x k)) = (0 : 𝕜) :=
      (Submodule.mem_orthogonal _ _).1 (hx k).residual_mem_orthogonal _ hmem
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [show A (x k) + (b - A (x k)) = b by abel] at h
    nlinarith [h]
  intro i j hij
  have hr : ‖b - A (x j)‖ ≤ ‖b - A (x i)‖ := norm_residual_antitone hx hij
  have hsq : ‖A (x i)‖ ^ 2 ≤ ‖A (x j)‖ ^ 2 := by
    nlinarith [key i, key j, norm_nonneg (b - A (x i)), norm_nonneg (b - A (x j))]
  nlinarith [norm_nonneg (A (x i)), norm_nonneg (A (x j))]

/-- Fong–Saunders, *CG versus MINRES*, Thm 3.1: the normwise relative backward error
`‖r_k‖ / (α ‖A‖ ‖x_k‖ + β ‖b‖)` is nonincreasing (`x₀ = 0`, `α ≥ 0`, `β > 0`). The
denominator is positive at every step, so no junk division occurs. -/
theorem backwardError_antitone {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b 0 k (x k))
    {normA α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) (hnormA : 0 ≤ normA) (hb : b ≠ 0) :
    Antitone fun k => ‖b - A (x k)‖ / (α * normA * ‖x k‖ + β * ‖b‖) := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hmono : Monotone fun k => ‖x k‖ := norm_monotone hA hx
  intro i j hij
  have hden : ∀ k : ℕ, 0 < α * normA * ‖x k‖ + β * ‖b‖ := by
    intro k
    have h1 : 0 ≤ α * normA * ‖x k‖ := by positivity
    have h2 : 0 < β * ‖b‖ := by positivity
    linarith
  rw [div_le_div_iff₀ (hden j) (hden i)]
  refine mul_le_mul (norm_residual_antitone hx hij) ?_ (le_of_lt (hden i)) (norm_nonneg _)
  have := hmono hij
  simp only at this
  nlinarith [mul_nonneg hα hnormA]

/-- The special case `‖r_k‖ / ‖x_k‖` (Fong–Saunders, *CG versus MINRES*, (3.5) with `β = 0`),
from step `1` on:
at `k = 0` the quotient `‖b‖ / ‖0‖` is a junk value, so the statement is on `Set.Ici 1`. -/
theorem norm_residual_div_norm_antitoneOn {x : ℕ → E}
    (hx : ∀ k, IsMinResIterate A b 0 k (x k)) (hb : b ≠ 0) :
    AntitoneOn (fun k => ‖b - A (x k)‖ / ‖x k‖) (Set.Ici 1) := by
  have hmono : Monotone fun k => ‖x k‖ := norm_monotone hA hx
  have h1 : 0 < ‖x 1‖ := by
    rw [norm_pos_iff, eq_CR_iterate hA (hx 1)]
    exact CR.iterate_one_x_ne_zero b hA hb
  intro i hi j hj hij
  simp only [Set.mem_Ici] at hi hj
  have hxi : 0 < ‖x i‖ := lt_of_lt_of_le h1 (hmono hi)
  have hxj : 0 < ‖x j‖ := lt_of_lt_of_le h1 (hmono hj)
  rw [div_le_div_iff₀ hxj hxi]
  exact mul_le_mul (norm_residual_antitone hx hij) (hmono hij) (le_of_lt hxi) (norm_nonneg _)

end Krylov.IsMinResIterate

namespace Krylov.IsGalerkinIterate

include hA

set_option linter.unusedSectionVars false in
/-- Galerkin iterates of an SPD system coincide with the CG iterates. -/
theorem eq_CG_iterate {x₀ : E} {k : ℕ} {x : E} (hx : IsGalerkinIterate A b x₀ k x) :
    x = (CG.iterate A b x₀ k).x := by
  obtain ⟨y, -, huniq⟩ := existsUnique_isGalerkinIterate_of_isCoercive hA.isCoercive b x₀ k
  exact (huniq x hx).trans (huniq _ (CG.isGalerkinIterate b x₀ hA k)).symm

/-- Steihaug, *The conjugate gradient method and trust regions in large scale optimization*
(tabulated as the CG column of Fong–Saunders, *CG versus MINRES*, Table 5.1): `‖x_k‖` is
nondecreasing (`x₀ = 0`). -/
theorem norm_monotone {x : ℕ → E} (hx : ∀ k, IsGalerkinIterate A b 0 k (x k)) :
    Monotone fun k => ‖x k‖ := by
  have h : ∀ k, x k = (CG.iterate A b 0 k).x := fun k => eq_CG_iterate hA (hx k)
  simpa only [h] using CG.norm_iterate_monotone b hA

/-- Hestenes–Stiefel, *Methods of conjugate gradients for solving linear systems*, Thm 6:3:
`‖x* - x_k‖` is nonincreasing. -/
theorem norm_error_antitone {x₀ : E} {x : ℕ → E} (hx : ∀ k, IsGalerkinIterate A b x₀ k (x k))
    {xstar : E} (hstar : A xstar = b) : Antitone fun k => ‖xstar - x k‖ := by
  have h : ∀ k, x k = (CG.iterate A b x₀ k).x := fun k => eq_CG_iterate hA (hx k)
  simpa only [h] using CG.norm_error_antitone b x₀ hA hstar

end Krylov.IsGalerkinIterate
