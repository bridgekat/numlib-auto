import Numlib.Krylov.CR
import Numlib.Krylov.CG
import Numlib.LinearSolve.Perturbation

/-!
# Monotonicity properties of Krylov iterates on SPD systems (Fong–Saunders)

Specification-level versions of Fong–Saunders Thm 2.3–2.5 and Thm 3.1: for *any* sequence of
minimal-residual Krylov iterates of a symmetric coercive system (MINRES, CR, GMRES, …) started at
`x₀ = 0`, `‖x_k‖` is nondecreasing, `‖x* - x_k‖` and `‖x* - x_k‖_A` are nonincreasing, and the
normwise relative backward error is nonincreasing. Proved by identifying the iterates with the CR
iterates (`CR.isMinResIterate` + uniqueness) and using the sign lemma of `CR.lean`.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive) {b : E}

namespace Krylov.IsMinResIterate

include hA

/-- Minimal-residual iterates of an SPD system coincide with the CR iterates. -/
theorem eq_CR_iterate {x₀ : E} {k : ℕ} {x : E} (hx : IsMinResIterate A b x₀ k x) :
    x = (CR.iterate A b x₀ k).x := by
  sorry

/-- Fong–Saunders Thm 2.3: `‖x_k‖` is nondecreasing (`x₀ = 0`). -/
theorem norm_monotone {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b 0 k (x k)) :
    Monotone fun k => ‖x k‖ := by
  sorry

/-- Fong–Saunders Thm 2.4: `‖x* - x_k‖` is nonincreasing. -/
theorem norm_error_antitone {x₀ : E} {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b x₀ k (x k))
    {xstar : E} (hstar : A xstar = b) : Antitone fun k => ‖xstar - x k‖ := by
  sorry

/-- Fong–Saunders Thm 2.5: `‖x* - x_k‖_A` is nonincreasing. -/
theorem energyNorm_error_antitone {x₀ : E} {x : ℕ → E}
    (hx : ∀ k, IsMinResIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - x k) := by
  sorry

/-- Fong–Saunders Thm 3.1: the normwise relative backward error
`‖r_k‖ / (α ‖A‖ ‖x_k‖ + β ‖b‖)` is nonincreasing (`x₀ = 0`, `α ≥ 0`, `β > 0`). The
denominator is positive at every step, so no junk division occurs. -/
theorem backwardError_antitone {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b 0 k (x k))
    {normA α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) (hnormA : 0 ≤ normA) (hb : b ≠ 0) :
    Antitone fun k => ‖b - A (x k)‖ / (α * normA * ‖x k‖ + β * ‖b‖) := by
  sorry

/-- The special case `‖r_k‖ / ‖x_k‖` (Fong–Saunders (3.5) with `β = 0`), from step `1` on:
at `k = 0` the quotient `‖b‖ / ‖0‖` is a junk value, so the statement is on `Set.Ici 1`. -/
theorem norm_residual_div_norm_antitoneOn {x : ℕ → E}
    (hx : ∀ k, IsMinResIterate A b 0 k (x k)) (hb : b ≠ 0) :
    AntitoneOn (fun k => ‖b - A (x k)‖ / ‖x k‖) (Set.Ici 1) := by
  sorry

end Krylov.IsMinResIterate

namespace Krylov.IsGalerkinIterate

include hA

/-- Galerkin iterates of an SPD system coincide with the CG iterates. -/
theorem eq_CG_iterate {x₀ : E} {k : ℕ} {x : E} (hx : IsGalerkinIterate A b x₀ k x) :
    x = (CG.iterate A b x₀ k).x := by
  sorry

/-- Steihaug (Fong–Saunders Table 5.1, CG column): `‖x_k‖` is nondecreasing (`x₀ = 0`). -/
theorem norm_monotone {x : ℕ → E} (hx : ∀ k, IsGalerkinIterate A b 0 k (x k)) :
    Monotone fun k => ‖x k‖ := by
  sorry

/-- Hestenes–Stiefel Thm 6:3: `‖x* - x_k‖` is nonincreasing. -/
theorem norm_error_antitone {x₀ : E} {x : ℕ → E} (hx : ∀ k, IsGalerkinIterate A b x₀ k (x k))
    {xstar : E} (hstar : A xstar = b) : Antitone fun k => ‖xstar - x k‖ := by
  sorry

end Krylov.IsGalerkinIterate
