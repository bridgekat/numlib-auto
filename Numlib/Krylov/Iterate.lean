import Numlib.Krylov.Arnoldi
import Numlib.LinearSolve.Projection.Optimality
import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Krylov iterates: specifications

The canonical specifications of Krylov subspace methods for `A x = b` started at `x₀`, with
`r₀ = b - A x₀` and `𝒦_m = 𝒦_m(A, r₀)`:

* `Krylov.IsMinResIterate A b x₀ m x`: `x ∈ x₀ + 𝒦_m` minimizes the residual
  (GMRES, MINRES, CR, GCR, ORTHOMIN/ORTHODIR full versions, MINRES-QLP on nonsingular systems);
* `Krylov.IsGalerkinIterate A b x₀ m x`: `x ∈ x₀ + 𝒦_m`, `r ⟂ 𝒦_m`
  (FOM, CG, D-Lanczos, the Lanczos method);
* `Krylov.IsMinErrorIterate A xstar x₀ m x`: minimal Euclidean error `‖xstar - x‖` over
  `x₀ + A 𝒦_m(A, A (xstar - x₀))` (SYMMLQ; CGNE / Craig on `A Aᵀ`).

Polynomial characterizations (Saad Lemma 6.28, 6.31), residual structure (Prop 6.7), lucky
breakdown / exactness at the grade (Prop 6.10), and the minimum-norm property of Krylov solutions
of compatible symmetric systems (core of Choi Thm 2.25).
-/

open Polynomial Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- Minimal-residual Krylov iterate at step `m` (GMRES / MINRES / CR specification). -/
abbrev IsMinResIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinRes A b x₀ (subspace A (b - A x₀) m) x

/-- Galerkin Krylov iterate at step `m` (FOM / CG / Lanczos-method specification). -/
abbrev IsGalerkinIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsGalerkin A b x₀ (subspace A (b - A x₀) m) x

/-- Minimal-error Krylov iterate at step `m` (SYMMLQ / CGNE specification): minimal `‖x* - x‖`
over `x₀ + A 𝒦_m(A, r₀)` with `r₀ = A (x* - x₀)` (`= b - A x₀` when `A x* = b`). The target `x*`
is explicit so that the specification is meaningful for singular `A`. -/
abbrev IsMinErrorIterate (A : E →ₗ[𝕜] E) (xstar x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinError xstar x₀ ((subspace A (A (xstar - x₀)) m).map A) x

variable {A : E →ₗ[𝕜] E} {b x₀ : E} {m : ℕ} {x : E}

/-- Residual polynomials: for `x ∈ x₀ + 𝒦_m(A, r₀)` there is `p` with `deg p ≤ m`, `p 0 = 1`
and `b - A x = p(A) r₀`. -/
theorem exists_residual_poly (hx : x - x₀ ∈ subspace A (b - A x₀) m) :
    ∃ p : 𝕜[X], p.degree ≤ m ∧ p.eval 0 = 1 ∧ b - A x = aeval A p (b - A x₀) := by
  sorry

/-- Conversely every such `p` arises from some `x ∈ x₀ + 𝒦_m`. -/
theorem exists_mem_of_residual_poly (p : 𝕜[X]) (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    ∃ x, x - x₀ ∈ subspace A (b - A x₀) m ∧ b - A x = aeval A p (b - A x₀) := by
  sorry

/-- The residual of any `x ∈ x₀ + 𝒦_m` lies in `𝒦_{m+1}`. -/
theorem residual_mem_subspace_succ (hx : x - x₀ ∈ subspace A (b - A x₀) m) :
    b - A x ∈ subspace A (b - A x₀) (m + 1) := by
  sorry

section MinRes

/-- A minimal-residual iterate always exists. -/
theorem exists_isMinResIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) :
    ∃ x, IsMinResIterate A b x₀ m x := by
  sorry

theorem existsUnique_isMinResIterate_of_injective (hA : Function.Injective A) (b x₀ : E)
    (m : ℕ) : ∃! x, IsMinResIterate A b x₀ m x := by
  sorry

namespace IsMinResIterate

/-- Saad Lemma 6.31: `‖r_m‖ = min {‖p(A) r₀‖ : deg p ≤ m, p 0 = 1}`. -/
theorem norm_residual_eq_iInf (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ = ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1}, ‖aeval A p.1 (b - A x₀)‖ := by
  sorry

theorem norm_residual_le_norm_aeval (hx : IsMinResIterate A b x₀ m x) (p : 𝕜[X])
    (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) : ‖b - A x‖ ≤ ‖aeval A p (b - A x₀)‖ := by
  sorry

/-- Residual norms are nonincreasing in `m`. -/
theorem norm_residual_antitone {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b x₀ k (x k)) :
    Antitone fun k => ‖b - A (x k)‖ := by
  sorry

/-- Lucky breakdown (Saad Prop 6.10): at `m ≥ grade` the minimal-residual iterate is exact
provided `A` is injective on `𝒦_grade`. -/
theorem apply_eq_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : IsMinResIterate A b x₀ m x) (hm : grade A (b - A x₀) ≤ m)
    (hinj : Set.InjOn A (subspace A (b - A x₀) (grade A (b - A x₀)))) : A x = b := by
  sorry

/-- The residual is orthogonal to `A 𝒦_m` (Petrov–Galerkin with `L = A 𝒦_m`). -/
theorem residual_mem_orthogonal (hx : IsMinResIterate A b x₀ m x) :
    b - A x ∈ ((subspace A (b - A x₀) m).map A)ᗮ := by
  sorry

end IsMinResIterate

/-- Converse of lucky breakdown (Saad Prop 6.10 ⇐, P-6.13): an exact solution in `x₀ + 𝒦_m`
forces `grade ≤ m` (no injectivity needed: `r₀ = A q(A) r₀` gives the annihilator `1 - X q`). -/
theorem grade_le_of_apply_eq [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : x - x₀ ∈ subspace A (b - A x₀) m) (hAx : A x = b) : grade A (b - A x₀) ≤ m := by
  sorry

end MinRes

section MinError

/-- A minimal-error iterate always exists (projection of `x* - x₀` onto `A 𝒦_m`). -/
theorem exists_isMinErrorIterate (A : E →ₗ[𝕜] E) (xstar x₀ : E) (m : ℕ) :
    ∃ x, IsMinErrorIterate A xstar x₀ m x := by
  sorry

theorem IsMinErrorIterate.unique {xstar x' : E} (hx : IsMinErrorIterate A xstar x₀ m x)
    (hx' : IsMinErrorIterate A xstar x₀ m x') : x = x' := by
  sorry

/-- Errors of minimal-error iterates are nonincreasing in `m`. -/
theorem IsMinErrorIterate.norm_error_antitone {xstar : E} {x : ℕ → E}
    (hx : ∀ k, IsMinErrorIterate A xstar x₀ k (x k)) : Antitone fun k => ‖xstar - x k‖ := by
  sorry

end MinError

section Galerkin

theorem existsUnique_isGalerkinIterate_of_isCoercive (hA : A.IsCoercive) (b x₀ : E) (m : ℕ) :
    ∃! x, IsGalerkinIterate A b x₀ m x := by
  sorry

namespace IsGalerkinIterate

/-- Saad Lemma 6.28: for symmetric coercive `A`,
`‖x* - x_m‖_A = min {‖p(A) (x* - x₀)‖_A : deg p ≤ m, p 0 = 1}`. -/
theorem energyNorm_error_eq_iInf (hA : A.IsSymmetricCoercive) (hx : IsGalerkinIterate A b x₀ m x)
    {xstar : E} (hstar : A xstar = b) :
    energyNorm A (xstar - x) =
      ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1},
        energyNorm A (aeval A p.1 (xstar - x₀)) := by
  sorry

theorem energyNorm_error_le_energyNorm_aeval (hA : A.IsSymmetricCoercive)
    (hx : IsGalerkinIterate A b x₀ m x) {xstar : E} (hstar : A xstar = b) (p : 𝕜[X])
    (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    energyNorm A (xstar - x) ≤ energyNorm A (aeval A p (xstar - x₀)) := by
  sorry

/-- Saad Prop 6.7: the Galerkin residual is a multiple of the next Arnoldi vector. -/
theorem residual_mem_span (hx : IsGalerkinIterate A b x₀ m x) :
    b - A x ∈ 𝕜 ∙ Arnoldi.vec A (b - A x₀) m := by
  sorry

/-- Galerkin residuals at different steps are orthogonal. -/
theorem inner_residual_eq_zero {m' : ℕ} {x' : E} (hx : IsGalerkinIterate A b x₀ m x)
    (hx' : IsGalerkinIterate A b x₀ m' x') (h : m ≠ m') :
    inner 𝕜 (b - A x) (b - A x') = 0 := by
  sorry

/-- Galerkin iterates are exact at the grade (Saad Prop 5.6 + Prop 6.10). -/
theorem apply_eq_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : IsGalerkinIterate A b x₀ m x) (hm : grade A (b - A x₀) ≤ m) : A x = b := by
  sorry

/-- Energy-norm errors are nonincreasing in `m` for symmetric coercive `A`. -/
theorem energyNorm_error_antitone (hA : A.IsSymmetricCoercive) {x : ℕ → E}
    (hx : ∀ k, IsGalerkinIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - x k) := by
  sorry

end IsGalerkinIterate

end Galerkin

/-- Any exact Krylov solution of a compatible system with symmetric `A` is the minimum-norm
solution (abstract core of Choi Thm 2.25 / Thm 3.1): `𝒦_m(A, b) ≤ (ker A)ᗮ`. -/
theorem norm_le_of_apply_eq (hA : A.IsSymmetric) {b x : E} {m : ℕ} (hx : x ∈ subspace A b m)
    (hAx : A x = b) (y : E) (hy : A y = b) : ‖x‖ ≤ ‖y‖ := by
  sorry

theorem subspace_le_orthogonal_ker (hA : A.IsSymmetric) {b : E} (hb : b ∈ LinearMap.range A)
    (m : ℕ) : subspace A b m ≤ (LinearMap.ker A)ᗮ := by
  sorry

end Krylov
