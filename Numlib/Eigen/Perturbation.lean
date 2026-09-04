import Numlib.Analysis.NormedRing.CondNumber
import Numlib.InnerProductSpace.Coercive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Eigenvalue perturbation and a posteriori bounds

Residual bounds for approximate eigenpairs of symmetric operators (Saad-eig Cor 3.3, Lemma 3.2,
Thm 3.8–3.9 Kato–Temple; Meurant §2.1; Choi §2.4), Bauer–Fike for diagonalizable matrices
(Saad-eig Thm 3.6, Kress Problem 7.6), the backward error of an approximate eigenpair
(Saad-eig Prop 3.4), Bendixson (Saad Thm 1.35) and Rayleigh-quotient bounds.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- Residual bound (Saad-eig Cor 3.3): some eigenvalue lies within `‖A x - θ x‖ / ‖x‖` of `θ`. -/
theorem exists_hasEigenvalue_dist_le (θ : ℝ) {x : E} (hx : x ≠ 0) :
    ∃ μ : 𝕜, Module.End.HasEigenvalue A μ ∧ ‖μ - (θ : 𝕜)‖ ≤ ‖A x - (θ : 𝕜) • x‖ / ‖x‖ := by
  sorry

/-- Saad-eig Lemma 3.2: with `θ = re⟪A x, x⟫` (`‖x‖ = 1`) and `(α, β) ∋ θ` free of eigenvalues,
`(β - θ)(θ - α) ≤ ‖r‖²`. -/
theorem rayleigh_gap_le_norm_residual_sq {x : E} (hx : ‖x‖ = 1) {α β : ℝ}
    (hαβ : α < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < β)
    (hfree : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∉ Set.Ioo α β) :
    (β - RCLike.re (inner 𝕜 (A x) x)) * (RCLike.re (inner 𝕜 (A x) x) - α) ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 := by
  sorry

/-- Kato–Temple (Saad-eig Thm 3.8): if `(a, b)` contains the Rayleigh quotient `θ` and exactly
one eigenvalue `λ`, then `-‖r‖²/(θ - a) ≤ λ - θ ≤ ‖r‖²/(b - θ)`. -/
theorem kato_temple {x : E} (hx : ‖x‖ = 1) {a b : ℝ} {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ)
    (hab : a < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < b)
    (hμab : RCLike.re μ ∈ Set.Ioo a b)
    (hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → RCLike.re μ' ∈ Set.Ioo a b → μ' = μ) :
    -(‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / (RCLike.re (inner 𝕜 (A x) x) - a)) ≤
        RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ∧
      RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ≤
        ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / (b - RCLike.re (inner 𝕜 (A x) x)) := by
  sorry

/-- Saad-eig Cor 3.4: `|λ - θ| ≤ ‖r‖² / δ` with `δ` the gap from `θ` to the other eigenvalues. -/
theorem abs_sub_rayleigh_le_norm_residual_sq_div {x : E} (hx : ‖x‖ = 1) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → μ' ≠ μ →
      δ ≤ |RCLike.re μ' - RCLike.re (inner 𝕜 (A x) x)|)
    (hclose : |RCLike.re μ - RCLike.re (inner 𝕜 (A x) x)| ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖) :
    |RCLike.re μ - RCLike.re (inner 𝕜 (A x) x)| ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / δ := by
  sorry

/-- Rayleigh quotient bounds: `λmin ≤ re⟪A x, x⟫ / ‖x‖² ≤ λmax`. -/
theorem rayleigh_mem_Icc {lmin lmax : ℝ}
    (hspec : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax) {x : E}
    (hx : x ≠ 0) : RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax := by
  sorry

end LinearMap.IsSymmetric

/-- Backward error of an approximate eigenpair (Saad-eig Prop 3.4): the least `‖ΔA‖` with
`(A - ΔA) u = θ u` (`‖u‖ = 1`) is `‖A u - θ u‖`, attained by the rank-one `r uᴴ`. -/
theorem isLeast_eigen_backwardError (A : E →L[𝕜] E) {u : E} (hu : ‖u‖ = 1) (θ : 𝕜) :
    IsLeast {ε : ℝ | ∃ ΔA : E →L[𝕜] E, (A - ΔA) u = θ • u ∧ ‖ΔA‖ = ε} ‖A u - θ • u‖ := by
  sorry

/-- Bendixson (Saad Thm 1.35): the real part of every eigenvalue of a bounded operator lies
between the extreme eigenvalues of its symmetric part `H = (A + A†)/2`. -/
theorem re_hasEigenvalue_mem_Icc_of_symmetricPart {A H : E →ₗ[𝕜] E} {lmin lmax : ℝ}
    (hH : H.IsSymmetricBoundedBy lmin lmax)
    (hHA : ∀ x, RCLike.re (inner 𝕜 (H x) x) = RCLike.re (inner 𝕜 (A x) x)) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) : RCLike.re μ ∈ Set.Icc lmin lmax := by
  sorry

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Bauer–Fike (Saad-eig Thm 3.6, Kress Problem 7.6): for `A = X D X⁻¹` and `μ ∈ σ(A + ΔA)`,
`dist(μ, σ(A)) ≤ κ₂(X) ‖ΔA‖₂`. -/
theorem bauer_fike (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X) (ΔA : Matrix n n ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (X * Matrix.diagonal d * X⁻¹ + ΔA)) :
    ∃ i, ‖μ - d i‖ ≤ NormedRing.condNumber X * ‖ΔA‖ := by
  sorry

/-- Residual form of Bauer–Fike: for a unit approximate eigenpair `(θ, u)` of `A = X D X⁻¹`,
`dist(θ, σ(A)) ≤ κ₂(X) ‖A u - θ u‖`. -/
theorem bauer_fike_residual (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X)
    {u : EuclideanSpace ℂ n} (hu : ‖u‖ = 1) (θ : ℂ) :
    ∃ i, ‖θ - d i‖ ≤ NormedRing.condNumber X *
      ‖Matrix.toEuclideanLin (X * Matrix.diagonal d * X⁻¹) u - θ • u‖ := by
  sorry

/-- Gershgorin discs, union form (Saad-eig Thm 3.11, Kress Thm 7.7); Mathlib's
`eigenvalue_mem_ball` is the pointwise version. -/
theorem spectrum_subset_iUnion_closedBall (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ i, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) := by
  sorry

end Matrix
