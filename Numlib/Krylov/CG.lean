import Numlib.Krylov.Lanczos
import Numlib.Krylov.Iterate

/-!
# The conjugate gradient recurrence (Hestenes–Stiefel)

`CG.step` is one step of the two-term CG recurrence
(Saad Alg 6.18, Atkinson–Han (5.6.2)/§9.4, Fong–Saunders Table 2.1, Meurant–Strakoš (3.2),
Choi Table 2.7). The main theorems: CG realises the Galerkin specification
(`CG.isGalerkinIterate`), the orthogonality invariants (Saad Prop 6.20), the identification of
CG residuals with Lanczos vectors (Saad (6.101)–(6.103), Meurant (3.4)), and the
Hestenes–Stiefel error identities and monotonicity results (HS Thm 6:1, 6:3; Steihaug).
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace CG

/-- State of the CG iteration: iterate, residual, search direction. -/
structure State (E : Type*) where
  x : E
  r : E
  p : E

/-- The CG step length `α = ⟪r, r⟫ / ⟪A p, p⟫`. -/
noncomputable def alpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.r s.r / inner 𝕜 (A s.p) s.p

/-- One CG step. -/
noncomputable def step (A : E →ₗ[𝕜] E) (s : State E) : State E :=
  let q := A s.p
  let α := alpha A s
  let r' := s.r - α • q
  let β : 𝕜 := inner 𝕜 r' r' / inner 𝕜 s.r s.r
  { x := s.x + α • s.p, r := r', p := r' + β • s.p }

/-- The CG direction update coefficient `β = ⟪r', r'⟫ / ⟪r, r⟫`. -/
noncomputable def beta (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (step A s).r (step A s).r / inner 𝕜 s.r s.r

/-- Initial state `x₀, r₀ = b - A x₀, p₀ = r₀`. -/
def init (A : E →ₗ[𝕜] E) (b x₀ : E) : State E := { x := x₀, r := b - A x₀, p := b - A x₀ }

/-- The `k`-th CG state. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A)^[k] (init A b x₀)

variable (A : E →ₗ[𝕜] E) (b x₀ : E)

@[simp] theorem iterate_zero : iterate A b x₀ 0 = init A b x₀ := rfl

theorem iterate_succ (k : ℕ) : iterate A b x₀ (k + 1) = step A (iterate A b x₀ k) := by
  sorry

/-- The state's residual field is the true residual. -/
theorem residual_eq (k : ℕ) : (iterate A b x₀ k).r = b - A (iterate A b x₀ k).x := by
  sorry

theorem step_x (s : State E) : (step A s).x = s.x + alpha A s • s.p := rfl

theorem step_r (s : State E) : (step A s).r = s.r - alpha A s • A s.p := rfl

variable {A} (hA : A.IsSymmetricCoercive)
include hA

/-- Well-definedness: `⟪A p_k, p_k⟫ > 0` as long as `r_k ≠ 0`. -/
theorem re_inner_apply_direction_pos {k : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) :
    0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p) := by
  sorry

/-- Once the residual vanishes the iteration is stationary. -/
theorem iterate_eq_of_residual_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) (j : ℕ) :
    iterate A b x₀ (k + j) = iterate A b x₀ k := by
  sorry

/-- Saad Prop 6.20 (i): residuals are mutually orthogonal. -/
theorem inner_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).r = 0 := by
  sorry

/-- Saad Prop 6.20 (ii): directions are `A`-conjugate. -/
theorem inner_apply_direction_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (A (iterate A b x₀ i).p) (iterate A b x₀ j).p = 0 := by
  sorry

/-- `⟪r_i, p_j⟫ = ‖r_i‖²` for `j ≥ i`… in the form `⟪r_i, p_j⟫ = 0` for `j < i`. -/
theorem inner_residual_direction_eq_zero {i j : ℕ} (h : j < i) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p = 0 := by
  sorry

theorem inner_residual_direction_eq {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p = (‖(iterate A b x₀ i).r‖ ^ 2 : ℝ) := by
  sorry

/-- `span {p_0, …, p_{k-1}} = span {r_0, …, r_{k-1}} = 𝒦_k(A, r₀)`. -/
theorem span_direction_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) k := by
  sorry

theorem span_residual_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).r) =
      subspace A (b - A x₀) k := by
  sorry

theorem iterate_sub_mem (k : ℕ) : (iterate A b x₀ k).x - x₀ ∈ subspace A (b - A x₀) k := by
  sorry

/-- CG realises the Galerkin specification (hence minimizes the energy-norm error). -/
theorem isGalerkinIterate (k : ℕ) : IsGalerkinIterate A b x₀ k (iterate A b x₀ k).x := by
  sorry

/-- CG residuals are the Lanczos vectors up to sign: `v_k = (-1)^k r_k / ‖r_k‖`
(Saad (6.101), Meurant (3.4)). -/
theorem arnoldi_vec_eq (k : ℕ) (hr : (iterate A b x₀ k).r ≠ 0) :
    Arnoldi.vec A (b - A x₀) k =
      ((-1 : 𝕜) ^ k * (‖(iterate A b x₀ k).r‖⁻¹ : ℝ)) • (iterate A b x₀ k).r := by
  sorry

/-- Termination: `r_k = 0` for `k ≥ grade` (CG is a direct method in `≤ n` steps). -/
theorem residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : grade A (b - A x₀) ≤ k) : (iterate A b x₀ k).r = 0 := by
  sorry

theorem residual_ne_zero_of_lt_grade [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : k < grade A (b - A x₀)) : (iterate A b x₀ k).r ≠ 0 := by
  sorry

section Errors

variable {xstar : E} (hstar : A xstar = b)
include hstar

/-- Hestenes–Stiefel Thm 6:1 / Meurant–Strakoš Thm 11:
`‖ε_k‖_A² - ‖ε_{k+1}‖_A² = α_k ‖r_k‖²`. -/
theorem energyNorm_error_sq_sub (k : ℕ) :
    energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 -
        energyNorm A (xstar - (iterate A b x₀ (k + 1)).x) ^ 2 =
      RCLike.re (alpha A (iterate A b x₀ k)) * ‖(iterate A b x₀ k).r‖ ^ 2 := by
  sorry

/-- `‖ε_k‖_A² = ∑_{j ≥ k} α_j ‖r_j‖²` (finite sum up to the grade). -/
theorem energyNorm_error_sq_eq_sum [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] (k : ℕ) :
    energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 =
      ∑ j ∈ Finset.Ico k (grade A (b - A x₀)),
        RCLike.re (alpha A (iterate A b x₀ j)) * ‖(iterate A b x₀ j).r‖ ^ 2 := by
  sorry

/-- Hestenes–Stiefel Thm 6:3 / Meurant–Strakoš Thm 12: the Euclidean error is nonincreasing. -/
theorem norm_error_antitone : Antitone fun k => ‖xstar - (iterate A b x₀ k).x‖ := by
  sorry

theorem energyNorm_error_antitone :
    Antitone fun k => energyNorm A (xstar - (iterate A b x₀ k).x) := by
  sorry

end Errors

/-- Steihaug: `‖x_k‖` is nondecreasing for CG started at `x₀ = 0`. -/
theorem norm_iterate_monotone : Monotone fun k => ‖(iterate A b 0 k).x‖ := by
  sorry

/-- `⟪p_i, p_j⟫ ≥ 0` for CG on SPD systems (ingredient of Steihaug's theorem). -/
theorem re_inner_direction_nonneg (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) := by
  sorry

section ThreeTerm

omit hA
variable (A)

/-! ### The three-term form (Saad §6.7.2, Alg 6.19)

`γ_m = ⟪r_m, r_m⟫ / ⟪A r_m, r_m⟫`, `ρ_0 = 1`,
`ρ_m = (1 - (γ_m/γ_{m-1}) (‖r_m‖²/‖r_{m-1}‖²) / ρ_{m-1})⁻¹`, and
`x_{m+1} = ρ_m (x_m + γ_m r_m) + (1 - ρ_m) x_{m-1}`,
`r_{m+1} = ρ_m (r_m - γ_m A r_m) + (1 - ρ_m) r_{m-1}` (6.96)–(6.98). -/

/-- `γ_m = ⟪r_m, r_m⟫ / ⟪A r_m, r_m⟫` (6.97). -/
noncomputable def gamma (m : ℕ) : 𝕜 :=
  inner 𝕜 (iterate A b x₀ m).r (iterate A b x₀ m).r /
    inner 𝕜 (A (iterate A b x₀ m).r) (iterate A b x₀ m).r

/-- `ρ_m` of (6.98), with `ρ_0 = 1`. -/
noncomputable def rho : ℕ → 𝕜
  | 0 => 1
  | m + 1 => (1 - gamma A b x₀ (m + 1) / gamma A b x₀ m *
      ((‖(iterate A b x₀ (m + 1)).r‖ ^ 2 / ‖(iterate A b x₀ m).r‖ ^ 2 : ℝ) : 𝕜) / rho m)⁻¹

variable {A}

/-- Saad (6.96): `x_{m+1} = ρ_m (x_m + γ_m r_m) + (1 - ρ_m) x_{m-1}` (with `x_{-1}` read as `x_0`,
harmless since `1 - ρ_0 = 0`), valid while `r_j ≠ 0` for `j ≤ m`. -/
theorem iterate_succ_eq_three_term (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    (iterate A b x₀ (m + 1)).x =
      rho A b x₀ m • ((iterate A b x₀ m).x + gamma A b x₀ m • (iterate A b x₀ m).r) +
        (1 - rho A b x₀ m) • (iterate A b x₀ (m - 1)).x := by
  sorry

/-- Saad (6.96) for the residuals: `r_{m+1} = ρ_m (r_m - γ_m A r_m) + (1 - ρ_m) r_{m-1}`. -/
theorem residual_succ_eq_three_term (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    (iterate A b x₀ (m + 1)).r =
      rho A b x₀ m • ((iterate A b x₀ m).r - gamma A b x₀ m • A (iterate A b x₀ m).r) +
        (1 - rho A b x₀ m) • (iterate A b x₀ (m - 1)).r := by
  sorry

/-- The iteration is stationary once the residual vanishes (Lean's `x / 0 = 0`). -/
theorem step_eq_self_of_residual_eq_zero (s : State E) (hr : s.r = 0) (hp : s.p = 0) :
    step A s = s := by
  sorry

theorem iterate_eq_of_residual_eq_zero' {k : ℕ} (hk : (iterate A b x₀ k).r = 0) (l : ℕ)
    (hl : k ≤ l) : iterate A b x₀ l = iterate A b x₀ k := by
  sorry

end ThreeTerm

end CG
