import Numlib.Krylov.Arnoldi
import Numlib.InnerProductSpace.Coercive

/-!
# The symmetric Lanczos process

For symmetric `A` the Arnoldi coefficients are real and tridiagonal (Saad Thm 6.19 / Saad-eig
Thm 6.2), which gives the three-term recurrence
`A v_j = β_j v_{j-1} + α_j v_j + β_{j+1} v_{j+1}` (Saad Alg 6.15, Choi §2.1, Meurant §2.1,
Fong–Saunders §1.1). Indexing is `0`-based: `alpha A b j = ⟪v_j, A v_j⟫` and
`beta A b j = h_{j+1,j} = ‖w_j‖ ≥ 0`, so `A v_{j+1} = beta j • v_j + alpha (j+1) • v_{j+1} +
beta (j+1) • v_{j+2}`.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Arnoldi

variable {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (b : E)
include hA

theorem coeff_conj_of_isSymmetric (i j : ℕ) : coeff A b i j = starRingEnd 𝕜 (coeff A b j i) := by
  sorry

/-- Tridiagonal structure: `h i j = 0` for `j > i + 1`. -/
theorem coeff_eq_zero_of_isSymmetric {i j : ℕ} (h : i + 1 < j) : coeff A b i j = 0 := by
  sorry

theorem coeff_diag_re_of_isSymmetric (j : ℕ) :
    coeff A b j j = (RCLike.re (coeff A b j j) : 𝕜) := by
  sorry

end Arnoldi

namespace Lanczos

variable (A : E →ₗ[𝕜] E) (b : E)

/-- Diagonal Lanczos coefficient `α_j = ⟪v_j, A v_j⟫` (real for symmetric `A`). -/
noncomputable def alpha (j : ℕ) : ℝ := RCLike.re (Arnoldi.coeff A b j j)

/-- Off-diagonal Lanczos coefficient `β_{j+1} = h_{j+1,j} = ‖w_j‖ ≥ 0`. -/
noncomputable def beta (j : ℕ) : ℝ := ‖Arnoldi.w A b j‖

theorem beta_nonneg (j : ℕ) : 0 ≤ beta A b j := norm_nonneg _

theorem coe_beta (j : ℕ) : (beta A b j : 𝕜) = Arnoldi.coeff A b (j + 1) j := by
  sorry

/-- The real symmetric tridiagonal Lanczos matrix `T_m` (Saad (6.89)). -/
noncomputable def tridiag (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A b i
    else if (i : ℕ) + 1 = j then beta A b i
    else if (j : ℕ) + 1 = i then beta A b j
    else 0

/-- The `(m+1) × m` extended Lanczos matrix `T̄_m`. -/
noncomputable def tridiagExt (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A b i
    else if (i : ℕ) + 1 = j then beta A b i
    else if (j : ℕ) + 1 = i then beta A b j
    else 0

theorem tridiag_isTridiagonal (m : ℕ) : (tridiag A b m).IsTridiagonal := by
  sorry

theorem tridiag_isSymm (m : ℕ) : (tridiag A b m).IsSymm := by
  sorry

variable {A} (hA : A.IsSymmetric)
include hA

theorem coe_alpha (j : ℕ) : (alpha A b j : 𝕜) = Arnoldi.coeff A b j j := by
  sorry

/-- Three-term recurrence, first step: `A v_0 = α_0 v_0 + β_0 v_1`. -/
theorem apply_vec_zero :
    A (Arnoldi.vec A b 0) = (alpha A b 0 : 𝕜) • Arnoldi.vec A b 0 +
      (beta A b 0 : 𝕜) • Arnoldi.vec A b 1 := by
  sorry

/-- Three-term recurrence (Saad Alg 6.15, (6.87)):
`A v_{j+1} = β_j v_j + α_{j+1} v_{j+1} + β_{j+1} v_{j+2}`. -/
theorem apply_vec (j : ℕ) :
    A (Arnoldi.vec A b (j + 1)) =
      (beta A b j : 𝕜) • Arnoldi.vec A b j + (alpha A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 1) +
        (beta A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 2) := by
  sorry

/-- The algorithmic form of the recurrence: `w_{j+1} = A v_{j+1} - α_{j+1} v_{j+1} - β_j v_j`. -/
theorem w_succ_eq (j : ℕ) :
    Arnoldi.w A b (j + 1) = A (Arnoldi.vec A b (j + 1)) -
      (alpha A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 1) - (beta A b j : 𝕜) • Arnoldi.vec A b j := by
  sorry

theorem beta_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    beta A b j = 0 ↔ grade A b ≤ j + 1 := by
  sorry

/-- Rayleigh-quotient bound: `α_j ∈ [λmin, λmax]` when the eigenvalues of `A` are. -/
theorem alpha_mem_Icc {lmin lmax : ℝ} (hA' : A.IsSymmetricBoundedBy lmin lmax)
    [FiniteDimensional 𝕜 (fullSubspace A b)] {j : ℕ} (hj : j < grade A b) :
    alpha A b j ∈ Set.Icc lmin lmax := by
  sorry

/-- `H_m = T_m` for symmetric `A` (Saad Thm 6.19). -/
theorem hessenbergSq_eq_map_tridiag (m : ℕ) :
    Arnoldi.hessenbergSq A b m = (tridiag A b m).map (algebraMap ℝ 𝕜) := by
  sorry

theorem hessenberg_eq_map_tridiagExt (m : ℕ) :
    Arnoldi.hessenberg A b m = (tridiagExt A b m).map (algebraMap ℝ 𝕜) := by
  sorry

/-- `A V_m = V_m T_m + β_m v_m e_mᵀ` (Saad (6.91)), coordinate form, for `m ≥ 1`. -/
theorem apply_sum (m : ℕ) (y : Fin (m + 1) → 𝕜) :
    A (∑ j, y j • Arnoldi.vec A b j) =
      ∑ i : Fin (m + 1), ((tridiag A b (m + 1)).map (algebraMap ℝ 𝕜)).mulVec y i •
          Arnoldi.vec A b i +
        ((beta A b m : 𝕜) * y (Fin.last m)) • Arnoldi.vec A b (m + 1) := by
  sorry

/-- Termination (Choi (2.4)): at `ℓ = grade`, `A V_ℓ = V_ℓ T_ℓ` and `𝒦_ℓ` is invariant. -/
theorem apply_sum_grade [FiniteDimensional 𝕜 (fullSubspace A b)] (y : Fin (grade A b) → 𝕜) :
    A (∑ j, y j • Arnoldi.vec A b j) =
      ∑ i : Fin (grade A b),
        ((tridiag A b (grade A b)).map (algebraMap ℝ 𝕜)).mulVec y i • Arnoldi.vec A b i := by
  sorry

end Lanczos
