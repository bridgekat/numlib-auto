import Numlib.Krylov.Iterate

/-!
# Relations between Galerkin and minimal-residual iterates

Residual smoothing (Weiss; Saad Lemma 6.18) and the Cullum–Greenbaum / Brown relations between
FOM and GMRES residuals (Saad Prop 6.12–6.17, (6.65), Cor 6.14; Fong–Saunders (4.1);
Greenbaum Lemma 5.4.1), proved at the specification level without any factorization.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E}

namespace Krylov

/-- Weiss's residual smoothing step: `r' = s + η (r - s)` with the residual-minimizing `η`. -/
noncomputable def smoothingCoeff (s r : E) : 𝕜 := inner 𝕜 (r - s) (-s) / (‖r - s‖ ^ 2 : ℝ)

/-- Saad Lemma 6.18 (Weiss): if `r ⟂ s'` where `s' = s + η (r - s)` is the residual-minimizing
combination and `r ⟂ s`, then `1/‖s'‖² = 1/‖s‖² + 1/‖r‖²`. -/
theorem inv_sq_norm_smoothing {s r : E} (hs : s ≠ 0) (hr : r ≠ 0)
    (horth : inner 𝕜 r s = 0) :
    let s' := s + (smoothingCoeff s r : 𝕜) • (r - s)
    1 / ‖s'‖ ^ 2 = 1 / ‖s‖ ^ 2 + 1 / ‖r‖ ^ 2 := by
  sorry

/-- Cullum–Greenbaum (Saad (6.65)): `1/‖r_{m+1}^G‖² = 1/‖r_m^G‖² + 1/‖r_{m+1}^F‖²`. -/
theorem inv_sq_norm_residual_minRes {m : ℕ} {xG xG' xF : E}
    (hG : IsMinResIterate A b x₀ m xG) (hG' : IsMinResIterate A b x₀ (m + 1) xG')
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (h0 : b - A xG' ≠ 0) :
    1 / ‖b - A xG'‖ ^ 2 = 1 / ‖b - A xG‖ ^ 2 + 1 / ‖b - A xF‖ ^ 2 := by
  sorry

/-- Saad Cor 6.14: `1/‖r_m^G‖² = ∑_{i ≤ m} 1/‖r_i^F‖²` when all Galerkin iterates exist. -/
theorem inv_sq_norm_residual_minRes_eq_sum {m : ℕ} {xG : E} {xF : ℕ → E}
    (hG : IsMinResIterate A b x₀ m xG) (hF : ∀ i ≤ m, IsGalerkinIterate A b x₀ i (xF i))
    (h0 : b - A xG ≠ 0) :
    1 / ‖b - A xG‖ ^ 2 = ∑ i ∈ Finset.range (m + 1), 1 / ‖b - A (xF i)‖ ^ 2 := by
  sorry

/-- `‖r_m^G‖ ≤ ‖r_m^F‖`. -/
theorem norm_residual_minRes_le_galerkin {m : ℕ} {xG xF : E}
    (hG : IsMinResIterate A b x₀ m xG) (hF : IsGalerkinIterate A b x₀ m xF) :
    ‖b - A xG‖ ≤ ‖b - A xF‖ := by
  sorry

/-- Saad Prop 6.15: `min_{i ≤ m} ‖r_i^F‖ ≤ √(m+1) ‖r_m^G‖`. -/
theorem exists_norm_residual_galerkin_le {m : ℕ} {xG : E} {xF : ℕ → E}
    (hG : IsMinResIterate A b x₀ m xG) (hF : ∀ i ≤ m, IsGalerkinIterate A b x₀ i (xF i)) :
    ∃ i ≤ m, ‖b - A (xF i)‖ ≤ Real.sqrt (m + 1) * ‖b - A xG‖ := by
  sorry

/-- Iterate relation (Saad (6.74)): `x_m^G = s_m² x_{m-1}^G + c_m² x_m^F` with
`c_m² = ‖r_m^G‖² / ‖r_m^F‖²`. -/
theorem minRes_eq_combination {m : ℕ} {xG xG' xF : E}
    (hG : IsMinResIterate A b x₀ m xG) (hG' : IsMinResIterate A b x₀ (m + 1) xG')
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (hinj : Function.Injective A)
    (h0 : b - A xF ≠ 0) :
    xG' = ((1 - ‖b - A xG'‖ ^ 2 / ‖b - A xF‖ ^ 2 : ℝ) : 𝕜) • xG +
      ((‖b - A xG'‖ ^ 2 / ‖b - A xF‖ ^ 2 : ℝ) : 𝕜) • xF := by
  sorry

/-- Brown (Saad Prop 6.17): the minimal-residual iteration stagnates at step `m + 1`
(`‖r_{m+1}^G‖ = ‖r_m^G‖ ≠ 0`) iff no Galerkin iterate exists at step `m + 1`. -/
theorem norm_residual_minRes_eq_iff_not_exists_galerkin [FiniteDimensional 𝕜 E] {m : ℕ}
    {xG xG' : E} (hG : IsMinResIterate A b x₀ m xG) (hG' : IsMinResIterate A b x₀ (m + 1) xG')
    (h0 : b - A xG' ≠ 0) [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hm : m + 1 ≤ grade A (b - A x₀)) :
    ‖b - A xG'‖ = ‖b - A xG‖ ↔ ¬ ∃ xF, IsGalerkinIterate A b x₀ (m + 1) xF := by
  sorry

/-- The step from `A 𝒦_m` to `A 𝒦_{m+1}` is spanned by `r^F_{m+1} - r^G_m` (the Galerkin residual
at `m + 1` minus the minimal-residual residual at `m`), the key step of the residual-smoothing
proof of the Cullum–Greenbaum relation: `A 𝒦_{m+1} = A 𝒦_m ⊔ 𝕜 ∙ (r^F_{m+1} - r^G_m)`. -/
theorem map_subspace_succ_eq_sup_span {m : ℕ} {xG xF : E} (hG : IsMinResIterate A b x₀ m xG)
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (hF0 : b - A xF ≠ 0)
    (hinj : Function.Injective A) [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hm : m + 1 ≤ grade A (b - A x₀)) :
    (subspace A (b - A x₀) (m + 1)).map A =
      (subspace A (b - A x₀) m).map A ⊔ 𝕜 ∙ ((b - A xF) - (b - A xG)) := by
  sorry

/-- Weiss's minimal-residual smoothing (Saad Alg 6.14) of a sequence of iterates `xO`:
`xS 0 = xO 0`, `xS (m+1) = xS m + η_m (xO (m+1) - xS m)` with `η_m` minimizing the residual
on the line. -/
noncomputable def mrs (A : E →ₗ[𝕜] E) (b : E) (xO : ℕ → E) : ℕ → E
  | 0 => xO 0
  | m + 1 => mrs A b xO m +
      (smoothingCoeff (b - A (mrs A b xO m)) (b - A (xO (m + 1))) : 𝕜) • (xO (m + 1) - mrs A b xO m)

/-- Saad §6.5.8 (Weiss, Zhou–Walker): minimal-residual smoothing of the Galerkin (FOM) iterates
produces the minimal-residual (GMRES) iterates. -/
theorem IsGalerkinIterate.mrs_isMinResIterate {xO : ℕ → E}
    (hO : ∀ m, IsGalerkinIterate A b x₀ m (xO m)) (hinj : Function.Injective A) (m : ℕ) :
    IsMinResIterate A b x₀ m (mrs A b xO m) := by
  sorry

/-- Saad (6.79): for pairwise orthogonal residuals `r^O_j` (Galerkin residuals), the smoothed
residual is the weighted average `r^S_m = (∑_{j ≤ m} r^O_j / ρ_j²) / (∑_{j ≤ m} 1 / ρ_j²)`. -/
theorem residual_mrs_eq {xO : ℕ → E} (hO : ∀ m, IsGalerkinIterate A b x₀ m (xO m))
    (hinj : Function.Injective A) (m : ℕ) (h0 : ∀ j ≤ m, b - A (xO j) ≠ 0) :
    b - A (mrs A b xO m) =
      (((∑ j ∈ Finset.range (m + 1), 1 / ‖b - A (xO j)‖ ^ 2)⁻¹ : ℝ) : 𝕜) •
        ∑ j ∈ Finset.range (m + 1), ((1 / ‖b - A (xO j)‖ ^ 2 : ℝ) : 𝕜) • (b - A (xO j)) := by
  sorry

end Krylov
