import Numlib.Conditioning.LinearSystem
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section01

/-!
# Quarteroni–Sacco–Saleri §4.6: stopping criteria

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §4.6, over the backbone `Numlib/Stationary/Basic` (the error and
increment recursions of the affine iteration, the a priori and a posteriori bounds of the
contraction case) and `Numlib/Conditioning/LinearSystem` (the residual–error relation through the
condition number).

## Conventions

The iteration is the linear method (4.2) of §4.1, `affineStep B f`, consistent with `A x = b` in
the sense of Definition 4.1 (`definition_4_1`), with solution `x = A⁻¹ b` and errors
`e⁽ᵏ⁾ = x⁽ᵏ⁾ - x`. Norms are the Euclidean norms of `EuclideanSpace ℝ (Fin n)`, written
`‖toLp 2 v‖`, and the spectral norm `‖·‖₂` of matrices (Mathlib's scoped
`Matrix.Norms.L2Operator`), which is the operator norm they induce; the backbone states the same
bounds on any normed space with the induced operator norm, so nothing depends on the choice. The
convergence factor `‖Bᵏ‖` and the average convergence rate `R_k(B)` are those of Definition 4.2
(`definition_4_2_factor`, `definition_4_2_rate`). The condition number `K(A) = ‖A‖₂ ‖A⁻¹‖₂` is
`NormedRing.condNumber A` in the spectral norm.

## Contents

* `norm_error_le_convergenceFactor`, `equation_4_69` — the first display of §4.6 and
  (4.68)–(4.69).
* `equation_4_71`, `equation_4_72`, `equation_4_72_apriori`, `increment_succ_le` — §4.6.1, the
  stopping test based on the increment.
* `residual_stopping_abs`, `residual_stopping_rel` — §4.6.2, the stopping test based on the
  residual.

(4.70) (`k_min ≃ -log ε / R(B)`) and the indicator (4.73) are heuristics — "should not be regarded
as an upper bound" — and Examples 4.11–4.12 are numerical; none is a node. The preconditioned
residual criterion `‖P⁻¹ r⁽ᵏ⁾‖ / ‖P⁻¹ r⁽⁰⁾‖ ≤ ε` is a criterion, not a result, and has no node.

## Readings

(4.69) is stated for `k ≥ 1` with `0 < ‖Bᵏ‖ < 1` and `0 < ε`, the conditions under which both
sides make sense (`R_k(B) > 0` and `log ε` finite); the book's "`‖Bᵏ‖ < 1` … amounts to requiring"
is the equivalence `‖Bᵏ‖ ≤ ε ↔ k ≥ -log ε / R_k(B)`. The increment ratio `c = δ_{k+1} / δ_k` of
§4.6.1 is a lower bound for `‖B‖` (`increment_succ_le`); the indicator (4.73) built from it is not
a bound and is not formalized.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}

/-- `‖x - y‖ = ‖y - x‖` under `WithLp.toLp 2`. -/
private theorem norm_toLp_sub_rev (x y : Fin n → ℝ) :
    ‖(toLp 2 (x - y) : EuclideanSpace ℝ (Fin n))‖ =
      ‖(toLp 2 (y - x) : EuclideanSpace ℝ (Fin n))‖ := by
  rw [← norm_neg, ← toLp_neg, neg_sub]

/-! ### The convergence factor and the number of iterations, (4.68)–(4.69) -/

/-- **The first display of §4.6.** From (4.4), `‖e⁽ᵏ⁾‖ / ‖e⁽⁰⁾‖ ≤ ‖Bᵏ‖`: the convergence factor
after `k` steps estimates the reduction of the error, `‖e⁽ᵏ⁾‖ ≤ ‖Bᵏ‖ ‖e⁽⁰⁾‖` (backbone
`Stationary.norm_step_iterate_sub_le`). -/
theorem norm_error_le_convergenceFactor (hc : definition_4_1 A b B f) (x₀ : Fin n → ℝ) (k : ℕ) :
    ‖(toLp 2 ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
        definition_4_2_factor B k * ‖(toLp 2 (x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ∧
      ‖(toLp 2 ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ /
        ‖(toLp 2 (x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤ definition_4_2_factor B k := by
  have h := Stationary.norm_step_iterate_sub_le (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B)
    (toLp 2 f) (toLp_fixed_of_consistent hc) (toLp 2 x₀) k
  rw [← toLp_affineStep_iterate, ← toLp_sub, ← toLp_sub, ← map_pow, l2_opNorm_toEuclideanCLM] at h
  exact ⟨h, div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) h⟩

/-- **(4.68)–(4.69).** The iteration is continued until the error has been reduced by a factor
`ε < 1`, `‖e⁽ᵏ⁾‖ ≤ ε ‖e⁽⁰⁾‖` (4.68), which holds as soon as `‖Bᵏ‖ ≤ ε`; and for `k ≥ 1` with
`0 < ‖Bᵏ‖ < 1` and `ε > 0`, the condition `‖Bᵏ‖ ≤ ε` amounts to `k ≥ -log ε / R_k(B)` (4.69),
`R_k(B) = -(1/k) log ‖Bᵏ‖` being the average convergence rate of Definition 4.2. -/
theorem equation_4_69 (hc : definition_4_1 A b B f) (x₀ : Fin n → ℝ) {k : ℕ} {ε : ℝ} :
    (definition_4_2_factor B k ≤ ε →
        ‖(toLp 2 ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
          ε * ‖(toLp 2 (x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖) ∧
      (k ≠ 0 → 0 < definition_4_2_factor B k → definition_4_2_factor B k < 1 → 0 < ε →
        (definition_4_2_factor B k ≤ ε ↔ -Real.log ε / definition_4_2_rate B k ≤ k)) := by
  refine ⟨fun hε => (norm_error_le_convergenceFactor hc x₀ k).1.trans
    (mul_le_mul_of_nonneg_right hε (norm_nonneg _)), fun hk h0 h1 hε => ?_⟩
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hlog : Real.log (definition_4_2_factor B k) < 0 := Real.log_neg h0 h1
  have hR : 0 < definition_4_2_rate B k := by
    rw [definition_4_2_rate, neg_mul, neg_pos]
    exact mul_neg_of_pos_of_neg (one_div_pos.mpr hk') hlog
  rw [div_le_iff₀ hR, definition_4_2_rate, definition_4_2_factor, show
    (k : ℝ) * (-(1 / k : ℝ) * Real.log ‖B ^ k‖) = -Real.log ‖B ^ k‖ by field_simp,
    neg_le_neg_iff]
  exact (Real.log_le_log_iff h0 hε).symm

/-! ### §4.6.1 A stopping test based on the increment -/

/-- **(4.71).** From the error recursion `e⁽ᵏ⁺¹⁾ = B e⁽ᵏ⁾` of (4.4), `‖e⁽ᵏ⁺¹⁾‖ ≤ ‖B‖ ‖e⁽ᵏ⁾‖`. -/
theorem equation_4_71 (hc : definition_4_1 A b B f) (x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep B f)^[k + 1] x₀ - A⁻¹ *ᵥ b = B *ᵥ ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) ∧
      ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
        ‖B‖ * ‖(toLp 2 ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ := by
  have h : (affineStep B f)^[k + 1] x₀ - A⁻¹ *ᵥ b = B *ᵥ ((affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b) := by
    rw [equation_4_4 hc, equation_4_4 hc, pow_succ', ← mulVec_mulVec]
  refine ⟨h, ?_⟩
  rw [h, ← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM]
  exact ContinuousLinearMap.le_opNorm _ _

/-- **(4.72), the a posteriori increment test.** If `‖B‖ < 1` then
`‖x - x⁽ᵏ⁺¹⁾‖ ≤ ‖B‖ / (1 - ‖B‖) ‖x⁽ᵏ⁺¹⁾ - x⁽ᵏ⁾‖`: the triangle inequality in (4.71),
`‖e⁽ᵏ⁺¹⁾‖ ≤ ‖B‖ (‖e⁽ᵏ⁺¹⁾‖ + ‖x⁽ᵏ⁺¹⁾ - x⁽ᵏ⁾‖)` (backbone `Stationary.norm_iterate_sub_le'`). -/
theorem equation_4_72 (hc : definition_4_1 A b B f) (hB : ‖B‖ < 1) (x₀ : Fin n → ℝ) (k : ℕ) :
    ‖(toLp 2 (A⁻¹ *ᵥ b - (affineStep B f)^[k + 1] x₀) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖B‖ / (1 - ‖B‖) *
        ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) :
          EuclideanSpace ℝ (Fin n))‖ := by
  have hG : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B‖ < 1 := by rwa [l2_opNorm_toEuclideanCLM]
  have h := Stationary.norm_iterate_sub_le' (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f) hG
    (toLp_fixed_of_consistent hc) (toLp 2 x₀) k
  rw [← toLp_affineStep_iterate, ← toLp_affineStep_iterate, ← toLp_sub, ← toLp_sub,
    l2_opNorm_toEuclideanCLM] at h
  rw [norm_toLp_sub_rev (A⁻¹ *ᵥ b)]
  exact h

/-- **The display after (4.72), the a priori form.** If `‖B‖ < 1` then
`‖x - x⁽ᵏ⁺¹⁾‖ ≤ ‖B‖ᵏ⁺¹ / (1 - ‖B‖) ‖x⁽¹⁾ - x⁽⁰⁾‖`, which estimates the number of iterations needed
to reach a given tolerance (backbone `Stationary.norm_iterate_sub_le`). -/
theorem equation_4_72_apriori (hc : definition_4_1 A b B f) (hB : ‖B‖ < 1) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    ‖(toLp 2 (A⁻¹ *ᵥ b - (affineStep B f)^[k + 1] x₀) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖B‖ ^ (k + 1) / (1 - ‖B‖) *
        ‖(toLp 2 ((affineStep B f)^[1] x₀ - x₀) : EuclideanSpace ℝ (Fin n))‖ := by
  have hG : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B‖ < 1 := by rwa [l2_opNorm_toEuclideanCLM]
  have h := Stationary.norm_iterate_sub_le (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f) hG
    (toLp_fixed_of_consistent hc) (toLp 2 x₀) (k + 1)
  rw [← toLp_affineStep_iterate, ← toLp_affineStep, ← toLp_sub, ← toLp_sub,
    l2_opNorm_toEuclideanCLM] at h
  rw [norm_toLp_sub_rev (A⁻¹ *ᵥ b), Function.iterate_one]
  exact h

/-- **§4.6.1, the estimate of `‖B‖`.** The increments obey
`x⁽ᵏ⁺¹⁾ - x⁽ᵏ⁾ = B (x⁽ᵏ⁾ - x⁽ᵏ⁻¹⁾)`, hence `δ_{k+1} ≤ ‖B‖ δ_k` with `δ_{j+1} = ‖x⁽ʲ⁺¹⁾ - x⁽ʲ⁾‖`, so
that the ratio `c = δ_{k+1} / δ_k` is a lower bound for `‖B‖` (backbone
`Stationary.step_iterate_succ_sub`). The indicator `ε⁽ᵏ⁺¹⁾ = δ_{k+1}² / (δ_k - δ_{k+1})` of (4.73),
obtained by replacing `‖B‖` with `c` in (4.72), is a heuristic and is not formalized. -/
theorem increment_succ_le (B : Matrix (Fin n) (Fin n) ℝ) (f x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀ =
        B *ᵥ ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) ∧
      ‖(toLp 2 ((affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀) :
          EuclideanSpace ℝ (Fin n))‖ ≤
        ‖B‖ * ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) :
          EuclideanSpace ℝ (Fin n))‖ ∧
      ‖(toLp 2 ((affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀) :
          EuclideanSpace ℝ (Fin n))‖ /
        ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) :
          EuclideanSpace ℝ (Fin n))‖ ≤ ‖B‖ := by
  have hinc : ∀ j, (affineStep B f)^[j + 1] x₀ - (affineStep B f)^[j] x₀ =
      (B ^ j) *ᵥ (affineStep B f x₀ - x₀) := fun j => by
    have h := Stationary.step_iterate_succ_sub (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f)
      (toLp 2 x₀) j
    rw [← toLp_affineStep_iterate, ← toLp_affineStep_iterate, ← toLp_affineStep, ← toLp_sub,
      ← toLp_sub, ← map_pow, toEuclideanCLM_toLp] at h
    exact toLp_injective 2 h
  have h : (affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀ =
      B *ᵥ ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) := by
    rw [hinc (k + 1), hinc k, pow_succ', ← mulVec_mulVec]
  have hle : ‖(toLp 2 ((affineStep B f)^[k + 2] x₀ - (affineStep B f)^[k + 1] x₀) :
      EuclideanSpace ℝ (Fin n))‖ ≤
      ‖B‖ * ‖(toLp 2 ((affineStep B f)^[k + 1] x₀ - (affineStep B f)^[k] x₀) :
        EuclideanSpace ℝ (Fin n))‖ := by
    rw [h, ← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM]
    exact ContinuousLinearMap.le_opNorm _ _
  exact ⟨h, hle, div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) hle⟩

/-! ### §4.6.2 A stopping test based on the residual -/

/-- **§4.6.2, the first display.** For a nonsingular `A` and any vector `y` (an iterate), if the
residual satisfies `‖b - A y‖ ≤ ε` then `‖x - y‖ = ‖A⁻¹ b - y‖ = ‖A⁻¹ (b - A y)‖ ≤ ‖A⁻¹‖ ε`. -/
theorem residual_stopping_abs (hA : IsUnit A) (b y : Fin n → ℝ) {ε : ℝ}
    (hr : ‖(toLp 2 (b - A *ᵥ y) : EuclideanSpace ℝ (Fin n))‖ ≤ ε) :
    ‖(toLp 2 (A⁻¹ *ᵥ b - y) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖A⁻¹‖ * ε := by
  have h : A⁻¹ *ᵥ b - y = A⁻¹ *ᵥ (b - A *ᵥ y) := by
    rw [mulVec_sub, nonsing_inv_mulVec_mulVec hA]
  rw [h, ← toEuclideanCLM_toLp, ← l2_opNorm_toEuclideanCLM]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hr (norm_nonneg _))

/-- **§4.6.2, the normalized residual test.** For a nonsingular `A`, `b ≠ 0` and any vector `y`,
if `‖b - A y‖ / ‖b‖ ≤ ε` then the relative error is controlled by the condition number,
`‖x - y‖ / ‖x‖ ≤ K(A) ‖b - A y‖ / ‖b‖ ≤ ε K(A)`, with `K(A) = ‖A‖₂ ‖A⁻¹‖₂` (backbone
`relative_error_le_condNumber_mul_relative_residual` for the operator `x ↦ A x` on
`EuclideanSpace`). -/
theorem residual_stopping_rel (hA : IsUnit A) {b : Fin n → ℝ} (hb : b ≠ 0) (y : Fin n → ℝ)
    {ε : ℝ} (hr : ‖(toLp 2 (b - A *ᵥ y) : EuclideanSpace ℝ (Fin n))‖ /
      ‖(toLp 2 b : EuclideanSpace ℝ (Fin n))‖ ≤ ε) :
    ‖(toLp 2 (A⁻¹ *ᵥ b - y) : EuclideanSpace ℝ (Fin n))‖ /
        ‖(toLp 2 (A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
      NormedRing.condNumber A * ε := by
  have hu : IsUnit (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) := hA.map _
  set e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofUnit hu.unit with he_def
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A := by
    ext x; rfl
  have hκ : NormedRing.condNumber (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      NormedRing.condNumber A := by
    rw [he, NormedRing.condNumber, NormedRing.condNumber, ← toEuclideanCLM_ringInverse hA,
      l2_opNorm_toEuclideanCLM, l2_opNorm_toEuclideanCLM]
  have hx : e (toLp 2 (A⁻¹ *ᵥ b)) = toLp 2 b := by
    change toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (toLp 2 (A⁻¹ *ᵥ b)) = toLp 2 b
    rw [toEuclideanCLM_toLp, mulVec_nonsing_inv_mulVec hA]
  have hb' : (toLp 2 b : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    rwa [Ne, toLp_eq_zero]
  have h := relative_error_le_condNumber_mul_relative_residual e (y := toLp 2 y) hx hb'
  rw [hκ] at h
  have hAy : e (toLp 2 y) = toLp 2 (A *ᵥ y) := by
    change toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A (toLp 2 y) = toLp 2 (A *ᵥ y)
    rw [toEuclideanCLM_toLp]
  rw [hAy, ← toLp_sub, ← toLp_sub] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr (NormedRing.condNumber_nonneg _))

end QuarteroniSaccoSaleri.Chapter04
