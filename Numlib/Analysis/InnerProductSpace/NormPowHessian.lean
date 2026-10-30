import Numlib.Analysis.InnerProductSpace.MinCurvature
import Numlib.Analysis.InnerProductSpace.NormPowIteratedFDeriv

/-!
# First and second derivatives of `‖s‖^r`

Explicit formulas for the gradient and the Hessian of `s ↦ ‖s‖ ^ r` on a real inner product space,
the regularization terms `σ/(p+1)! ‖s‖^{p+1}` of adaptive-regularization models
([cartis2022evaluation], (2.4.1), (3.3.1), (4.1.2)).

## Main statements

* `fderiv_norm_rpow_apply`: for `r > 1`, `D(‖·‖^r)(s)[v] = r ‖s‖^{r-2} ⟪s, v⟫` at every `s`
  (read as `0` at `s = 0`), and `norm_fderiv_norm_rpow`: its norm is `r ‖s‖^{r-1}`.
* `iteratedFDeriv_two_norm_rpow_apply`: for `s ≠ 0`,
  `D²(‖·‖^r)(s)[u, v] = r ‖s‖^{r-2} ⟪u, v⟫ + r (r - 2) ‖s‖^{r-4} ⟪s, u⟫ ⟪s, v⟫`; at the origin the
  Hessian is `0` for `r > 2` (`iteratedFDeriv_two_norm_rpow_zero`) and `2 ⟪u, v⟫` for `r = 2`
  (`iteratedFDeriv_two_norm_rpow_two_apply`); `‖·‖^r` is `C²` for `r ≥ 2`
  (`contDiff_two_norm_rpow`). For `r = 3` the Hessian of `σ/6 ‖s‖³` is `σ/2 (‖s‖ I + s sᵀ/‖s‖)`.
* `iteratedFDeriv_two_norm_rpow_bounds`: for `r ≥ 2`,
  `0 ≤ D²(‖·‖^r)(s)[d, d] ≤ r (r - 1) ‖s‖^{r-2} ‖d‖²`, with equality on the right for `d = s`;
  the Hessian has operator norm `r (r - 1) ‖s‖^{r-2}` (`norm_iteratedFDeriv_normRpow`), which is the
  book's (3.3.28) `max_{‖d‖=1} ⟨∇²(‖s‖³) d, d⟩ = 6 ‖s‖` for `r = 3`; in terms of the least
  curvature, `minCurvature_neg_iteratedFDeriv_two_norm_rpow`.

All higher orders are in `Numlib.Analysis.InnerProductSpace.NormPowIteratedFDeriv`.
-/

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The derivative of `‖·‖^r`** ([cartis2022evaluation], (3.3.2)): for `r > 1` and all `s, v`,
`D(‖·‖^r)(s)[v] = r ‖s‖^{r-2} ⟪s, v⟫`, i.e. the gradient is `r ‖s‖^{r-2} s` (which is `0` at
`s = 0`). -/
theorem fderiv_norm_rpow_apply {r : ℝ} (hr : 1 < r) (s v : E) :
    fderiv ℝ (fun s : E ↦ ‖s‖ ^ r) s v = r * ‖s‖ ^ (r - 2) * ⟪s, v⟫ := by
  rw [(hasFDerivAt_norm_rpow s hr).fderiv]
  simp

/-- The gradient of `‖·‖^r` has norm `r ‖s‖^{r-1}`, for `r > 1` and every `s`. -/
theorem norm_fderiv_norm_rpow {r : ℝ} (hr : 1 < r) (s : E) :
    ‖fderiv ℝ (fun s : E ↦ ‖s‖ ^ r) s‖ = r * ‖s‖ ^ (r - 1) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [(hasFDerivAt_norm_rpow (0 : E) hr).fderiv]
    simp [Real.zero_rpow (by linarith : r - 1 ≠ 0)]
  · rw [norm_fderiv_norm_rpow_of_ne_zero hs, abs_of_pos (by linarith)]

/-- **The Hessian of `‖·‖^r` off the origin**: for every real `r` and `s ≠ 0`,
`D²(‖·‖^r)(s)[u, v] = r ‖s‖^{r-2} ⟪u, v⟫ + r (r - 2) ‖s‖^{r-4} ⟪s, u⟫ ⟪s, v⟫`. -/
theorem iteratedFDeriv_two_norm_rpow_apply (r : ℝ) {s : E} (hs : s ≠ 0) (u v : E) :
    iteratedFDeriv ℝ 2 (fun s : E ↦ ‖s‖ ^ r) s ![u, v]
      = r * ‖s‖ ^ (r - 2) * ⟪u, v⟫ + r * (r - 2) * ‖s‖ ^ (r - 4) * ⟪s, u⟫ * ⟪s, v⟫ := by
  have hev : fderiv ℝ (fun s : E ↦ ‖s‖ ^ r)
      =ᶠ[nhds s] fun z ↦ (r * ‖z‖ ^ (r - 2)) • innerSL ℝ z :=
    Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hs) fun z hz ↦
      (hasFDerivAt_norm_rpow_of_ne_zero hz r).fderiv
  have hc : HasFDerivAt (fun z : E ↦ r * ‖z‖ ^ (r - 2))
      (r • ((r - 2) * ‖s‖ ^ (r - 2 - 2)) • innerSL ℝ s) s :=
    (hasFDerivAt_norm_rpow_of_ne_zero hs (r - 2)).const_mul r
  have hd : HasFDerivAt (fun z : E ↦ (r * ‖z‖ ^ (r - 2)) • innerSL ℝ z) _ s :=
    hc.smul (innerSL ℝ).hasFDerivAt
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq, hd.fderiv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  rw [show r - 2 - 2 = r - 4 by ring, show (innerSL ℝ u) v = ⟪u, v⟫ from rfl]
  ring

/-- For `r > 2` the Hessian of `‖·‖^r` vanishes at the origin. -/
theorem iteratedFDeriv_two_norm_rpow_zero {r : ℝ} (hr : 2 < r) :
    iteratedFDeriv ℝ 2 (fun s : E ↦ ‖s‖ ^ r) 0 = 0 :=
  iteratedFDeriv_normRpow_zero (by exact_mod_cast hr)

/-- For `r = 2` the Hessian of `‖·‖^r = ⟪·, ·⟫` is `2 ⟪u, v⟫` at every point. -/
theorem iteratedFDeriv_two_norm_rpow_two_apply (s u v : E) :
    iteratedFDeriv ℝ 2 (fun s : E ↦ ‖s‖ ^ (2 : ℝ)) s ![u, v] = 2 * ⟪u, v⟫ := by
  have hf : fderiv ℝ (fun s : E ↦ ‖s‖ ^ (2 : ℝ)) = fun z ↦ (2 : ℝ) • innerSL ℝ z := by
    funext z
    rw [(hasFDerivAt_norm_rpow z one_lt_two).fderiv]
    simp
  rw [iteratedFDeriv_two_apply, hf]
  have hd : HasFDerivAt (fun z : E ↦ (2 : ℝ) • innerSL ℝ z) ((2 : ℝ) • innerSL ℝ) s :=
    (innerSL ℝ).hasFDerivAt.const_smul (2 : ℝ)
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- For `r ≥ 2`, `‖·‖^r` is `C²` on the whole space. -/
theorem contDiff_two_norm_rpow {r : ℝ} (hr : 2 ≤ r) :
    ContDiff ℝ 2 (fun s : E ↦ ‖s‖ ^ r) := by
  rcases hr.eq_or_lt with rfl | hr
  · have h := contDiff_norm_pow_of_even (E := E) (r := 2) even_two
    rw [NormPowIteratedFDeriv.norm_pow_eq_normRpow] at h
    exact h.of_le (by exact_mod_cast le_top)
  · exact contDiff_normRpow_of_lt (by exact_mod_cast hr)

/-- **Bounds on the Hessian of `‖·‖^r`** for `r ≥ 2`:
`0 ≤ D²(‖·‖^r)(s)[d, d] ≤ r (r - 1) ‖s‖^{r-2} ‖d‖²`, with equality on the right for `d = s`
(`iteratedFDeriv_normRpow_apply_self`). Hence the Hessian is positive semidefinite with operator
norm `r (r - 1) ‖s‖^{r-2}` (`norm_iteratedFDeriv_normRpow`). -/
theorem iteratedFDeriv_two_norm_rpow_bounds {r : ℝ} (hr : 2 ≤ r) (s d : E) :
    0 ≤ iteratedFDeriv ℝ 2 (fun s : E ↦ ‖s‖ ^ r) s ![d, d] ∧
      iteratedFDeriv ℝ 2 (fun s : E ↦ ‖s‖ ^ r) s ![d, d]
        ≤ r * (r - 1) * ‖s‖ ^ (r - 2) * ‖d‖ ^ 2 := by
  rcases eq_or_ne s 0 with rfl | hs
  · rcases hr.eq_or_lt with rfl | hr'
    · rw [iteratedFDeriv_two_norm_rpow_two_apply, real_inner_self_eq_norm_sq]
      simp only [norm_zero, sub_self, Real.rpow_zero]
      constructor <;> nlinarith [sq_nonneg ‖d‖]
    · rw [iteratedFDeriv_two_norm_rpow_zero hr', norm_zero, Real.zero_rpow (by linarith)]
      simp
  have hns : 0 < ‖s‖ := norm_pos_iff.2 hs
  rw [iteratedFDeriv_two_norm_rpow_apply r hs, real_inner_self_eq_norm_sq]
  have h4 : ‖s‖ ^ (r - 4) * ⟪s, d⟫ ^ 2 ≤ ‖s‖ ^ (r - 2) * ‖d‖ ^ 2 := by
    have hcs : ⟪s, d⟫ ^ 2 ≤ ‖s‖ ^ 2 * ‖d‖ ^ 2 := by
      rw [← mul_pow]
      exact sq_le_sq' (neg_le_of_abs_le (abs_real_inner_le_norm s d)) (real_inner_le_norm s d)
    have he : ‖s‖ ^ (r - 2) = ‖s‖ ^ (r - 4) * ‖s‖ ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hns]
      congr 1
      push_cast
      ring
    rw [he, mul_assoc]
    exact mul_le_mul_of_nonneg_left hcs (Real.rpow_nonneg hns.le _)
  have h0 : 0 ≤ ‖s‖ ^ (r - 4) * ⟪s, d⟫ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hns.le _) (sq_nonneg _)
  have hp : 0 ≤ ‖s‖ ^ (r - 2) * ‖d‖ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hns.le _) (sq_nonneg _)
  have hr0 : 0 ≤ r * (r - 2) := mul_nonneg (by linarith) (by linarith)
  constructor
  · nlinarith
  · nlinarith

/-- **The largest curvature of `‖·‖^r`** ([cartis2022evaluation], (3.3.28) for `r = 3`:
`max_{‖d‖=1} ⟨∇²(‖s‖³) d, d⟩ = 6 ‖s‖`): for `r ≥ 2` on a nonzero space,
`λ_min[-D²(‖·‖^r)(s)] = -r (r - 1) ‖s‖^{r-2}`. The bound is `iteratedFDeriv_two_norm_rpow_bounds`;
it is attained at `d = s/‖s‖`, or at any unit `d` when `s = 0`. -/
theorem minCurvature_neg_iteratedFDeriv_two_norm_rpow [Nontrivial E] {r : ℝ} (hr : 2 ≤ r)
    (s : E) :
    minCurvature (-iteratedFDeriv ℝ 2 (fun s : E ↦ ‖s‖ ^ r) s)
      = -(r * (r - 1) * ‖s‖ ^ (r - 2)) := by
  set A := iteratedFDeriv ℝ 2 (fun s : E ↦ ‖s‖ ^ r) s with hA
  refine le_antisymm ?_ ?_
  · -- attained at a unit vector
    obtain ⟨d, hd, hval⟩ : ∃ d : E, ‖d‖ = 1 ∧ A (fun _ ↦ d) = r * (r - 1) * ‖s‖ ^ (r - 2) := by
      rcases eq_or_ne s 0 with rfl | hs
      · obtain ⟨d, hd⟩ := exists_norm_eq E zero_le_one
        refine ⟨d, hd, ?_⟩
        rcases hr.eq_or_lt with rfl | hr'
        · rw [apply_diag_eq_vec, iteratedFDeriv_two_norm_rpow_two_apply,
            real_inner_self_eq_norm_sq, hd]
          norm_num
        · rw [hA, iteratedFDeriv_two_norm_rpow_zero hr', norm_zero, Real.zero_rpow (by linarith)]
          simp
      · refine ⟨‖s‖⁻¹ • s, ?_, ?_⟩
        · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hs)]
        · rw [iteratedFDeriv_normRpow_apply_unit r 2 hs, Fin.prod_univ_two]
          norm_num
    have h := minCurvature_le_apply (-A) hd
    rwa [neg_apply, hval] at h
  · rw [le_minCurvature_iff]
    intro d
    rw [neg_apply, apply_diag_eq_vec]
    have := (iteratedFDeriv_two_norm_rpow_bounds hr s d).2
    linarith
