import Numlib.LinearSolve.Projection.Optimality
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# One-dimensional projection processes

The projection step with `K = span {v}`, `L = span {w}` (Saad[^saad-iterative] (5.12)–(5.13)),
and its three classical instances, written with the residual `r = b - A x`: steepest descent
(`v = w = r`), minimal residual iteration (`v = r`, `w = A r`), and residual-norm steepest
descent (`v = A† r`, `w = A v`). Convergence: Kantorovich's inequality (Saad Lemma 5.8), the
steepest-descent rate (Saad Thm 5.9) and the minimal-residual rate (Saad Thm 5.10, valid for
bounded coercive operators on any inner product space).

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The real part of the sesquilinear form of a symmetric operator is symmetric. -/
theorem IsSymmetric.re_inner_comm {C : F →ₗ[𝕜] F} (hC : C.IsSymmetric) (w z : F) :
    RCLike.re (inner 𝕜 (C z) w) = RCLike.re (inner 𝕜 (C w) z) := by
  rw [hC z w, ← inner_conj_symm]
  exact RCLike.conj_re _

namespace IsSymmetricBoundedBy

/-- **Polarization**: for a symmetric operator the numerical radius controls the norm. If the
quadratic form of `C` lies in `[-d, d] ‖·‖²` then `‖C u‖ ≤ d ‖u‖`. This is the substitute for
the spectral theorem in all the estimates below. -/
theorem norm_apply_le {C : F →ₗ[𝕜] F} {d : ℝ} (hC : C.IsSymmetricBoundedBy (-d) d) (u : F) :
    ‖C u‖ ≤ d * ‖u‖ := by
  have hpol : ∀ w z : F, 4 * RCLike.re (inner 𝕜 (C w) z) ≤ 2 * d * (‖w‖ ^ 2 + ‖z‖ ^ 2) := by
    intro w z
    have h1 := hC.re_inner_le (w + z)
    have h2 := hC.le_re_inner (w - z)
    have e1 : RCLike.re (inner 𝕜 (C (w + z)) (w + z))
        = RCLike.re (inner 𝕜 (C w) w) + 2 * RCLike.re (inner 𝕜 (C w) z)
          + RCLike.re (inner 𝕜 (C z) z) := by
      simp only [map_add, inner_add_left, inner_add_right]
      rw [hC.isSymmetric.re_inner_comm w z]
      ring
    have e2 : RCLike.re (inner 𝕜 (C (w - z)) (w - z))
        = RCLike.re (inner 𝕜 (C w) w) - 2 * RCLike.re (inner 𝕜 (C w) z)
          + RCLike.re (inner 𝕜 (C z) z) := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      rw [hC.isSymmetric.re_inner_comm w z]
      ring
    rw [e1] at h1
    rw [e2] at h2
    have hd2 : d * (‖w + z‖ ^ 2 + ‖w - z‖ ^ 2) = d * (2 * (‖w‖ ^ 2 + ‖z‖ ^ 2)) := by
      rw [parallelogram_law_with_norm 𝕜 w z]
    linarith
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hu2 : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  have hd : 0 ≤ d := by
    have h1 := hC.le_re_inner u
    have h2 := hC.re_inner_le u
    nlinarith [h1, h2, hu2]
  rcases eq_or_ne (C u) 0 with h0 | h0
  · rw [h0, norm_zero]; positivity
  have hCu : 0 < ‖C u‖ := norm_pos_iff.2 h0
  have hkey := hpol u (((‖u‖ / ‖C u‖ : ℝ) : 𝕜) • C u)
  have hnormz : ‖((‖u‖ / ‖C u‖ : ℝ) : 𝕜) • C u‖ = ‖u‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (by positivity)]
    field_simp
  have hinnerz : RCLike.re (inner 𝕜 (C u) (((‖u‖ / ‖C u‖ : ℝ) : 𝕜) • C u)) = ‖u‖ * ‖C u‖ := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_mul, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
    field_simp
  rw [hnormz, hinnerz] at hkey
  nlinarith [hkey, hupos]

/-- The quadratic-form version of the operator inequality `(A - lmin)(lmax - A) ≥ 0`:
`‖A u‖² + lmin lmax ‖u‖² ≤ (lmin + lmax) re ⟪A u, u⟫`. -/
theorem norm_apply_sq_add_le {B : F →ₗ[𝕜] F} {lmin lmax : ℝ}
    (hB : B.IsSymmetricBoundedBy lmin lmax) (u : F) :
    ‖B u‖ ^ 2 + lmin * lmax * ‖u‖ ^ 2 ≤ (lmin + lmax) * RCLike.re (inner 𝕜 (B u) u) := by
  have hre : ∀ (r : ℝ) (v : F), RCLike.re ((r : 𝕜) * inner 𝕜 v v) = r * ‖v‖ ^ 2 := by
    intro r v
    rw [RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  have hC : (B - (((lmin + lmax) / 2 : ℝ) : 𝕜) • LinearMap.id :
      F →ₗ[𝕜] F).IsSymmetricBoundedBy (-((lmax - lmin) / 2)) ((lmax - lmin) / 2) := by
    refine ⟨fun v w => ?_, fun v => ?_, fun v => ?_⟩
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
      rw [hB.isSymmetric v w]
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub]
      rw [hre]
      linarith [hB.le_re_inner v]
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub]
      rw [hre]
      linarith [hB.re_inner_le v]
  have hnorm := norm_apply_le hC u
  have happ : (B - (((lmin + lmax) / 2 : ℝ) : 𝕜) • LinearMap.id : F →ₗ[𝕜] F) u
      = B u - (((lmin + lmax) / 2 : ℝ) : 𝕜) • u := rfl
  rw [happ] at hnorm
  have hsq : ‖B u - (((lmin + lmax) / 2 : ℝ) : 𝕜) • u‖ ^ 2
      ≤ ((lmax - lmin) / 2) ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg (B u - (((lmin + lmax) / 2 : ℝ) : 𝕜) • u), norm_nonneg u, hnorm]
  rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, norm_smul,
    RCLike.norm_ofReal, mul_pow, sq_abs] at hsq
  linarith

/-- `lmin ⟪B u, u⟫ ≤ ‖B u‖²` (the operator inequality `lmin B ≤ B²`). -/
theorem le_norm_apply_sq {B : F →ₗ[𝕜] F} {lmin lmax : ℝ} (hl : 0 ≤ lmin)
    (hB : B.IsSymmetricBoundedBy lmin lmax) (u : F) :
    lmin * RCLike.re (inner 𝕜 (B u) u) ≤ ‖B u‖ ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hcs : RCLike.re (inner 𝕜 (B u) u) ≤ ‖B u‖ * ‖u‖ := re_inner_le_norm _ _
  have h1 : lmin * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 (B u) u) := hB.le_re_inner u
  have h2 : lmin * ‖u‖ ≤ ‖B u‖ := by nlinarith
  nlinarith [norm_nonneg (B u)]

/-- `‖B u‖² ≤ lmax ⟪B u, u⟫` (the operator inequality `B² ≤ lmax B`). -/
theorem norm_apply_sq_le {B : F →ₗ[𝕜] F} {lmin lmax : ℝ} (hl : 0 ≤ lmin)
    (hB : B.IsSymmetricBoundedBy lmin lmax) (u : F) :
    ‖B u‖ ^ 2 ≤ lmax * RCLike.re (inner 𝕜 (B u) u) := by
  have h1 := hB.norm_apply_sq_add_le u
  have h2 := hB.re_inner_le u
  nlinarith [mul_nonneg hl (sub_nonneg.2 h2)]

end IsSymmetricBoundedBy

end LinearMap

namespace Projection

/-- One projection step onto `span {v}` orthogonally to `span {w}`:
`x ↦ x + (⟪r, w⟫ / ⟪A v, w⟫) v` with `r = b - A x` (Saad, *Iterative Methods*, (5.12)). -/
noncomputable def step1 (A : E →ₗ[𝕜] E) (b : E) (v w : E) (x : E) : E :=
  x + (inner 𝕜 w (b - A x) / inner 𝕜 w (A v)) • v

variable {A : E →ₗ[𝕜] E} {b : E}

theorem step1_isPetrovGalerkin (v w x : E) (h : inner 𝕜 w (A v) ≠ 0) :
    IsPetrovGalerkin A b x (𝕜 ∙ v) (𝕜 ∙ w) (step1 A b v w x) := by
  refine ⟨?_, ?_⟩
  · rw [step1, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right, step1, map_add, map_smul,
      show b - (A x + (inner 𝕜 w (b - A x) / inner 𝕜 w (A v)) • A v)
        = (b - A x) - (inner 𝕜 w (b - A x) / inner 𝕜 w (A v)) • A v from by abel,
      inner_sub_right, inner_smul_right]
    field_simp
    ring

/-- Steepest descent step (Saad, *Iterative Methods*, Alg 5.2): `v = w = r` with the residual
`r = b - A x`. -/
noncomputable def steepestDescentStep (A : E →ₗ[𝕜] E) (b : E) (x : E) : E :=
  step1 A b (b - A x) (b - A x) x

/-- Minimal residual iteration step (Saad, *Iterative Methods*, Alg 5.3): `v = r`, `w = A r`
with the residual `r = b - A x`. -/
noncomputable def minResStep (A : E →ₗ[𝕜] E) (b : E) (x : E) : E :=
  step1 A b (b - A x) (A (b - A x)) x

/-- Residual-norm steepest descent step (Saad, *Iterative Methods*, Alg 5.4): `v = A† r`,
`w = A v` with the residual `r = b - A x` and `A†` the adjoint of `A`. -/
noncomputable def residualNormSDStep [CompleteSpace E] (A : E →L[𝕜] E) (b : E) (x : E) : E :=
  step1 (A : E →ₗ[𝕜] E) b ((ContinuousLinearMap.adjoint A) (b - A x))
    (A ((ContinuousLinearMap.adjoint A) (b - A x))) x

/-- The steepest-descent and minimal-residual steps do nothing once the residual vanishes. -/
private theorem step1_of_residual_eq_zero {v w x : E} (h0 : b - A x = 0) (hv : v = b - A x) :
    step1 A b v w x = x := by
  rw [step1, hv, h0, smul_zero, add_zero]

theorem steepestDescentStep_isGalerkin (x : E) (hA : A.IsCoercive) :
    IsGalerkin A b x (𝕜 ∙ (b - A x)) (steepestDescentStep A b x) := by
  rcases eq_or_ne (b - A x) 0 with h0 | h0
  · rw [steepestDescentStep, step1_of_residual_eq_zero h0 rfl]
    exact ⟨by simp, by rw [h0]; exact Submodule.zero_mem _⟩
  · refine step1_isPetrovGalerkin (b - A x) (b - A x) x fun hcon => ?_
    have hpos := hA.inner_self_pos h0
    rw [inner_eq_zero_symm.1 hcon, map_zero] at hpos
    exact lt_irrefl 0 hpos

theorem minResStep_isMinRes (x : E) (hA : A.IsCoercive) :
    IsMinRes A b x (𝕜 ∙ (b - A x)) (minResStep A b x) := by
  have hmap : (𝕜 ∙ (b - A x)).map A = 𝕜 ∙ A (b - A x) := by
    rw [Submodule.map_span, Set.image_singleton]
  rcases eq_or_ne (b - A x) 0 with h0 | h0
  · rw [minResStep, step1_of_residual_eq_zero h0 rfl]
    refine ⟨by simp, fun y _ => ?_⟩
    rw [h0, norm_zero]
    exact norm_nonneg _
  · refine IsMinRes.iff_isPetrovGalerkin.2 ?_
    rw [hmap]
    refine step1_isPetrovGalerkin (b - A x) (A (b - A x)) x fun hcon => ?_
    exact h0 (hA.injective (by rw [map_zero]; exact inner_self_eq_zero.1 hcon))

/-- Kantorovich's inequality (Saad, *Iterative Methods*, Lemma 5.8): for symmetric coercive
`A` with spectrum in `[λmin, λmax]`,
`re⟪A x, x⟫ · re⟪A⁻¹ x, x⟫ ≤ (λmax + λmin)² / (4 λmax λmin) ‖x‖⁴`. -/
theorem kantorovich_inequality {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) (x : E) {y : E} (hy : A y = x) :
    RCLike.re (inner 𝕜 (A x) x) * RCLike.re (inner 𝕜 y x) ≤
      (lmax + lmin) ^ 2 / (4 * lmax * lmin) * ‖x‖ ^ 4 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hll : lmin ≤ lmax := by
    nlinarith [hA.le_re_inner x, hA.re_inner_le x, hx2]
  have hlmax : 0 < lmax := lt_of_lt_of_le hl hll
  have hAc : A.IsSymmetricCoercive := hA.isSymmetricCoercive hl
  -- transport `A` to the energy space, where it has the same quadratic-form bounds
  let A' : WithEnergy A hAc →ₗ[𝕜] WithEnergy A hAc :=
    (WithEnergy.equiv A hAc).toLinearMap ∘ₗ A ∘ₗ (WithEnergy.equiv A hAc).symm.toLinearMap
  have hA'app : ∀ u : E, A' (WithEnergy.equiv A hAc u) = WithEnergy.equiv A hAc (A u) :=
    fun _ => rfl
  have hinnerW : ∀ u v : E, inner 𝕜 (WithEnergy.equiv A hAc u) (WithEnergy.equiv A hAc v)
      = inner 𝕜 (A u) v := fun _ _ => rfl
  have hnormW : ∀ u : E, ‖WithEnergy.equiv A hAc u‖ ^ 2 = RCLike.re (inner 𝕜 (A u) u) := by
    intro u
    rw [WithEnergy.norm_equiv]
    exact hAc.energyNorm_sq u
  have hsq : ∀ u : E, RCLike.re (inner 𝕜 (A (A u)) u) = ‖A u‖ ^ 2 := by
    intro u
    rw [hA.isSymmetric (A u) u]
    exact inner_self_eq_norm_sq _
  have hsurj := (WithEnergy.equiv A hAc).surjective
  have hA'bound : A'.IsSymmetricBoundedBy lmin lmax := by
    refine ⟨fun v w => ?_, fun v => ?_, fun v => ?_⟩
    · obtain ⟨u, rfl⟩ := hsurj v
      obtain ⟨z, rfl⟩ := hsurj w
      rw [hA'app, hA'app, hinnerW, hinnerW]
      exact hA.isSymmetric (A u) z
    · obtain ⟨u, rfl⟩ := hsurj v
      rw [hA'app, hinnerW, hnormW, hsq]
      exact LinearMap.IsSymmetricBoundedBy.le_norm_apply_sq hl.le hA u
    · obtain ⟨u, rfl⟩ := hsurj v
      rw [hA'app, hinnerW, hnormW, hsq]
      exact LinearMap.IsSymmetricBoundedBy.norm_apply_sq_le hl.le hA u
  have hK1 := hA'bound.norm_apply_sq_add_le (WithEnergy.equiv A hAc y)
  rw [hA'app, hnormW, hnormW, hinnerW, hsq, hy] at hK1
  -- `hK1 : ‖x‖² + lmin lmax re⟪A y, y⟫ ≤ (lmin + lmax) re⟪A x, y⟫` after the substitutions
  have hβ : RCLike.re (inner 𝕜 x y) = RCLike.re (inner 𝕜 y x) := by
    rw [← inner_conj_symm y x]
    exact (RCLike.conj_re _).symm
  have hαnn : 0 ≤ RCLike.re (inner 𝕜 (A x) x) :=
    le_trans (by positivity) (hA.le_re_inner x)
  have hβnn : 0 ≤ RCLike.re (inner 𝕜 y x) := by
    rw [← hβ, ← hy]
    exact le_trans (by positivity) (hA.le_re_inner y)
  rw [hβ] at hK1
  have hnn : 0 ≤ RCLike.re (inner 𝕜 (A x) x) + lmin * lmax * RCLike.re (inner 𝕜 y x) :=
    add_nonneg hαnn (mul_nonneg (mul_nonneg hl.le hlmax.le) hβnn)
  have hsquare : (RCLike.re (inner 𝕜 (A x) x) + lmin * lmax * RCLike.re (inner 𝕜 y x)) ^ 2
      ≤ ((lmin + lmax) * ‖x‖ ^ 2) ^ 2 := by nlinarith [hK1, hnn]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hsquare,
    sq_nonneg (RCLike.re (inner 𝕜 (A x) x) - lmin * lmax * RCLike.re (inner 𝕜 y x))]

/-- Expansion of the energy norm along the steepest-descent line. -/
private theorem energyNorm_sub_smul_apply_sq (hAc : A.IsSymmetricCoercive) (d : E) (t : ℝ) :
    energyNorm A (d - (t : 𝕜) • A d) ^ 2
      = energyNorm A d ^ 2 - 2 * t * ‖A d‖ ^ 2
        + t ^ 2 * RCLike.re (inner 𝕜 (A (A d)) (A d)) := by
  have hsym : RCLike.re (inner 𝕜 (A (A d)) d) = ‖A d‖ ^ 2 := by
    rw [hAc.isSymmetric (A d) d]
    exact inner_self_eq_norm_sq _
  rw [hAc.energyNorm_sq, hAc.energyNorm_sq]
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul, map_sub,
    inner_self_eq_norm_sq]
  rw [hsym]
  ring

/-- Saad, *Iterative Methods*, Thm 5.9: steepest descent contracts the energy norm of the error
by the factor `(λmax - λmin)/(λmax + λmin)`. -/
theorem energyNorm_steepestDescentStep_le {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) {xstar : E} (hstar : A xstar = b) (x : E) :
    energyNorm A (xstar - steepestDescentStep A b x) ≤
      (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x) := by
  have hAc : A.IsSymmetricCoercive := hA.isSymmetricCoercive hl
  have hAd : A (xstar - x) = b - A x := by rw [map_sub, hstar]
  rcases eq_or_ne (b - A x) 0 with h0 | h0
  · have hd0 : xstar - x = 0 := by
      have h1 := hA.le_re_inner (xstar - x)
      rw [hAd, h0, inner_zero_left, map_zero] at h1
      have h2 : ‖xstar - x‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
    rw [steepestDescentStep, step1_of_residual_eq_zero h0 rfl, hd0]
    simp [energyNorm]
  have hrpos : 0 < ‖b - A x‖ := norm_pos_iff.2 h0
  have hr2 : (0 : ℝ) < ‖b - A x‖ ^ 2 := by positivity
  have hll : lmin ≤ lmax := by
    nlinarith [hA.le_re_inner (b - A x), hA.re_inner_le (b - A x), hr2]
  have hlmax : 0 < lmax := lt_of_lt_of_le hl hll
  have hspos : (0 : ℝ) < lmax + lmin := by linarith
  set q : ℝ := RCLike.re (inner 𝕜 (A (b - A x)) (b - A x)) with hqdef
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) (hA.le_re_inner (b - A x))
  have hself : inner 𝕜 (A (b - A x)) (b - A x) = (q : 𝕜) := by
    refine (RCLike.conj_eq_iff_re.1 ?_).symm
    rw [inner_conj_symm]
    exact (hA.isSymmetric (b - A x) (b - A x)).symm
  set a : ℝ := ‖b - A x‖ ^ 2 / q with hadef
  have hstep : steepestDescentStep A b x = x + (a : 𝕜) • (b - A x) := by
    rw [steepestDescentStep, step1]
    congr 2
    rw [inner_self_eq_norm_sq_to_K, ← hA.isSymmetric (b - A x) (b - A x), hself,
      ← RCLike.ofReal_pow, ← RCLike.ofReal_div]
  have herr : xstar - steepestDescentStep A b x = (xstar - x) - (a : 𝕜) • A (xstar - x) := by
    rw [hstep, hAd]; abel
  have hexp0 := energyNorm_sub_smul_apply_sq hAc (xstar - x) a
  rw [← herr, hAd, ← hqdef] at hexp0
  have hexp : energyNorm A (xstar - steepestDescentStep A b x) ^ 2
      = energyNorm A (xstar - x) ^ 2 - ‖b - A x‖ ^ 4 / q := by
    rw [hexp0, hadef]
    field_simp
    ring
  -- Kantorovich applied to the residual, whose preimage is the error
  have hkant := kantorovich_inequality hl hA (b - A x) hAd
  have hconj : RCLike.re (inner 𝕜 (xstar - x) (b - A x)) = energyNorm A (xstar - x) ^ 2 := by
    rw [hAc.energyNorm_sq, ← hAd, ← inner_conj_symm]
    exact RCLike.conj_re _
  rw [hconj, ← hqdef] at hkant
  have hkant' : 4 * lmax * lmin * (q * energyNorm A (xstar - x) ^ 2)
      ≤ ‖b - A x‖ ^ 4 * (lmax + lmin) ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * lmax * lmin)] at hkant
    nlinarith [hkant]
  have hfrac : 4 * lmax * lmin / (lmax + lmin) ^ 2 * energyNorm A (xstar - x) ^ 2
      ≤ ‖b - A x‖ ^ 4 / q := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hqpos]
    nlinarith [hkant']
  have hcoeff : ((lmax - lmin) / (lmax + lmin)) ^ 2
      = 1 - 4 * lmax * lmin / (lmax + lmin) ^ 2 := by
    field_simp
    ring
  have hcnn : 0 ≤ (lmax - lmin) / (lmax + lmin) := by
    apply div_nonneg <;> linarith
  have henn := energyNorm_nonneg A (xstar - x)
  have hsq : energyNorm A (xstar - steepestDescentStep A b x) ^ 2
      ≤ ((lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x)) ^ 2 := by
    rw [hexp, mul_pow, hcoeff]
    nlinarith [hfrac]
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (energyNorm_nonneg _ _), Real.sqrt_sq (mul_nonneg hcnn henn)] at hfin

/-- Saad, *Iterative Methods*, Thm 5.10: for a bounded operator with `c ‖x‖² ≤ re⟪A x, x⟫`, the
minimal residual iteration contracts the residual by the factor `√(1 - c² / ‖A‖²)`. -/
theorem norm_residual_minResStep_le {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) (b x : E) :
    ‖b - A (minResStep (A : E →ₗ[𝕜] E) b x)‖ ≤
      Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x‖ := by
  have hcoer : (A : E →ₗ[𝕜] E).IsCoercive := ⟨c, hc, hA⟩
  have hmin := minResStep_isMinRes (A := (A : E →ₗ[𝕜] E)) (b := b) x hcoer
  set θ : ℝ := c / ‖A‖ ^ 2 with hθ
  have hθnn : 0 ≤ θ := by positivity
  have hstep := hmin.min (x + (θ : 𝕜) • (b - A x))
    (by rw [add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hres : b - (A : E →ₗ[𝕜] E) (x + (θ : 𝕜) • (b - A x))
      = (b - A x) - (θ : 𝕜) • A (b - A x) := by
    simp only [map_add, map_smul]; abel
  rw [hres] at hstep
  have hRich := ContinuousLinearMap.norm_sub_smul_apply_sq_le hA hθnn (b - A x)
  have hcoeff : 1 - 2 * θ * c + θ ^ 2 * ‖A‖ ^ 2 = 1 - c ^ 2 / ‖A‖ ^ 2 := by
    rcases eq_or_ne ‖A‖ 0 with h | h
    · rw [hθ, h]; norm_num
    · rw [hθ]; field_simp; ring
  rw [hcoeff] at hRich
  have hsq : ‖b - (A : E →ₗ[𝕜] E) (minResStep (A : E →ₗ[𝕜] E) b x)‖ ^ 2
      ≤ (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x‖ ^ 2 := by
    refine le_trans ?_ hRich
    nlinarith [hstep, norm_nonneg (b - (A : E →ₗ[𝕜] E) (minResStep (A : E →ₗ[𝕜] E) b x)),
      norm_nonneg ((b - A x) - (θ : 𝕜) • A (b - A x))]
  simp only [ContinuousLinearMap.coe_coe] at hsq ⊢
  rcases eq_or_ne ‖b - A x‖ 0 with hr0 | hr0
  · rw [hr0] at hsq ⊢
    have hz : ‖b - A (minResStep (A : E →ₗ[𝕜] E) b x)‖ ^ 2 = 0 :=
      le_antisymm (by simpa using hsq) (sq_nonneg _)
    rw [pow_eq_zero_iff two_ne_zero |>.1 hz, mul_zero]
  · have hrpos : 0 < ‖b - A x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr0)
    have hR2 : (0 : ℝ) < ‖b - A x‖ ^ 2 := by positivity
    have hknn : 0 ≤ 1 - c ^ 2 / ‖A‖ ^ 2 := by
      nlinarith [hsq, sq_nonneg ‖b - A (minResStep (A : E →ₗ[𝕜] E) b x)‖, hR2]
    have hfin := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hknn, Real.sqrt_sq (norm_nonneg _)] at hfin

end Projection
