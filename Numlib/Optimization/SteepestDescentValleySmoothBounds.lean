import Numlib.Optimization.SteepestDescentValleyScalarBounds
import Numlib.Analysis.Calculus.UniformDerivativeBounds

/-!
# Uniform genuine derivatives of the completed valley

The parameterized profile has uniformly bounded Fréchet derivatives through order two
for bounded nonnegative widths, even with unrestricted vertical coordinate. Outside a
fixed rectangle its actual jets agree locally with the width-only polynomial plateau.
-/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace Optimization.SteepestDescentValley

/-- The upper plateau formula only needs the two outward coordinates to be in their
respective constant branches; this also permits a neighborhood of a zero width. -/
theorem profile_plateau_of_coordinates {d z : ℝ} (hu : 1 ≤ z - d / 2)
    (hl : -z - d / 2 ≤ 0) : profile d z = 8 * d ^ 2 := by
  rw [profile, correction_of_one_le d hu, correction_of_nonpos d hl]
  ring

/-- Strictly outside the upper transition strip, every genuine joint derivative is the
corresponding derivative of the width-only plateau, including at width zero. -/
theorem iteratedFDeriv_profile_upper_plateau {d z : ℝ} (hu : 1 < z - d / 2)
    (hl : -z - d / 2 < 0) (j : ℕ) :
    iteratedFDeriv ℝ j (fun p : ℝ × ℝ => profile p.1 p.2) (d, z) =
      iteratedFDeriv ℝ j (fun p : ℝ × ℝ => 8 * p.1 ^ 2) (d, z) := by
  have hu' : ∀ᶠ p : ℝ × ℝ in 𝓝 (d, z), 1 < p.2 - p.1 / 2 :=
    (isOpen_lt continuous_const (continuous_snd.sub (continuous_fst.div_const 2))).mem_nhds hu
  have hl' : ∀ᶠ p : ℝ × ℝ in 𝓝 (d, z), -p.2 - p.1 / 2 < 0 :=
    (isOpen_lt (continuous_snd.neg.sub (continuous_fst.div_const 2)) continuous_const).mem_nhds hl
  have heq : (fun p : ℝ × ℝ => profile p.1 p.2) =ᶠ[𝓝 (d, z)]
      (fun p : ℝ × ℝ => 8 * p.1 ^ 2) :=
    (hu'.and hl').mono fun p hp => profile_plateau_of_coordinates hp.1.le hp.2.le
  exact (heq.iteratedFDeriv ℝ j).self_of_nhds

/-- The reflected exterior has the same actual polynomial jets. -/
theorem iteratedFDeriv_profile_lower_plateau {d z : ℝ} (hl : 1 < -z - d / 2)
    (hu : z - d / 2 < 0) (j : ℕ) :
    iteratedFDeriv ℝ j (fun p : ℝ × ℝ => profile p.1 p.2) (d, z) =
      iteratedFDeriv ℝ j (fun p : ℝ × ℝ => 8 * p.1 ^ 2) (d, z) := by
  have hl' : ∀ᶠ p : ℝ × ℝ in 𝓝 (d, z), 1 < -p.2 - p.1 / 2 :=
    (isOpen_lt continuous_const (continuous_snd.neg.sub (continuous_fst.div_const 2))).mem_nhds hl
  have hu' : ∀ᶠ p : ℝ × ℝ in 𝓝 (d, z), p.2 - p.1 / 2 < 0 :=
    (isOpen_lt (continuous_snd.sub (continuous_fst.div_const 2)) continuous_const).mem_nhds hu
  have heq : (fun p : ℝ × ℝ => profile p.1 p.2) =ᶠ[𝓝 (d, z)]
      (fun p : ℝ × ℝ => 8 * p.1 ^ 2) := by
    filter_upwards [hl', hu'] with p hp hq
    rw [← profile_reflection]
    exact profile_plateau_of_coordinates hp.le (by simpa using hq.le)
  exact (heq.iteratedFDeriv ℝ j).self_of_nhds

/-- A width-only polynomial has the same jets at every vertical coordinate. -/
theorem iteratedFDeriv_plateau_vertical (d z : ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j (fun p : ℝ × ℝ => 8 * p.1 ^ 2) (d, z) =
      iteratedFDeriv ℝ j (fun p : ℝ × ℝ => 8 * p.1 ^ 2) (d, 0) := by
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun p : ℝ × ℝ => 8 * p.1 ^ 2) j (0, z) (d, 0)
  simpa only [Prod.fst_add, Prod.fst_zero, add_zero, Prod.mk_add_mk, zero_add] using h.symm

/-- One constant, chosen before the width, bounds all actual joint Fréchet derivatives
through order two for widths in `[0,2]`, on the entire vertical line. -/
theorem exists_profile_derivative_bound :
    ∃ C > 0, ∀ j ≤ 2, ∀ d ∈ Icc (0 : ℝ) 2, ∀ z : ℝ,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => profile p.1 p.2) (d, z)‖ ≤ C := by
  let box := (Icc (0 : ℝ) 2) ×ˢ (Icc (-3 : ℝ) 3)
  have hc : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hp : ContDiff ℝ 2 (fun p : ℝ × ℝ => 8 * p.1 ^ 2) := by fun_prop
  have hb (j : ℕ) (hj : j ≤ 2) : ∃ B ≥ (0 : ℝ), ∀ p ∈ box,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => profile p.1 p.2) p‖ ≤ B ∧
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => 8 * p.1 ^ 2) p‖ ≤ B := by
    obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn
      (contDiff_profile.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn
    obtain ⟨D, hD⟩ := hc.exists_bound_of_continuousOn
      (hp.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn
    exact ⟨max 0 (max B D), le_max_left _ _, fun p hp =>
      ⟨(hB p hp).trans ((le_max_left _ _).trans (le_max_right _ _)),
       (hD p hp).trans ((le_max_right _ _).trans (le_max_right _ _))⟩⟩
  obtain ⟨B0, hB0, hb0⟩ := hb 0 (by omega)
  obtain ⟨B1, hB1, hb1⟩ := hb 1 (by omega)
  obtain ⟨B2, hB2, hb2⟩ := hb 2 (by omega)
  let C := 1 + B0 + B1 + B2
  have hC : 0 < C := by dsimp [C]; linarith
  have hb' (j : ℕ) (hj : j ≤ 2) (p : ℝ × ℝ) (hp : p ∈ box) :
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => profile p.1 p.2) p‖ ≤ C ∧
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => 8 * p.1 ^ 2) p‖ ≤ C := by
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    all_goals constructor
    all_goals first | exact (hb0 p hp).1.trans (by dsimp [C]; linarith)
                    | exact (hb0 p hp).2.trans (by dsimp [C]; linarith)
                    | exact (hb1 p hp).1.trans (by dsimp [C]; linarith)
                    | exact (hb1 p hp).2.trans (by dsimp [C]; linarith)
                    | exact (hb2 p hp).1.trans (by dsimp [C]; linarith)
                    | exact (hb2 p hp).2.trans (by dsimp [C]; linarith)
  refine ⟨C, hC, fun j hj d hd z => ?_⟩
  by_cases hz : z ∈ Icc (-3 : ℝ) 3
  · exact (hb' j hj (d, z) ⟨hd, hz⟩).1
  have heq : iteratedFDeriv ℝ j (fun p : ℝ × ℝ => profile p.1 p.2) (d, z) =
      iteratedFDeriv ℝ j (fun p : ℝ × ℝ => 8 * p.1 ^ 2) (d, z) := by
    simp only [mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · exact iteratedFDeriv_profile_lower_plateau (by linarith [hd.1, hd.2])
        (by linarith [hd.1]) j
    · exact iteratedFDeriv_profile_upper_plateau (by linarith [hd.2])
        (by linarith [hd.1]) j
  rw [heq, iteratedFDeriv_plateau_vertical]
  exact (hb' j hj (d, 0) ⟨hd, by norm_num⟩).2

/-- Each Euclidean coordinate is a contraction. -/
theorem norm_euclidean_proj_le_one (i : Fin 2) :
    ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [PiLp.proj_apply, one_mul] using PiLp.norm_apply_le x i

/-- A single constant bounds the genuine first and second Fréchet derivatives of the
actual moving coordinate map, uniformly over the finite parameters and the plane. -/
theorem exists_movingCoordinates_derivative_bound :
    ∃ D ≥ (1 : ℝ), ∀ (P : Parameters) (j : ℕ), 1 ≤ j → j ≤ 2 →
      ∀ p : EuclideanSpace ℝ (Fin 2),
        ‖iteratedFDeriv ℝ j
          (fun p : EuclideanSpace ℝ (Fin 2) =>
            (scalarWidth P (p 0), p 1 - scalarMidpoint P (p 0))) p‖ ≤ D ^ j := by
  obtain ⟨C, hC, hb⟩ := exists_width_midpoint_derivative_bound
  let D := C + 2
  have hD : 1 ≤ D := by dsimp [D]; linarith
  refine ⟨D, hD, fun P j hj hj2 p => ?_⟩
  have hj' : j = 1 ∨ j = 2 := by omega
  have h0 : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) => p 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  have h1 : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) => p 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff
  have hw := (contDiff_scalarWidth P).comp h0
  have hm := (contDiff_scalarMidpoint P).comp h0
  simp only [Function.comp_def] at hw hm
  have hwp : ‖iteratedFDeriv ℝ j
      (fun p : EuclideanSpace ℝ (Fin 2) => scalarWidth P (p 0)) p‖ ≤ C := by
    have h := norm_iteratedFDeriv_scalar_pullback (contDiff_scalarWidth P)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) (norm_euclidean_proj_le_one 0) hj2 p
    simp only [Function.comp_def, EuclideanSpace.coe_proj] at h
    exact h.trans (hb P j hj' _).1
  have hmp : ‖iteratedFDeriv ℝ j
      (fun p : EuclideanSpace ℝ (Fin 2) => scalarMidpoint P (p 0)) p‖ ≤ C := by
    have h := norm_iteratedFDeriv_scalar_pullback (contDiff_scalarMidpoint P)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) (norm_euclidean_proj_le_one 0) hj2 p
    simp only [Function.comp_def, EuclideanSpace.coe_proj] at h
    exact h.trans (hb P j hj' _).2
  have hip : ‖iteratedFDeriv ℝ j
      (fun p : EuclideanSpace ℝ (Fin 2) => p 1) p‖ ≤ 1 := by
    have hi : ContDiff ℝ 2 (fun t : ℝ => t) := contDiff_id
    have h := norm_iteratedFDeriv_scalar_pullback hi
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) (norm_euclidean_proj_le_one 1) hj2 p
    simp only [Function.comp_def, EuclideanSpace.coe_proj] at h
    apply h.trans
    rcases hj' with rfl | rfl <;> norm_num [iteratedDeriv_succ]
  rw [iteratedFDeriv_prodMk hw.contDiffAt (h1.sub hm).contDiffAt
    (by exact_mod_cast hj2), ContinuousMultilinearMap.opNorm_prod]
  refine (max_le (hwp.trans (show C ≤ 1 + C by linarith)) ?_).trans ?_
  · rw [fun_iteratedFDeriv_sub_apply (h1.of_le (by exact_mod_cast hj2)).contDiffAt
      (hm.of_le (by exact_mod_cast hj2)).contDiffAt]
    exact (norm_sub_le _ _).trans (add_le_add hip hmp)
  · have hDC : 1 + C ≤ D := by dsimp [D]; linarith
    exact hDC.trans (le_self_pow₀ hD (by omega))

/-- The moving valley term has a uniform genuine first and second derivative bound,
with all dependence of both moving strip boundaries included by composition. -/
theorem exists_euclideanMovingProfile_derivative_bound :
    ∃ K > 0, ∀ (P : Parameters) (j : ℕ), 1 ≤ j → j ≤ 2 →
      ∀ p : EuclideanSpace ℝ (Fin 2),
        ‖iteratedFDeriv ℝ j (euclideanMovingProfile P) p‖ ≤ K := by
  obtain ⟨C, hC, hbC⟩ := exists_profile_derivative_bound
  obtain ⟨D, hD, hbD⟩ := exists_movingCoordinates_derivative_bound
  let K := 2 * C * D ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun P j hj hj2 p => ?_⟩
  have h0 : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) => p 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  have h1 : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) => p 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff
  have hw := ((contDiff_scalarWidth P).comp h0).prodMk
    (h1.sub ((contDiff_scalarMidpoint P).comp h0))
  have h := norm_iteratedFDeriv_comp_le contDiff_profile hw (by exact_mod_cast hj2) p
    (C := C) (D := D) (fun i hi => hbC i (hi.trans hj2) _
      ⟨(scalarWidth_pos P _).le,
        (scalarWidth_bounds P _).2.trans (by linarith [P.eps_le_one])⟩ _)
    (fun i hi hi2 => hbD P i hi (hi2.trans hj2) p)
  change ‖iteratedFDeriv ℝ j (euclideanMovingProfile P) p‖ ≤ _ at h
  apply h.trans
  have hj' : j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl
  · norm_num [K]
    nlinarith [sq_nonneg (D - 1)]
  · norm_num [K]

/-- One constant bounds the value and every genuine derivative through order two
of the actual moving profile on the entire plane, uniformly over the finite family. -/
theorem exists_euclideanMovingProfile_jet_bound :
    ∃ K > 0, ∀ (P : Parameters) (j : ℕ), j ≤ 2 →
      ∀ p : EuclideanSpace ℝ (Fin 2),
        ‖iteratedFDeriv ℝ j (euclideanMovingProfile P) p‖ ≤ K := by
  obtain ⟨C, hC, hbC⟩ := exists_profile_derivative_bound
  obtain ⟨D, hD, hbD⟩ := exists_euclideanMovingProfile_derivative_bound
  refine ⟨C + D, by linarith, fun P j hj p => ?_⟩
  by_cases hj0 : j = 0
  · subst j
    have h := hbC 0 (by omega) (scalarWidth P (p 0))
      ⟨(scalarWidth_pos P _).le,
        (scalarWidth_bounds P _).2.trans (by linarith [P.eps_le_one])⟩
      (p 1 - scalarMidpoint P (p 0))
    simp only [norm_iteratedFDeriv_zero] at h ⊢
    exact h.trans (by linarith)
  · exact (hbD P j (by omega) hj p).trans (by linarith)

/-- The complete actual objective has a single uniform first and second Fréchet
derivative bound, chosen before the tolerance and the number of cells. -/
theorem exists_euclideanObjective_derivative_bound :
    ∃ K > 0, ∀ (P : Parameters) (j : ℕ), 1 ≤ j → j ≤ 2 →
      ∀ p : EuclideanSpace ℝ (Fin 2),
        ‖iteratedFDeriv ℝ j (euclideanObjective P) p‖ ≤ K := by
  obtain ⟨C, hC, hb⟩ := exists_euclideanMovingProfile_derivative_bound
  refine ⟨200 + C, by linarith, fun P j hj hj2 p => ?_⟩
  have h0 : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) => p 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  have hf := (contDiff_scalarObjective P).comp h0
  simp only [Function.comp_def] at hf
  have hg := contDiff_euclideanMovingProfile P
  have hsum := hf.add hg
  have hfp : ‖iteratedFDeriv ℝ j
      (fun p : EuclideanSpace ℝ (Fin 2) => scalarObjective P (p 0)) p‖ ≤ 200 := by
    have h := norm_iteratedFDeriv_scalar_pullback (contDiff_scalarObjective P)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) (norm_euclidean_proj_le_one 0) hj2 p
    simp only [Function.comp_def, EuclideanSpace.coe_proj] at h
    exact h.trans (scalarObjective_derivatives_bound P (by omega) _)
  have hsum_bound : ‖iteratedFDeriv ℝ j
      (fun p : EuclideanSpace ℝ (Fin 2) => scalarObjective P (p 0) + euclideanMovingProfile P p) p‖
        ≤ 200 + C := by
    rw [fun_iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast hj2)).contDiffAt
      (hg.of_le (by exact_mod_cast hj2)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add hfp (hb P j hj hj2 p))
  have heq : euclideanObjective P = fun p : EuclideanSpace ℝ (Fin 2) =>
      (Real.sqrt 2)⁻¹ • (scalarObjective P (p 0) + euclideanMovingProfile P p) := by
    ext p
    simp only [euclideanObjective, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [heq]
  change ‖iteratedFDeriv ℝ j ((Real.sqrt 2)⁻¹ •
    (fun p : EuclideanSpace ℝ (Fin 2) =>
      scalarObjective P (p 0) + euclideanMovingProfile P p)) p‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hsum.of_le (by exact_mod_cast hj2)).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt 2)⁻¹)]
  apply (mul_le_mul_of_nonneg_left hsum_bound (by positivity)).trans
  apply mul_le_of_le_one_left (by linarith : 0 ≤ 200 + C)
  apply (inv_le_one₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

/-- All completed finite valley objectives have globally Lipschitz gradients with one
constant fixed before selecting the tolerance or cell count. -/
theorem exists_euclideanObjective_gradient_lipschitz :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ P : Parameters, LipschitzWith K (gradient (euclideanObjective P)) := by
  obtain ⟨C, hC, hb⟩ := exists_euclideanObjective_derivative_bound
  refine ⟨⟨C, hC.le⟩, hC, fun P => ?_⟩
  exact lipschitzWith_gradient_of_iteratedFDeriv_two_le (contDiff_euclideanObjective P)
    (fun p => hb P 2 (by omega) (by omega) p)

end Optimization.SteepestDescentValley
