import Numlib.Optimization.SteepestDescent.Exact.CorridorObjective
import Numlib.Analysis.Calculus.IteratedDeriv.Product

/-!
# Uniform actual derivative tensors of the source corridor

The central and connector regions lie in a fixed compact coefficient box.
Outside that box the actual profile agrees locally with its quadratic plateau.
This identifies its genuine derivative tensors and gives global uniform bounds.
-/

open Set Filter Topology
noncomputable section
namespace ExactSteepestDescent.Corridor

/-- Strictly outside the enlarged corridor, the profile locally equals its plateau. -/
theorem profile_eventuallyEq_plateau {δ z : ℝ} (hδ : 0 < δ)
    (hz : z < -δ / 2 - 1 ∨ δ / 2 + 1 < z) :
    (fun w : ℝ × ℝ => profile w.1 w.2) =ᶠ[𝓝 (δ,z)]
      (fun w : ℝ × ℝ => 8*w.1^2) := by
  have hpos : IsOpen {w : ℝ × ℝ | 0 < w.1} :=
    isOpen_lt continuous_const continuous_fst
  rcases hz with hz | hz
  · have hlow : IsOpen {w : ℝ × ℝ | w.2 < -w.1 / 2 - 1} :=
      isOpen_lt continuous_snd (by fun_prop)
    have hU : IsOpen {w : ℝ × ℝ | 0 < w.1 ∧ w.2 < -w.1 / 2 - 1} :=
      hpos.inter hlow
    filter_upwards [hU.mem_nhds ⟨hδ,hz⟩] with w hw
    exact profile_exterior hw.1.le (Or.inl hw.2.le)
  · have hupp : IsOpen {w : ℝ × ℝ | w.1 / 2 + 1 < w.2} :=
      isOpen_lt (by fun_prop) continuous_snd
    have hU : IsOpen {w : ℝ × ℝ | 0 < w.1 ∧ w.1 / 2 + 1 < w.2} :=
      hpos.inter hupp
    filter_upwards [hU.mem_nhds ⟨hδ,hz⟩] with w hw
    exact profile_exterior hw.1.le (Or.inr hw.2.le)

/-- The plateau's actual derivatives are independent of the vertical coordinate. -/
theorem iteratedFDeriv_plateau (j : ℕ) (δ z : ℝ) :
    iteratedFDeriv ℝ j (fun w : ℝ × ℝ => 8*w.1^2) (δ,z) =
      iteratedFDeriv ℝ j (fun w : ℝ × ℝ => 8*w.1^2) (δ,0) := by
  have he : (fun w : ℝ × ℝ => 8*(w+(0,z)).1^2) =
      (fun w : ℝ × ℝ => 8*w.1^2) := by ext w; simp
  have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun w : ℝ × ℝ => 8*w.1^2) j (0,z) (δ,0)
  have ht' : iteratedFDeriv ℝ j (fun w : ℝ × ℝ => 8*w.1^2) (δ,z) =
      iteratedFDeriv ℝ j (fun w : ℝ × ℝ => 8*(w+(0,z)).1^2) (δ,0) := by
    simpa using ht.symm
  exact ht'.trans (congrFun (congrArg (iteratedFDeriv ℝ j) he) (δ,0))

/-- All actual derivative tensors of orders zero through two are uniformly bounded
for every positive width at most two and every vertical coordinate. -/
theorem profile_derivatives_bounded_global : ∃ B > 0, ∀ j ≤ 2,
    ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∀ z : ℝ,
      ‖iteratedFDeriv ℝ j (fun w : ℝ × ℝ => profile w.1 w.2) (δ,z)‖ ≤ B := by
  obtain ⟨B,hB,H⟩ := profile_derivatives_bounded
  have hp : ContDiff ℝ 2 (fun w : ℝ × ℝ => 8*w.1^2) := by fun_prop
  obtain ⟨C,hC,HC⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_iteratedFDeriv hp
  refine ⟨B+C,by positivity,?_⟩
  intro j hj δ hδ hδ2 z
  by_cases hz : z ∈ Icc (-2 : ℝ) 2
  · exact (H j hj δ ⟨hδ.le,hδ2⟩ z hz).trans (by linarith)
  · have he : z < -δ / 2 - 1 ∨ δ / 2 + 1 < z := by
      simp only [mem_Icc,not_and_or,not_le] at hz
      rcases hz with hz | hz
      · left; linarith
      · right; linarith
    rw [(profile_eventuallyEq_plateau hδ he).iteratedFDeriv ℝ j |>.eq_of_nhds,
      iteratedFDeriv_plateau]
    have hc := HC j hj (δ,(0 : ℝ))
      (show (δ,(0 : ℝ)) ∈ Icc (0 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2 from
        ⟨⟨hδ.le,hδ2⟩,by norm_num⟩)
    linarith

/-- The actual coordinate map into width and centered vertical displacement. -/
def corridorCoordinates (P : Parameters) (w : ℝ × ℝ) : ℝ × ℝ :=
  (curve P 0 w.1, w.2-curve P 1 w.1)

/-- The genuine coordinate map has the same global twice differentiability as its curves. -/
theorem contDiff_corridorCoordinates (P : Parameters) :
    ContDiff ℝ 2 (corridorCoordinates P) :=
  ((curve_spec P 0).1.comp contDiff_fst).prodMk
    (contDiff_snd.sub ((curve_spec P 1).1.comp contDiff_fst))

/-- A single constant bounds the genuine positive-order coordinate-map jets
independently of the accuracy and the point. -/
theorem corridorCoordinates_derivatives_bounded : ∃ D : ℝ, 1 ≤ D ∧
    ∀ (P : Parameters) (j : ℕ), 1 ≤ j → j ≤ 2 → ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (corridorCoordinates P) w‖ ≤ D^j := by
  obtain ⟨B,hB,H⟩ := curve_flat_derivatives_bounded
  refine ⟨B+1,by linarith,?_⟩
  intro P j hj hj2 w
  have hj' : (j : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj2
  have hw : ContDiff ℝ 2 (fun w : ℝ × ℝ => curve P 0 w.1) :=
    (curve_spec P 0).1.comp contDiff_fst
  have hc : ContDiff ℝ 2 (fun w : ℝ × ℝ => curve P 1 w.1) :=
    (curve_spec P 1).1.comp contDiff_fst
  have hf : ContDiff ℝ 2 (fun w : ℝ × ℝ => w.2) := contDiff_snd
  have hs := hf.sub hc
  have hwidth : ‖iteratedFDeriv ℝ j (fun w : ℝ × ℝ => curve P 0 w.1) w‖ ≤ B := by
    apply (norm_iteratedFDeriv_comp_fst_le (curve_spec P 0).1 hj' w).trans
    simpa only [Real.norm_eq_abs] using H P 0 (by decide) j hj hj2 w.1
  have hcenter : ‖iteratedFDeriv ℝ j (fun w : ℝ × ℝ => curve P 1 w.1) w‖ ≤ B := by
    apply (norm_iteratedFDeriv_comp_fst_le (curve_spec P 1).1 hj' w).trans
    simpa only [Real.norm_eq_abs] using H P 1 (by decide) j hj hj2 w.1
  have hsnd : ‖iteratedFDeriv ℝ j (fun w : ℝ × ℝ => w.2) w‖ ≤ 1 := by
    change ‖iteratedFDeriv ℝ j (ContinuousLinearMap.snd ℝ ℝ ℝ) w‖ ≤ 1
    simpa only [ContinuousLinearMap.norm_snd] using
      (ContinuousLinearMap.snd ℝ ℝ ℝ).norm_iteratedFDeriv_le hj w
  have hsub : ‖iteratedFDeriv ℝ j (fun w : ℝ × ℝ => w.2-curve P 1 w.1) w‖ ≤ 1+B := by
    rw [show (fun w : ℝ × ℝ => w.2-curve P 1 w.1) =
      (fun w : ℝ × ℝ => w.2) - (fun w : ℝ × ℝ => curve P 1 w.1) from rfl,
      iteratedFDeriv_sub (hf.of_le hj') (hc.of_le hj')]
    exact (norm_sub_le _ _).trans (add_le_add hsnd hcenter)
  change ‖iteratedFDeriv ℝ j
    (fun w : ℝ × ℝ => (curve P 0 w.1, w.2-curve P 1 w.1)) w‖ ≤ _
  rw [iteratedFDeriv_prodMk hw.contDiffAt hs.contDiffAt hj',
    ContinuousMultilinearMap.opNorm_prod]
  have hb : max ‖iteratedFDeriv ℝ j (fun w : ℝ × ℝ => curve P 0 w.1) w‖
      ‖iteratedFDeriv ℝ j (fun w : ℝ × ℝ => w.2-curve P 1 w.1) w‖ ≤ B+1 := by
    exact max_le (hwidth.trans (by linarith)) (hsub.trans_eq (by ring))
  apply hb.trans
  interval_cases j
  · simp
  · nlinarith [sq_nonneg B]

/-- The true source corridor function has uniformly bounded actual derivative
tensors through order two on the entire plane, including all connector joins. -/
theorem residualCorridor_derivatives_bounded : ∃ B > 0,
    ∀ (P : Parameters) (j : ℕ), j ≤ 2 → ∀ w : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (residualCorridor P) w‖ ≤ B := by
  obtain ⟨B,hB,H⟩ := profile_derivatives_bounded_global
  obtain ⟨D,hD,HD⟩ := corridorCoordinates_derivatives_bounded
  refine ⟨2*B*D^2,by positivity,?_⟩
  intro P j hj w
  have hwidth := curve_width_mem P w.1
  have hj' : (j : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj
  have hh := norm_iteratedFDeriv_comp_le contDiff_profile (contDiff_corridorCoordinates P)
    (n := j) hj' w (C := B) (D := D)
    (fun i hi => H i (hi.trans hj) _
      (P.accuracy_pos.trans_le hwidth.1) hwidth.2 _)
    (fun i hi hij => HD P i hi (hij.trans hj) w)
  have hfac : (j.factorial : ℝ) ≤ 2 := by interval_cases j <;> norm_num
  have hpow : D^j ≤ D^2 := by
    interval_cases j
    · simpa only [pow_zero] using (one_le_pow₀ hD : (1 : ℝ) ≤ D^2)
    · norm_num; nlinarith [sq_nonneg (D-1)]
    · exact le_rfl
  exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hfac hB.le) hpow
    (pow_nonneg (zero_le_one.trans hD) _) (by positivity))

/-- The actual scalar initial seed has the exact linear source formula. -/
theorem curveSeed_scalar (P : Parameters) : curveSeed P 2 =
    (fun t => 4-amplitude P 0*t) := by
  ext t
  rw [curveSeed, Hermite.taylorTail_two]
  simp [curveJet, scalarJet, scalarValue]
  ring

/-- The actual scalar objective has a uniformly bounded second derivative globally. -/
theorem scalarObjective_second_bounded : ∃ B > 0, ∀ (P : Parameters) (t : ℝ),
    |iteratedDeriv 2 (scalarObjective P) t| ≤ B := by
  obtain ⟨B,hB,H⟩ := curve_uniform_bounds
  obtain ⟨C,hC,HC⟩ := scalarTerminalPolynomial_uniform_bound
  refine ⟨B+C,by positivity,?_⟩
  intro P t
  have hxN : 0 ≤ horizontal P P.horizon := by
    rw [← horizontal_zero P]
    exact (horizontal_increasing P 0 P.horizon P.horizon_pos le_rfl).le
  by_cases ht0 : t ≤ 0
  · rw [scalarObjective_left P (by omega) (ht0.trans hxN),
      curve_left P 2 (by omega) ht0, curveSeed, Hermite.taylorTail_top]
    simp [curveJet,scalarJet]
    linarith
  by_cases htN : t ≤ horizontal P P.horizon
  · rw [scalarObjective_left P (by omega) htN]
    exact (H P 2 2 le_rfl t ⟨(lt_of_not_ge ht0).le,htN⟩).trans (by linarith)
  by_cases ht1 : t ≤ horizontal P P.horizon + 1
  · rw [scalarObjective_interval P (by omega) ⟨(lt_of_not_ge htN).le,ht1⟩]
    exact (HC P 2 le_rfl (t-horizontal P P.horizon)
      ⟨by linarith,by linarith⟩).trans (by linarith)
  · rw [scalarObjective_right P (by omega) (lt_of_not_ge ht1).le]
    norm_num
    linarith

/-- The actual source objective has a globally bounded second derivative tensor. -/
theorem objective_second_bounded : ∃ B > 0, ∀ (P : Parameters) (w : ℝ × ℝ),
    ‖iteratedFDeriv ℝ 2 (objective P) w‖ ≤ B := by
  obtain ⟨B,hB,H⟩ := scalarObjective_second_bounded
  obtain ⟨C,hC,HC⟩ := residualCorridor_derivatives_bounded
  refine ⟨|1/Real.sqrt 2| * (B+C),by positivity,?_⟩
  intro P w
  have hf : ContDiff ℝ 2 (fun w : ℝ × ℝ => scalarObjective P w.1) :=
    (contDiff_scalarObjective P).comp contDiff_fst
  have hg := contDiff_residualCorridor P
  have he : objective P = (1/Real.sqrt 2) •
      ((fun w : ℝ × ℝ => scalarObjective P w.1) + residualCorridor P) := by
    ext w
    simp only [objective, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring
  have hsmul := iteratedFDeriv_const_smul_apply (a := (1/Real.sqrt 2 : ℝ))
    (f := (fun w : ℝ × ℝ => scalarObjective P w.1) + residualCorridor P)
    (x := w) ((hf.add hg).contDiffAt)
  rw [he,hsmul,norm_smul,Real.norm_eq_abs,iteratedFDeriv_add hf hg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (norm_add_le _ _).trans
  apply add_le_add _ (HC P 2 le_rfl w)
  exact (norm_iteratedFDeriv_comp_fst_le (contDiff_scalarObjective P) le_rfl w).trans
    (by simpa only [Real.norm_eq_abs] using H P w.1)

end ExactSteepestDescent.Corridor
