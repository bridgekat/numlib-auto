import Numlib.Optimization.SteepestDescent.Exact.CorridorProfiles
import Numlib.Analysis.Calculus.ContDiff.CompactJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual corridor derivative bounds on bounded strips

All source central and unit-width transition strips with corridor width at most
two map into one fixed compact coefficient domain. The genuine joint derivative
tensors are uniformly bounded there. Actual chain-rule estimates preserve this
uniformity under bounded coordinate-map jets.
-/

open Set
namespace ExactSteepestDescent.Corridor

/-- A common positive constant bounds every actual joint derivative through
order two on the fixed box containing all source central and transition strips. -/
theorem profile_derivatives_bounded : ∃ B > 0, ∀ j ≤ 2,
    ∀ δ ∈ Icc (0 : ℝ) 2, ∀ z ∈ Icc (-2 : ℝ) 2,
      ‖iteratedFDeriv ℝ j (fun w : ℝ × ℝ => profile w.1 w.2) (δ, z)‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_iteratedFDeriv
    contDiff_profile
  exact ⟨B, hB, fun j hj δ hδ z hz => hb j hj (δ, z) ⟨hδ, hz⟩⟩

/-- Actual bounded coordinate-map jets give uniform derivative bounds for the
composed corridor profile. The constant precedes the map and its evaluation point. -/
theorem profile_composition_derivatives_bounded : ∃ B > 0,
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (F : E → ℝ × ℝ), ContDiff ℝ 2 F → ∀ (D : ℝ), 1 ≤ D → ∀ x : E,
      F x ∈ Icc (0 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2 →
      (∀ i, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i F x‖ ≤ D ^ i) →
      ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (fun y => profile (F y).1 (F y).2) x‖ ≤
        B * D ^ 2 := by
  obtain ⟨B, hB, hb⟩ := profile_derivatives_bounded
  refine ⟨2 * B, by positivity, ?_⟩
  intro E _ _ F hF D hD x hx hjet j hj
  have hh := norm_iteratedFDeriv_comp_le contDiff_profile hF
    (n := j) (by exact_mod_cast hj) x
    (C := B) (D := D) (fun i hi => hb i (hi.trans hj) _ hx.1 _ hx.2)
    (fun i hi hij => hjet i hi (hij.trans hj))
  have hfac : (j.factorial : ℝ) ≤ 2 := by interval_cases j <;> norm_num
  have hpow : D ^ j ≤ D ^ 2 := by
    interval_cases j
    · simpa only [pow_zero] using (one_le_pow₀ hD : (1 : ℝ) ≤ D ^ 2)
    · norm_num
      nlinarith [sq_nonneg (D - 1)]
    · exact le_rfl
  exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hfac hB.le) hpow
    (pow_nonneg (zero_le_one.trans hD) _) (by positivity))

end ExactSteepestDescent.Corridor
