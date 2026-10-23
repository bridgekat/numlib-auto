import Numlib.Optimization.SecondOrder.SharpnessInterpolation

/-!
# Uniform smooth witnesses for deterministic second-order methods

A single interpolation constant, chosen before accuracy and method, realizes
all actual recursively generated oracle histories. Every resulting objective
has uniform global value and derivative bounds and an exact first stopping time.
-/

namespace ShiftedNewton.Sharpness

/-- The Hermite interpolation constant can be fixed before both the requested
accuracy and the actual admissible method. -/
theorem exists_uniform_history_constant {κrg κlambda : ℝ}
    (hg0 : 0 ≤ κrg) (hg1 : κrg < 1) (hl : 1 < κlambda) :
    ∃ K : ℝ, 0 ≤ K ∧ 4 ≤ K ∧ 1 + κrg ≤ K ∧
      (1 / 2 + 2 * (1 + κrg) + 2 * (1 + κrg) ^ 2) / ((1 - κrg) / (2 * κlambda)) ^ 3 ≤ K ∧
      (1 + 4 * (1 + κrg)) / ((1 - κrg) / (2 * κlambda)) ^ 2 ≤ K ∧
      4 / ((1 - κrg) / (2 * κlambda)) ≤ K := by
  let c := (1 - κrg) / (2 * κlambda)
  let C := 1 + κrg
  let A := (1 / 2 + 2 * C + 2 * C ^ 2) / c ^ 3
  let D := (1 + 4 * C) / c ^ 2
  let F := 4 / c
  have hc : 0 < c := by dsimp [c];positivity
  have hC : 0 ≤ C := by dsimp [C];linarith
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hF : 0 ≤ F := by dsimp [F];positivity
  refine ⟨4 + C + A + D + F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  all_goals dsimp only [C, A, D, F, c] at *
  all_goals linarith

/-- Actual prescribed jets and boundedness give a common global Lipschitz
constant for the first derivative as well as the highest derivative. -/
theorem derivative_lipschitz_of_bounded_jets {f : ℝ → ℝ} {B L : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hf : ContDiff ℝ 2 f)
    (hbound : ∀ j ≤ 2, ∀ x, |iteratedDeriv j f x| ≤ B)
    (hLip : LipschitzWith ⟨L, hL⟩ (iteratedDeriv 2 f)) :
    LipschitzWith ⟨max B L, hB.trans (le_max_left _ _)⟩ (deriv f) := by
  have hcommon := norm_iteratedFDeriv_sub_le_of_bounded_jets hf hB
    (fun j hj x => by simpa only [Real.norm_eq_abs] using hbound j hj x)
    (fun x y => hLip.norm_sub_le x y)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hcommon 1 (by decide) x y
  simp only [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub,
    iteratedDeriv_one, Real.norm_eq_abs] at hh
  change |deriv f x - deriv f y| ≤ max B L * |x - y|
  exact hh

/-- Uniformly regular actual objectives force an arbitrary admissible actual
controller to stop for the first time at exactly the cubic reciprocal horizon.
Both regularity constants are chosen before the accuracy and the method. -/
theorem exists_uniform_slow_objective_sqrt {κrg κlambda : ℝ}
    (hg0 : 0 ≤ κrg) (hg1 : κrg < 1) (hl : 1 < κlambda) :
    ∃ (L : ℝ) (hL : 0 < L), ∃ (B : ℝ) (hB : 0 < B),
      ∀ t : ℝ, 0 < t → t < 1 → ∀ (κrs : ℝ) (M : ScalarMethod),
      IsScalarMethodClass M (t ^ 2) κrg κrs κlambda →
      ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ ScalarObjectiveClass f ∧
        LipschitzWith ⟨L, hL.le⟩ (iteratedDeriv 2 f) ∧
        LipschitzWith ⟨max B L, hB.le.trans (le_max_left _ _)⟩ (deriv f) ∧
        (∀ j ≤ 2, ∀ x, |iteratedDeriv j f x| ≤ B) ∧ f 0 = 1 ∧
        (∀ k < horizon t, t ^ 2 < |deriv f (M.iterates f k)|) ∧
        |deriv f (M.iterates f (horizon t))| ≤ t ^ 2 := by
  obtain ⟨K, hK, hK4, hKC, hK0, hK1, hK2⟩ := exists_uniform_history_constant hg0 hg1 hl
  obtain ⟨L, hL, B, hB, H⟩ := Hermite.exists_uniform_interpolant 2 K hK
  refine ⟨L, hL, B, hB, ?_⟩
  intro t ht ht1 κrs M hM
  obtain ⟨hinc, hres, hjet, hstep⟩ :=
    history_interpolation_data ht ht1 hM hK hK4 hKC hK0 hK1 hK2
  obtain ⟨f, hf, hLip, hmatch, hbound⟩ := H (horizon t) (horizon_pos ht)
    (fun k => (history M t k).point) (jet t) hinc hres
  have hb := hbound ⟨hjet, hstep⟩
  have hm : ScalarMatches f (history M t) (horizon t) := by
    intro k hk
    have h0 := hmatch k hk 0 (by decide)
    have h1 := hmatch k hk 1 (by decide)
    have h2 := hmatch k hk 2 (by decide)
    simp only [iteratedDeriv_zero, jet, ite_true] at h0
    norm_num only [iteratedDeriv_one, jet, show ¬(1 : ℕ)=0 by decide,
      ite_false, ite_true] at h1
    norm_num only [jet, show ¬(2 : ℕ)=0 by decide, show ¬(2 : ℕ)=1 by decide,
      ite_false, ite_true] at h2
    exact ⟨h0.trans (history_value M t k).symm,
      h1.trans (history_first M t k).symm, h2.trans (history_second M t k).symm⟩
  have hx := M.iterates_eq_of_matches (history_point_zero M t)
    (fun k _ => history_point_succ M t k) hm
  refine ⟨f, hf, scalarObjectiveClass_of_bounded_jets hf hB.le hb hLip, hLip,
    derivative_lipschitz_of_bounded_jets hB.le hL.le hf hb hLip, hb, ?_, ?_, ?_⟩
  · have hh := (hm 0 (Nat.zero_le _)).1
    simpa [value] using hh
  · intro k hk
    rw [hx k hk.le, (hm k hk.le).2.1, history_first]
    exact accuracy_lt_first ht hk
  · rw [hx (horizon t) le_rfl, (hm (horizon t) le_rfl).2.1, history_first]
    exact terminal_first_le ht ht1

/-- The square-root accuracy horizon is exactly the source real-power ceiling. -/
theorem horizon_sqrt {ε : ℝ} (hε : 0 ≤ ε) :
    horizon (Real.sqrt ε) = ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ := by
  unfold horizon
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hε]
  norm_num only [Nat.cast_ofNat, show (1 / (2 : ℝ)) * 3 = 3 / 2 by norm_num]
  rw [Real.rpow_neg hε, one_div]

/-- Every admissible deterministic scalar second-order controller has an actual
uniformly regular objective whose first successful gradient test occurs at
exactly the source ceiling of the accuracy to the power minus three halves. -/
theorem exists_uniform_slow_objective {κrg κlambda : ℝ}
    (hg0 : 0 ≤ κrg) (hg1 : κrg < 1) (hl : 1 < κlambda) :
    ∃ (L : ℝ) (hL : 0 < L), ∃ (B : ℝ) (hB : 0 < B),
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (κrs : ℝ) (M : ScalarMethod),
      IsScalarMethodClass M ε κrg κrs κlambda →
      ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ ScalarObjectiveClass f ∧
        LipschitzWith ⟨L, hL.le⟩ (iteratedDeriv 2 f) ∧
        LipschitzWith ⟨max B L, hB.le.trans (le_max_left _ _)⟩ (deriv f) ∧
        (∀ j ≤ 2, ∀ x, |iteratedDeriv j f x| ≤ B) ∧ f 0 = 1 ∧
        (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, ε < |deriv f (M.iterates f k)|) ∧
        |deriv f (M.iterates f ⌈ε ^ (-(3 / 2 : ℝ))⌉₊)| ≤ ε := by
  obtain ⟨L, hL, B, hB, H⟩ := exists_uniform_slow_objective_sqrt hg0 hg1 hl
  refine ⟨L, hL, B, hB, ?_⟩
  intro ε hε hε1 κrs M hM
  have ht : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have ht1 : Real.sqrt ε < 1 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hε1)
  have hM' : IsScalarMethodClass M ((Real.sqrt ε) ^ 2) κrg κrs κlambda := by
    simpa only [Real.sq_sqrt hε.le] using hM
  simpa only [horizon_sqrt hε.le, Real.sq_sqrt hε.le] using H _ ht ht1 κrs M hM'

end ShiftedNewton.Sharpness
