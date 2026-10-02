/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ParametricIntervalIntegral` or beside
`Mathlib.Analysis.Calculus.DSlope`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The segment average of the derivative

For `f : 𝕜 → F` differentiable on a convex set `U` of `𝕜 = ℝ` or `ℂ`, with values in a normed
space `F` over `𝕜`, and `a ∈ U`, the **segment average**

  `g z = ∫₀¹ f'(a + t (z - a)) dt`

satisfies `f z = f a + (z - a) • g z` on `U` (`eq_add_smul_integral_comp_segment`): it is the
difference quotient `(f z - f a) / (z - a)` extended by `f'(a)` at `a`. Differentiating under the
integral sign, on an open convex set where `f` is `C^{n+1}` the average is `C^n`, with
`g⁽ᵏ⁾(z) = ∫₀¹ tᵏ f⁽ᵏ⁺¹⁾(a + t (z - a)) dt` (`iteratedDeriv_integral_deriv_comp_segment`,
`contDiffOn_integral_deriv_comp_segment`), so `‖g⁽ᵏ⁾‖ ≤ M / (k + 1)` where `‖f⁽ᵏ⁺¹⁾‖ ≤ M`
(`norm_integral_pow_smul_comp_segment_le`).

This is Hadamard's lemma in one variable (`ContDiffAt.dslope_same` of
`Numlib/Analysis/Calculus/RootMultiplicity`), and one step of the Hermite–Genocchi formula for
divided differences (`Numlib/Analysis/Calculus/HermiteGenocchi`).
-/

open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Interval

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] {U : Set 𝕜} {a z : 𝕜}

omit [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] in
/-- A function continuous on a convex set is continuous along the segments in it, also with the
weight `tᵏ`. -/
theorem ContinuousOn.pow_smul_comp_segment {φ : 𝕜 → F} (hφ : ContinuousOn φ U)
    (hU : Convex ℝ U) (ha : a ∈ U) (hz : z ∈ U) (k : ℕ) :
    ContinuousOn (fun t : ℝ => t ^ k • φ (a + t • (z - a))) (Icc 0 1) :=
  (continuous_pow k).continuousOn.smul
    (hφ.comp (by fun_prop) fun _ ht => hU.add_smul_sub_mem ha hz ht)

@[deprecated (since := "2026-09-30")]
alias ContinuousOn.comp_segment := ContinuousOn.pow_smul_comp_segment

omit [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
/-- Around a point `z` of an open convex set `U`, the segments from `a ∈ U` to the points of a
closed ball about `z` sweep out a compact subset of `U`, on which a function continuous on `U` is
bounded. -/
private theorem exists_bound_comp_segment {φ : 𝕜 → F} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hφ : ContinuousOn φ U) (ha : a ∈ U) (hz : z ∈ U) :
    ∃ ε > 0, ∃ C, ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball z ε, ‖φ (a + t • (w - a))‖ ≤ C := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
  have hδU : Metric.closedBall z (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  set K := (fun p : ℝ × 𝕜 => a + p.1 • (p.2 - a)) '' (Icc 0 1 ×ˢ Metric.closedBall z (ε / 2))
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_closedBall z _)).image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    exact hUc.add_smul_sub_mem ha (hδU hw) ht
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hφ.mono hKU)
  exact ⟨ε / 2, half_pos hε, C, fun t ht w hw =>
    hC _ ⟨(t, w), ⟨ht, Metric.ball_subset_closedBall hw⟩, rfl⟩⟩

omit [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] in
/-- The weighted segment averages are measurable on `(0, 1]`. -/
private theorem aestronglyMeasurable_comp_segment {φ : 𝕜 → F} (hUc : Convex ℝ U)
    (hφ : ContinuousOn φ U) (ha : a ∈ U) (hw : z ∈ U) (k : ℕ) :
    AEStronglyMeasurable (fun t : ℝ => t ^ k • φ (a + t • (z - a))) (volume.restrict (Ι 0 1)) := by
  rw [uIoc_of_le zero_le_one]
  exact ((hφ.pow_smul_comp_segment hUc ha hw k).mono Ioc_subset_Icc_self).aestronglyMeasurable
    measurableSet_Ioc

omit [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] in
/-- **Continuity of the weighted segment average.** If `φ` is continuous on an open convex set
`U`, then `w ↦ ∫₀¹ tᵏ φ(a + t(w - a)) dt` is continuous on `U`. -/
theorem continuousOn_integral_pow_smul_comp_segment {φ : 𝕜 → F} (hU : IsOpen U)
    (hUc : Convex ℝ U) (hφ : ContinuousOn φ U) (ha : a ∈ U) (k : ℕ) :
    ContinuousOn (fun w => ∫ t in (0 : ℝ)..1, t ^ k • φ (a + t • (w - a))) U := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ε, hε, C, hC⟩ := exists_bound_comp_segment hU hUc hφ ha hz
  have h01 : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine continuousAt_of_dominated_interval (μ := volume) (bound := fun _ => C)
    (F := fun w t => t ^ k • φ (a + t • (w - a)))
    (eventually_of_mem (hU.mem_nhds hz) fun w hw =>
      aestronglyMeasurable_comp_segment hUc hφ ha hw k)
    (eventually_of_mem (Metric.ball_mem_nhds z hε) fun w hw => ae_of_all _ fun t ht => ?_)
    intervalIntegrable_const (ae_of_all _ fun t ht => ?_)
  · rw [h01] at ht
    rw [norm_smul, norm_pow, Real.norm_of_nonneg ht.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.1.le ht.2)).trans
      (hC t (Ioc_subset_Icc_self ht) w hw)
  · rw [h01] at ht
    have hpt : a + t • (z - a) ∈ U := hUc.add_smul_sub_mem ha hz (Ioc_subset_Icc_self ht)
    exact continuousAt_const.smul (ContinuousAt.comp (g := φ)
      (hφ.continuousAt (hU.mem_nhds hpt)) (by fun_prop))

/-- **Differentiation under the integral along segments.** If `φ` has derivative `φ'` on an open
convex set `U`, with `φ'` continuous there, then `w ↦ ∫₀¹ tᵏ φ(a + t(w - a)) dt` has derivative
`∫₀¹ tᵏ⁺¹ φ'(a + t(z - a)) dt` at every `z ∈ U`. -/
theorem hasDerivAt_integral_pow_smul_comp_segment {φ φ' : 𝕜 → F} (hU : IsOpen U)
    (hUc : Convex ℝ U) (hφ : ∀ w ∈ U, HasDerivAt φ (φ' w) w) (hφ' : ContinuousOn φ' U)
    (ha : a ∈ U) (hz : z ∈ U) (k : ℕ) :
    HasDerivAt (fun w => ∫ t in (0 : ℝ)..1, t ^ k • φ (a + t • (w - a)))
      (∫ t in (0 : ℝ)..1, t ^ (k + 1) • φ' (a + t • (z - a))) z := by
  have hφc : ContinuousOn φ U := fun w hw => (hφ w hw).continuousAt.continuousWithinAt
  obtain ⟨ε, hε, C, hC⟩ := exists_bound_comp_segment hU hUc hφ' ha hz
  obtain ⟨ε', hε', hε'U⟩ := Metric.isOpen_iff.mp hU z hz
  have h01 : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F := fun w t => t ^ k • φ (a + t • (w - a)))
    (F' := fun w t => t ^ (k + 1) • φ' (a + t • (w - a)))
    (Metric.ball_mem_nhds z (lt_min hε hε'))
    (eventually_of_mem (hU.mem_nhds hz) fun w hw =>
      aestronglyMeasurable_comp_segment hUc hφc ha hw k)
    ((hφc.pow_smul_comp_segment hUc ha hz k).intervalIntegrable_of_Icc zero_le_one)
    (aestronglyMeasurable_comp_segment hUc hφ' ha hz (k + 1)) (ae_of_all _ fun t ht w hw => ?_)
    intervalIntegrable_const (ae_of_all _ fun t ht w hw => ?_)).2
  · rw [h01] at ht
    rw [norm_smul, norm_pow, Real.norm_of_nonneg ht.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.1.le ht.2)).trans
      (hC t (Ioc_subset_Icc_self ht) w (Metric.ball_subset_ball (min_le_left _ _) hw))
  · rw [h01] at ht
    have hwU : w ∈ U := hε'U (Metric.ball_subset_ball (min_le_right _ _) hw)
    have hpt : a + t • (w - a) ∈ U := hUc.add_smul_sub_mem ha hwU (Ioc_subset_Icc_self ht)
    have hin : HasDerivAt (fun w => a + t • (w - a)) (t • (1 : 𝕜)) w :=
      (((hasDerivAt_id w).sub_const a).const_smul t).const_add a
    refine (((hφ _ hpt).scomp w hin).const_smul (t ^ k)).congr_deriv ?_
    rw [smul_one_smul, smul_smul, pow_succ]

/-- **The segment average**: if `f` has derivative `f'` on a convex set `U`, with `f'`
continuous there, then `f z = f a + (z - a) • ∫₀¹ f'(a + t(z - a)) dt` for `a, z ∈ U`. -/
theorem eq_add_smul_integral_comp_segment [CompleteSpace F] {f f' : 𝕜 → F} (hU : Convex ℝ U)
    (hf : ∀ w ∈ U, HasDerivAt f (f' w) w) (hf' : ContinuousOn f' U) (ha : a ∈ U) (hz : z ∈ U) :
    f z = f a + (z - a) • ∫ t in (0 : ℝ)..1, f' (a + t • (z - a)) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => f (a + t • (z - a))) ((z - a) • f' (a + t • (z - a))) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact ((hf _ (hU.add_smul_sub_mem ha hz ht)).scomp t
      (((hasDerivAt_id t).smul_const (z - a)).const_add a)).congr_deriv (by simp)
  have hint : IntervalIntegrable (fun t : ℝ => (z - a) • f' (a + t • (z - a))) volume 0 1 :=
    (((hf'.pow_smul_comp_segment hU ha hz 0).const_smul (z - a)).intervalIntegrable_of_Icc
      zero_le_one).congr fun t _ => by simp
  rw [← intervalIntegral.integral_smul, integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **The segment average** of a scalar function: `f z = f a + (z - a) ∫₀¹ f'(a + t(z - a)) dt`,
the case `F = 𝕜` of `eq_add_smul_integral_comp_segment`. -/
theorem eq_add_mul_integral_comp_segment {f f' : 𝕜 → 𝕜} (hU : Convex ℝ U)
    (hf : ∀ w ∈ U, HasDerivAt f (f' w) w) (hf' : ContinuousOn f' U) (ha : a ∈ U) (hz : z ∈ U) :
    f z = f a + (z - a) * ∫ t in (0 : ℝ)..1, f' (a + t • (z - a)) :=
  eq_add_smul_integral_comp_segment hU hf hf' ha hz

/-- The derivatives `f⁽ᵏ⁺¹⁾` of a function `C^{k+2}` on an open convex set `U` make the segment
averages `w ↦ ∫₀¹ tᵏ f⁽ᵏ⁺¹⁾(a + t(w - a)) dt` a chain, each the derivative of the previous. -/
theorem hasDerivAt_integral_pow_smul_iteratedDeriv_comp_segment {f : 𝕜 → F} {n : WithTop ℕ∞}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hf : ContDiffOn 𝕜 n f U) (ha : a ∈ U) (hz : z ∈ U)
    {k : ℕ} (hk : (k + 2 : ℕ) ≤ n) :
    HasDerivAt (fun w => ∫ t in (0 : ℝ)..1, t ^ k • iteratedDeriv (k + 1) f (a + t • (w - a)))
      (∫ t in (0 : ℝ)..1, t ^ (k + 1) • iteratedDeriv (k + 2) f (a + t • (z - a))) z := by
  have hfN : ContDiffOn 𝕜 (k + 2 : ℕ) f U := hf.of_le hk
  exact hasDerivAt_integral_pow_smul_comp_segment hU hUc
    (fun w hw => hfN.hasDerivAt_iteratedDeriv_of_isOpen hU (j := k + 1) (by omega) hw)
    (hfN.continuousOn_iteratedDeriv_of_isOpen hU le_rfl) ha hz k

/-- **The derivatives of the segment average**: if `f` is `C^{k+1}` on an open convex set `U`,
then `g z = ∫₀¹ f'(a + t(z - a)) dt` has `g⁽ᵏ⁾(z) = ∫₀¹ tᵏ f⁽ᵏ⁺¹⁾(a + t(z - a)) dt` on `U`. -/
theorem iteratedDeriv_integral_deriv_comp_segment {f : 𝕜 → F} {n : WithTop ℕ∞} (hU : IsOpen U)
    (hUc : Convex ℝ U) (hf : ContDiffOn 𝕜 n f U) (ha : a ∈ U) {k : ℕ} (hk : (k + 1 : ℕ) ≤ n) :
    EqOn (iteratedDeriv k fun w => ∫ t in (0 : ℝ)..1, deriv f (a + t • (w - a)))
      (fun w => ∫ t in (0 : ℝ)..1, t ^ k • iteratedDeriv (k + 1) f (a + t • (w - a))) U := by
  induction k with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    have hk' : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n := le_trans (by exact_mod_cast (by omega)) hk
    rw [iteratedDeriv_succ, ((ih hk').eventuallyEq_of_mem (hU.mem_nhds hw)).deriv_eq,
      (hasDerivAt_integral_pow_smul_iteratedDeriv_comp_segment hU hUc hf ha hw hk).deriv]

/-- The segment average of a function `C^{n+1}` on an open convex set is `C^n` there, for a finite
`n`. -/
private theorem contDiffOn_integral_deriv_comp_segment_nat {f : 𝕜 → F} (hU : IsOpen U)
    (hUc : Convex ℝ U) {n : ℕ} (hf : ContDiffOn 𝕜 (n + 1 : ℕ) f U) (ha : a ∈ U) :
    ContDiffOn 𝕜 n (fun w => ∫ t in (0 : ℝ)..1, deriv f (a + t • (w - a))) U := by
  have h := (contDiffOn_of_hasDerivAt_chain (n := n)
    (G := fun k w => ∫ t in (0 : ℝ)..1, t ^ k • iteratedDeriv (k + 1) f (a + t • (w - a))) hU
    (fun k hk w hw => hasDerivAt_integral_pow_smul_iteratedDeriv_comp_segment hU hUc hf ha hw
      (by exact_mod_cast (by omega : k + 2 ≤ n + 1)))
    (continuousOn_integral_pow_smul_comp_segment hU hUc
      (hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl) ha n)).1
  exact h.congr fun w _ => by simp

/-- **The segment average of a `C^{n+1}` function is `C^n`**: if `f` is `C^{n+1}` on an open
convex set `U` (`n = ∞` allowed), then `w ↦ ∫₀¹ f'(a + t(w - a)) dt` is `C^n` there. -/
theorem contDiffOn_integral_deriv_comp_segment {f : 𝕜 → F} (hU : IsOpen U) (hUc : Convex ℝ U)
    {n : ℕ∞} (hf : ContDiffOn 𝕜 (n + 1 : ℕ∞) f U) (ha : a ∈ U) :
    ContDiffOn 𝕜 n (fun w => ∫ t in (0 : ℝ)..1, deriv f (a + t • (w - a))) U := by
  refine contDiffOn_iff_forall_nat_le.2 fun m hm => ?_
  refine contDiffOn_integral_deriv_comp_segment_nat hU hUc (hf.of_le ?_) ha
  have hm' : (m : ℕ∞) + 1 ≤ n + 1 := by gcongr
  exact_mod_cast hm'

omit [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] in
/-- The weighted segment average of `φ` is bounded by `M / (k + 1)` when `‖φ‖ ≤ M` on the
segment. -/
theorem norm_integral_pow_smul_comp_segment_le {φ : 𝕜 → F} {M : ℝ} (k : ℕ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ (a + t • (z - a))‖ ≤ M) :
    ‖∫ t in (0 : ℝ)..1, t ^ k • φ (a + t • (z - a))‖ ≤ M / (k + 1) := by
  calc ‖∫ t in (0 : ℝ)..1, t ^ k • φ (a + t • (z - a))‖
      ≤ ∫ t in (0 : ℝ)..1, t ^ k * M := by
        refine norm_integral_le_of_norm_le zero_le_one (ae_of_all _ fun t ht => ?_)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        rw [norm_smul, norm_pow, Real.norm_of_nonneg ht.1.le]
        exact mul_le_mul_of_nonneg_left (hM t (Ioc_subset_Icc_self ht)) (pow_nonneg ht.1.le _)
    _ = M / (k + 1) := by
        rw [intervalIntegral.integral_mul_const, integral_pow, one_pow,
          zero_pow (Nat.succ_ne_zero k), sub_zero]
        ring
