import Numlib.Optimization.ConstrainedSecondOrder

/-!
# Strict sufficiency from a stationary comparison minorant

A normalized sequence violating strict objective minimality gives a genuine tangent
direction with nonpositive first variation. If a stationary comparison function is bounded
above by the objective on feasible points and agrees with it at the base point, the same
sequence makes its Hessian nonpositive. Apply the existing stationary tangent-cone Peano
result to the negated comparison function on the range of that actual sequence.
-/

open Filter Topology Metric Set

namespace Constrained

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Failure of strict constrained minimality gives a nonzero tangent direction with
nonpositive objective first variation and nonpositive stationary comparison Hessian. -/
theorem exists_tangent_direction_nonpos_second_of_not_strict
    {f L : E → ℝ} {f' : E →L[ℝ] ℝ} {L' : E → E →L[ℝ] ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} {x : E}
    (hf : HasFDerivAt f f' x) (hL : ∀ᶠ y in 𝓝 x, HasFDerivAt L (L' y) y)
    (hH : HasFDerivAt L' H x) (hstat : L' x = 0) (hval : L x = f x)
    (hcomp : ∀ y ∈ S, L y ≤ f y)
    (hnot : ¬∃ δ > 0, ∀ y ∈ S, dist y x < δ → y ≠ x → f x < f y) :
    ∃ z, z ≠ 0 ∧ z ∈ posTangentConeAt S x ∧ f' z ≤ 0 ∧ H z z ≤ 0 := by
  push Not at hnot
  have hseq : ∀ n : ℕ, ∃ y, y ∈ S ∧ dist y x < 1 / ((n : ℝ) + 1) ∧ y ≠ x ∧
      f y ≤ f x := fun n => hnot (1 / ((n : ℝ) + 1)) (by positivity)
  choose y hyS hyd hyne hyf using hseq
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hyd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hwne : ∀ n, y n - x ≠ 0 := fun n => sub_ne_zero.mpr (hyne n)
  set u : ℕ → E := fun n => ‖y n - x‖⁻¹ • (y n - x) with hu
  have hunorm : ∀ n, ‖u n‖ = 1 := fun n => by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hwne n))]
  obtain ⟨z, hz, φ, hφ, hulim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    fun n => mem_sphere_zero_iff_norm.mpr (hunorm n)
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [mem_sphere_zero_iff_norm, hzero, norm_zero] at hz
    exact zero_ne_one hz
  have hyφ : Tendsto (y ∘ φ) atTop (𝓝 x) := hylim.comp hφ.tendsto_atTop
  have htanT : z ∈ posTangentConeAt (range y) x := by
    apply mem_tangentConeAt_of_seq atTop (fun n => Real.toNNReal ‖y (φ n) - x‖⁻¹)
      (fun n => y (φ n) - x)
    · simpa using hyφ.sub_const x
    · exact Eventually.of_forall fun n => by simp
    · refine hulim.congr fun n => ?_
      rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr (norm_nonneg _))]
      rfl
  have htanS : z ∈ posTangentConeAt S x :=
    tangentConeAt_mono (by rintro _ ⟨n, rfl⟩; exact hyS n) htanT
  have hfnonpos : f' z ≤ 0 := by
    have hrem := (hasFDerivAt_iff_tendsto.mp hf).comp hyφ
    have hpoint : ∀ n, f' (u (φ n)) ≤ ‖y (φ n) - x‖⁻¹ *
        ‖f (y (φ n)) - f x - f' (y (φ n) - x)‖ := by
      intro n
      rw [hu, map_smul, smul_eq_mul]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
      rw [Real.norm_eq_abs]
      linarith [neg_abs_le (f (y (φ n)) - f x - f' (y (φ n) - x)), hyf (φ n)]
    exact le_of_tendsto_of_tendsto' (((f').continuous.tendsto z).comp hulim) hrem hpoint
  have hmin : IsMinOn (fun q => -L q) (range y) x := by
    rintro _ ⟨n, rfl⟩
    change -L x ≤ -L (y n)
    exact neg_le_neg ((hcomp _ (hyS n)).trans ((hyf n).trans_eq hval.symm))
  have hnegL : ∀ᶠ q in 𝓝 x, HasFDerivAt (fun p => -L p) (-L' q) q :=
    hL.mono fun _ hq => hq.neg
  have hHnonpos : H z z ≤ 0 := by
    have hh := nonneg_second_on_tangentCone_of_isLocalMinOn hnegL hH.neg
      (by rw [hstat, neg_zero]) hmin.isLocalMinOn htanT
    simpa only [neg_apply, neg_nonneg] using hh
  exact ⟨z, hz0, htanS, hfnonpos, hHnonpos⟩

/-- A stationary comparison minorant with positive Hessian on every potentially descending
nonzero feasible tangent direction gives strict constrained minimality. -/
theorem isStrictLocalMinOn_of_posDef_comparison
    {f L : E → ℝ} {f' : E →L[ℝ] ℝ} {L' : E → E →L[ℝ] ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} {x : E}
    (hf : HasFDerivAt f f' x) (hL : ∀ᶠ y in 𝓝 x, HasFDerivAt L (L' y) y)
    (hH : HasFDerivAt L' H x) (hstat : L' x = 0) (hval : L x = f x)
    (hcomp : ∀ y ∈ S, L y ≤ f y)
    (hpos : ∀ z ∈ posTangentConeAt S x, f' z ≤ 0 → z ≠ 0 → 0 < H z z) :
    ∃ δ > 0, ∀ y ∈ S, dist y x < δ → y ≠ x → f x < f y := by
  by_contra hnot
  obtain ⟨z, hz, htan, hfz, hHz⟩ :=
    exists_tangent_direction_nonpos_second_of_not_strict hf hL hH hstat hval hcomp hnot
  exact (not_lt_of_ge hHz) (hpos z htan hfz hz)

end Constrained
