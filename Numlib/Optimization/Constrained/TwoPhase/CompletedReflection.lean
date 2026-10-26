import Numlib.Optimization.Constrained.TargetPerturbation

/-!
# Target progress after completed inner merit calls

A stricter old-target certificate separates any failed reflected-target test.
Actual Taylor perturbation then bounds the target gap below. Genuine derivative
and radius bounds turn this into an explicit accuracy-dependent target decrease.
-/

open scoped BigOperators
namespace Constrained.TwoPhase
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual bounded objective jets control its finite Taylor perturbation by
order times derivative bound times the legal displacement radius. -/
theorem targetTaylorBound_le_order_mul_radius (f : E → ℝ) (j : ℕ) (x : E)
    {δ B : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B)
    (hjet : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    targetTaylorBound f j x δ ≤ (j : ℝ) * B * δ := by
  unfold targetTaylorBound
  calc
    _ ≤ ∑ _i ∈ Finset.range j, B * δ := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : δ ^ (i + 1) ≤ δ := by
        rw [pow_succ]
        exact mul_le_of_le_one_left hδ (pow_le_one₀ hδ hδ1)
      have hden : (1 : ℝ) ≤ (i + 1).factorial := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (i + 1))
      have hnorm := hjet (i + 1) (by omega) (by simpa using hi)
      exact (div_le_self (mul_nonneg (norm_nonneg _) (pow_nonneg hδ _)) hden).trans
        (mul_le_mul hnorm hp (pow_nonneg hδ _) hB)
    _ = _ := by simp [mul_assoc]

/-- Uniform completed-reflection coefficient, preceding all accuracies. -/
noncomputable def completedReflectionCoefficient (j : ℕ) (β θ κ B : ℝ) : ℝ :=
  (1 - β) * θ * κ ^ (j - 1) / ((j.factorial : ℝ) * j * B)

/-- Legal margin and positive fixed data make the reflection coefficient positive. -/
theorem completedReflectionCoefficient_pos {j : ℕ} (hj : 0 < j)
    {β θ κ B : ℝ} (hβ : β < 1) (hθ : 0 < θ) (hκ : 0 < κ) (hB : 0 < B) :
    0 < completedReflectionCoefficient j β θ κ B := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  unfold completedReflectionCoefficient
  positivity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [ProperSpace E]

/-- A continuing actual reflection after a completed old-target merit call
spends a fixed accuracy power in target decrease. The bound follows from true
criticality perturbation, actual derivative norms and the returned radius floor. -/
theorem completed_reflection_target_drop {f : E → ℝ} {c : E → F} {x : E}
    {j : ℕ} (hj : 0 < j) (hf : ContDiffAt ℝ j f x) (hc : ContDiffAt ℝ j c x)
    {X : Set E} (hX : IsClosed X) (hx : x ∈ X)
    {t β θ κ B ε₀ ε δ : ℝ} (hβ1 : β < 1)
    (hθ : 0 < θ) (hκ : 0 < κ) (hB : 0 < B) (hε₀ : 0 < ε₀) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hfloor : κ * (ε₀ * ε) ≤ δ)
    (hjet : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ B)
    (hover : f x < t) (hres : θ * ε₀ ≤ ‖residual f c t x‖)
    (hold : TaylorModel.constrainedCriticality (targetMerit f c t) j X x δ ≤
      β * (ε * ‖residual f c t x‖ * δ ^ j / j.factorial))
    (hnew : ε * ‖residual f c (reflectTarget f t x) x‖ * δ ^ j / j.factorial <
      TaylorModel.constrainedCriticality (targetMerit f c (reflectTarget f t x)) j X x δ) :
    completedReflectionCoefficient j β θ κ B * (ε₀ * ε) ^ j <
      t - reflectTarget f t x := by
  rw [residual_reflect] at hnew
  have hsep := reflection_gap_bound_of_criticality_failure hf hc hX hx hδ.le hold hnew
  have hbound := targetTaylorBound_le_order_mul_radius f j x hδ.le hδ1 hB.le hjet
  have hgap : 2 * |f x - t| = t - reflectTarget f t x := by
    rw [abs_of_neg (sub_neg.mpr hover), reflectTarget]
    ring
  rw [hgap] at hsep
  have hdrop : 0 < t - reflectTarget f t x := sub_pos.mpr (reflect_lt hover)
  have hsep' := hsep.trans_le (mul_le_mul_of_nonneg_left hbound hdrop.le)
  have hfac : (0 : ℝ) < j.factorial := by positivity
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hscale : 0 ≤ (1 - β) * ε * δ ^ j / j.factorial := by positivity
  have hr := mul_le_mul_of_nonneg_left hres hscale
  have hstep : (1 - β) * θ * (ε₀ * ε) * δ ^ (j - 1) /
      ((j.factorial : ℝ) * j * B) < t - reflectTarget f t x := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (j.factorial : ℝ) * j * B)).mpr
    have hp : δ ^ j = δ ^ (j - 1) * δ := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    rw [hp] at hsep' hr
    have hh := (mul_lt_mul_iff_of_pos_right hδ).mp
      (show ((1 - β) * θ * (ε₀ * ε) * δ ^ (j - 1)) * δ <
        ((t - reflectTarget f t x) * ((j.factorial : ℝ) * j * B)) * δ by
          have hraw : ((1 - β) * θ * (ε₀ * ε) * δ ^ (j - 1) * δ) /
              (j.factorial : ℝ) < (t - reflectTarget f t x) * ((j : ℝ) * B * δ) := by
            apply lt_of_le_of_lt _ hsep'
            convert hr using 1 <;> ring
          have hcross := (div_lt_iff₀ hfac).mp hraw
          convert hcross using 1; ring)
    exact hh
  have hpow := pow_le_pow_left₀ (mul_pos hκ (mul_pos hε₀ hε)).le hfloor (j - 1)
  have hcoef : 0 ≤ (1 - β) * θ * (ε₀ * ε) /
      ((j.factorial : ℝ) * j * B) := by positivity
  have hh := mul_le_mul_of_nonneg_left hpow hcoef
  have he : completedReflectionCoefficient j β θ κ B * (ε₀ * ε) ^ j =
      ((1 - β) * θ * (ε₀ * ε) / ((j.factorial : ℝ) * j * B)) *
        (κ * (ε₀ * ε)) ^ (j - 1) := by
    rw [completedReflectionCoefficient,
      show (ε₀ * ε) ^ j = (ε₀ * ε) ^ (j - 1) * (ε₀ * ε) by
        conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]]
    simp only [mul_pow]
    ring
  rw [he]
  apply (hh.trans_lt ?_)
  convert hstep using 1; ring

end Constrained.TwoPhase
