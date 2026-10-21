import Numlib.Optimization.TrustRegionSharpness
import Numlib.Optimization.QuadraticSubproblem
import Numlib.Optimization.TrustRegion
import NumlibSurface.CartisGouldToint.Chapter02.Section01
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Cauchy decrease for a quadratic trust-region model -/

open Set Metric
open Optimization.QuadraticSubproblem

namespace CartisGouldToint.Chapter02.Section03

variable {n : ℕ}


/-- A Cauchy point minimizes the quadratic model along the feasible negative-gradient ray.
Membership is explicit because `IsMinOn` itself does not assert feasibility. -/
abbrev IsCauchyPoint (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (delta : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  Optimization.QuadraticSubproblem.IsCauchyPoint g H delta s

/-- A Cauchy point has no larger value than any feasible negative-gradient ray step. -/
theorem IsCauchyPoint.le_ray {g : EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {delta : ℝ} {s : EuclideanSpace ℝ (Fin n)}
    (hs : IsCauchyPoint g H delta s) {t : ℝ} (ht : 0 ≤ t) (hfeas : t * ‖g‖ ≤ delta) :
    quadratic g H s ≤ quadratic g H (-(t • g)) := by
  apply hs.2
  refine ⟨?_, ⟨t, ht, rfl⟩⟩
  rw [mem_closedBall_zero_iff, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact hfeas

/-- Lemma 2.3.2: quadratic Cauchy decrease, with positivity of the predicted reduction whenever
the gradient is nonzero. The positivity ensures that the trust-region ratio has nonzero
denominator for every step giving at least Cauchy decrease. -/
theorem lemma_2_3_2 {g : EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {delta : ℝ} (hdelta : 0 < delta)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsCauchyPoint g H delta s) :
    (1 / 2 : ℝ) * ‖g‖ * min (‖g‖ / (1 + ‖H‖)) delta ≤
        quadratic g H 0 - quadratic g H s ∧
      (g ≠ 0 → 0 < quadratic g H 0 - quadratic g H s) := by
  exact ⟨cauchy_decrease g H hdelta.le (fun _ ht hf => hs.le_ray ht hf),
    fun hg => cauchy_decrease_pos H hdelta hg (fun _ ht hf => hs.le_ray ht hf)⟩

end CartisGouldToint.Chapter02.Section03

namespace CartisGouldToint.Chapter02.Section03

/-- The actual trial step in (2.3.6) has a positive denominator whenever it gives at least
Cauchy decrease and the gradient is nonzero. -/
theorem lemma_2_3_2_ratio_denominator_pos {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {delta : ℝ} (hdelta : 0 < delta) {sC s : EuclideanSpace ℝ (Fin n)}
    (hsC : IsCauchyPoint g H delta sC) (hg : g ≠ 0)
    (hs : Optimization.QuadraticSubproblem.quadratic g H s ≤
      Optimization.QuadraticSubproblem.quadratic g H sC) :
    0 < Optimization.QuadraticSubproblem.quadratic g H 0 -
      Optimization.QuadraticSubproblem.quadratic g H s := by
  exact lt_of_lt_of_le ((lemma_2_3_2 hdelta hsC).2 hg) (sub_le_sub_left hs _)

end CartisGouldToint.Chapter02.Section03

namespace CartisGouldToint.Chapter02.Section03
variable {n : ℕ}

open Section01 Optimization.TrustRegion

/-- Assumption m.HBa: a uniform nonnegative bound on all quadratic-model operators. -/
def trustRegionAssumptions
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ k, ‖H k‖ ≤ B

/-- Algorithm 2.3.1: a lawful TR1 update trace. Its stopping time is the first gradient
test in Theorem 2.3.7.
The operators are symmetric, as required for the source's quadratic model. -/
def algorithm_2_3_1 (p : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (delta : ℕ → ℝ) : Prop :=
  IsRun p f (gradient f) H x s delta ∧ ∀ k, (H k).IsSymmetric

variable {p : Parameters} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {delta : ℕ → ℝ}

/-- Lemma 2.3.1. Counts use the iterations before endpoint k, consistently with delta k. -/
theorem lemma_2_3_1 (h : algorithm_2_3_1 p f H x s delta) (k : ℕ) {m : ℝ}
    (hm : 0 < m) (hmin : m ≤ delta k) :
    (k : ℝ) ≤ (Optimization.ParameterUpdates.successCount
      (fun j => p.eta1 ≤ ratio f (gradient f (x j)) (H j) (x j) (s j)) k : ℝ) *
      (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
      |Real.log (m / delta 0)| / |Real.log p.gamma2| := by
  have hh := h.1.total_count_le k hm hmin
  have hz : 0 ≤ |Real.log p.gamma2| := abs_nonneg _
  have he : Real.log (delta 0 / m) = -Real.log (m / delta 0) := by
    rw [Real.log_div (h.1.radius_pos 0).ne' hm.ne',
      Real.log_div hm.ne' (h.1.radius_pos 0).ne']
    ring
  have hb := div_le_div_of_nonneg_right (neg_le_abs (Real.log (m / delta 0))) hz
  rw [he] at hh
  linarith

/-- Lemma 2.3.3: a small radius makes the iteration very successful and prevents contraction. -/
theorem lemma_2_3_3 (h : algorithm_2_3_1 p f H x s delta) {L B : ℝ}
    (hf : assumption_f_gL f L) (hB : trustRegionAssumptions H B) (k : ℕ)
    (hsmall : delta k < (1 - p.eta2) / (2 * (L + B)) * ‖gradient f (x k)‖) :
    p.eta2 ≤ ratio f (gradient f (x k)) (H k) (x k) (s k) ∧
      p.eta1 ≤ ratio f (gradient f (x k)) (H k) (x k) (s k) ∧ delta k ≤ delta (k + 1) := by
  have hr := h.1.ratio_ge_of_radius_lt hf.hasFDerivAt hf.lipschitz hf.2.1 hB.2 k hsmall
  exact ⟨hr, p.eta_le.trans hr,
    h.1.radius_nondecrease_of_small hf.hasFDerivAt hf.lipschitz hf.2.1 hB.2 k hsmall⟩

/-- Lemma 2.3.4: the source's explicit coefficient times the smallest gradient through k
bounds the current radius from below. A zero initial gradient is already terminal. -/
theorem lemma_2_3_4 (h : algorithm_2_3_1 p f H x s delta) {L B : ℝ}
    (hf : assumption_f_gL f L) (hB : trustRegionAssumptions H B) (k : ℕ) :
    radiusCoefficient p L B (delta 0) ‖gradient f (x 0)‖ *
      runningMin (fun j => ‖gradient f (x j)‖) k ≤ delta k := by
  by_cases hg : gradient f (x 0) = 0
  · simpa [radiusCoefficient, hg] using (h.1.radius_pos k).le
  · have hs := radiusCoefficient_spec p hf.2.1 hB.1 (h.1.radius_pos 0) (norm_pos_iff.mpr hg)
    exact h.1.radius_lower hf.hasFDerivAt hf.lipschitz hf.2.1 hB.2 hs.1.le hs.2.1 hs.2.2 k

/-- Lemma 2.3.5, using model displacements m(0)-m(s) as in its proof. The transcription's
m(x)-m(x+s) is inconsistent with the displacement definition (2.3.1). -/
theorem lemma_2_3_5 (h : algorithm_2_3_1 p f H x s delta) {L B : ℝ}
    (hf : assumption_f_gL f L) (hB : trustRegionAssumptions H B) (k : ℕ) :
    decreaseCoefficient B (radiusCoefficient p L B (delta 0) ‖gradient f (x 0)‖) *
      ‖gradient f (x k)‖ * runningMin (fun j => ‖gradient f (x j)‖) k ≤
      quadratic (gradient f (x k)) (H k) 0 - quadratic (gradient f (x k)) (H k) (s k) := by
  have hc : 0 ≤ radiusCoefficient p L B (delta 0) ‖gradient f (x 0)‖ := by
    by_cases hg : gradient f (x 0) = 0
    · simp [radiusCoefficient, hg]
    · exact (radiusCoefficient_spec p hf.2.1 hB.1
        (h.1.radius_pos 0) (norm_pos_iff.mpr hg)).1.le
  exact h.1.predicted_decrease_of_radius_lower hB.2 hc k (lemma_2_3_4 h hf hB k)

/-- Lemma 2.3.6: a tolerance-independent positive constant bounds successful iterations before
the first approximate first-order minimizer. -/
theorem lemma_2_3_6 (h : algorithm_2_3_1 p f H x s delta) {L B low : ℝ}
    (hf : assumption_f_gL f L) (hB : trustRegionAssumptions H B) (hlow : ∀ y, low ≤ f y) :
    ∃ kS : ℝ, 0 < kS ∧ ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ,
      approximateFirstOrderMinimizer f epsilon (x K) ∧
      (∀ j < K, epsilon < ‖gradient f (x j)‖) ∧
      (Optimization.ParameterUpdates.successCount
        (fun j => p.eta1 ≤ ratio f (gradient f (x j)) (H j) (x j) (s j)) K : ℝ) ≤
        kS * ((f (x 0) - low) / epsilon ^ 2) := by
  obtain ⟨kS, kA, kB, kC, hs, _, _, _, hh⟩ :=
    h.1.exists_complexity_constants hf.hasFDerivAt hf.lipschitz hf.2.1 hB.2 hlow
  refine ⟨kS, hs, ?_⟩
  intro epsilon he
  obtain ⟨K, hk, hfirst, _, hgrad⟩ := hh epsilon he
  exact ⟨K, hk, hfirst, by linarith only [hgrad]⟩

/-- Theorem 2.3.7: first-order TR1 function and gradient budgets, counting initialization,
rejected trials and cached gradients, with constants chosen independently of epsilon. -/
theorem theorem_2_3_7 (h : algorithm_2_3_1 p f H x s delta) {L B low : ℝ}
    (hf : assumption_f_gL f L) (hB : trustRegionAssumptions H B) (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kB kC : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kB ∧ 0 < kC ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ,
        approximateFirstOrderMinimizer f epsilon (x K) ∧
        (∀ j < K, epsilon < ‖gradient f (x j)‖) ∧
        (K : ℝ) + 1 ≤ kA * ((f (x 0) - low) / epsilon ^ 2) +
          kB * |Real.log epsilon| + kC ∧
        (Optimization.ParameterUpdates.successCount
          (fun j => p.eta1 ≤ ratio f (gradient f (x j)) (H j) (x j) (s j)) K : ℝ) + 1 ≤
          kS * ((f (x 0) - low) / epsilon ^ 2) + 1 :=
  h.1.exists_complexity_constants hf.hasFDerivAt hf.lipschitz hf.2.1 hB.2 hlow

end CartisGouldToint.Chapter02.Section03

namespace CartisGouldToint.Chapter02.Section03

/-- The source's Cauchy-point condition is exactly the general backbone condition. -/
theorem isCauchyPoint_iff_backbone {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {delta : ℝ} {s : EuclideanSpace ℝ (Fin n)} :
    IsCauchyPoint g H delta s ↔
      Optimization.QuadraticSubproblem.IsCauchyPoint g H delta s := Iff.rfl

/-- The all-ray comparison is equivalent to the source's comparison with some Cauchy point. -/
theorem cauchy_condition_iff {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n)}
    {H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {delta : ℝ} (hdelta : 0 ≤ delta) (s : EuclideanSpace ℝ (Fin n)) :
    (∀ t : ℝ, 0 ≤ t → t * ‖g‖ ≤ delta →
      Optimization.QuadraticSubproblem.quadratic g H s ≤
        Optimization.QuadraticSubproblem.quadratic g H (-(t • g))) ↔
      ∃ sC : EuclideanSpace ℝ (Fin n), IsCauchyPoint g H delta sC ∧
        Optimization.QuadraticSubproblem.quadratic g H s ≤
          Optimization.QuadraticSubproblem.quadratic g H sC :=
  Optimization.QuadraticSubproblem.le_all_ray_iff_exists_isCauchyPoint hdelta s

end CartisGouldToint.Chapter02.Section03

namespace CartisGouldToint.Chapter02.Section03
open Optimization.TrustRegion

/-- Every symmetric model sequence admits a lawful TR1 trace from the specified initial data. -/
theorem algorithm_2_3_1_exists {n : ℕ} (p : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ k, (H k).IsSymmetric) (x0 : EuclideanSpace ℝ (Fin n))
    {delta0 : ℝ} (hd : 0 < delta0) :
    ∃ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (delta : ℕ → ℝ),
      x 0 = x0 ∧ delta 0 = delta0 ∧ algorithm_2_3_1 p f H x s delta := by
  obtain ⟨x, s, delta, hx, hr, hrun⟩ := exists_isRun p f (gradient f) H x0 hd
  exact ⟨x, s, delta, hx, hr, hrun, hH⟩

/-- Every lawful TR1 step satisfies the textbook's comparison to an actual Cauchy point. -/
theorem algorithm_2_3_1_cauchy_step {n : ℕ} {p : Parameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {delta : ℕ → ℝ}
    (h : algorithm_2_3_1 p f H x s delta) (k : ℕ) :
    ∃ sC : EuclideanSpace ℝ (Fin n), IsCauchyPoint (gradient f (x k)) (H k) (delta k) sC ∧
      quadratic (gradient f (x k)) (H k) (s k) ≤ quadratic (gradient f (x k)) (H k) sC :=
  h.1.exists_cauchyPoint k

end CartisGouldToint.Chapter02.Section03

namespace CartisGouldToint.Chapter02.Section03
open Section01 Optimization.TrustRegion

/-- Theorem 2.3.8: a family of legal TR1 runs requires at least `ε⁻²` objective
and gradient evaluations before the first approximate first-order minimizer. The
Lipschitz, model and initial objective-gap bounds are fixed before `ε` is chosen.
The model operators are identities and all active iterations are successful. -/
theorem theorem_2_3_8 :
    ∃ (p : Parameters) (L B : ℝ), 1 ≤ L ∧ 0 < B ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (K : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (delta : ℕ → ℝ),
        assumption_f_Bb f ∧ assumption_f_gL f L ∧
        (∀ y, -B ≤ f y) ∧ f (x 0) = 0 ∧ x 0 = 0 ∧ delta 0 = 2 ∧
        trustRegionAssumptions (n := 1) (fun _ => ContinuousLinearMap.id ℝ _) 1 ∧
        algorithm_2_3_1 p f (fun _ => ContinuousLinearMap.id ℝ _) x s delta ∧
        (∀ k < K, ε < ‖gradient f (x k)‖) ∧
        approximateFirstOrderMinimizer f ε (x K) ∧
        1 / ε ^ 2 ≤ (K : ℝ) + 1 ∧
        1 / ε ^ 2 ≤ (Optimization.ParameterUpdates.successCount
          (fun k => p.eta1 ≤ ratio f (gradient f (x k))
            (ContinuousLinearMap.id ℝ _) (x k) (s k)) K : ℝ) + 1 := by
  obtain ⟨L, B, hfamily⟩ := exists_sharp_firstOrder_family
  refine ⟨sharpParameters, max (L : ℝ) 1, (B : ℝ) + 1, le_max_right _ _,
    by positivity, ?_⟩
  intro ε hε hεone
  obtain ⟨f, K, x, s, delta, hf, hLip, hb, hf0, hx0, hd0, hrun,
    hfirst, hterminal, hcount, hK⟩ := hfamily ε hε hεone
  have hlow (y) : -((B : ℝ) + 1) ≤ f y := by
    have hh := (abs_le.mp (hb y)).1
    linarith
  refine ⟨f, K, x, s, delta, assumption_f_Bb_iff.mpr ⟨_, hlow⟩,
    ⟨hf, le_max_right _ _, ?_⟩, hlow, hf0, hx0, hd0, ?_, ⟨hrun, ?_⟩,
    hfirst, hterminal, by linarith, ?_⟩
  · intro y z
    exact (hLip.norm_sub_le y z).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · refine ⟨by norm_num, fun _ => ?_⟩
    exact ContinuousLinearMap.norm_id_le
  · intro k y z
    rfl
  · rw [hcount]
    linarith

end CartisGouldToint.Chapter02.Section03
