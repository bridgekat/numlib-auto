/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter14.Section03
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Augmented Lagrangian methods -/

open Filter Topology

namespace ConnGouldToint.Chapter14

variable {G F : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The shared data and stopping tests of Algorithms 14.4.1 and 14.4.3.
Starting points and the approximately minimized iterates are supplied by the run. -/
structure AugmentedLagrangianRun (f : G → ℝ) (c : G → F) where
  start : ℕ → G
  iterate : ℕ → G
  multiplier : ℕ → F
  parameter : ℕ → ℝ
  optimalityTolerance : ℕ → ℝ
  feasibilityTolerance : ℕ → ℝ
  reduction : ℝ
  reduction_pos : 0 < reduction
  reduction_lt_one : reduction < 1
  parameter_pos : ∀ k, 0 < parameter k
  parameter_zero_lt_one : parameter 0 < 1
  optimalityTolerance_pos : ∀ k, 0 < optimalityTolerance k
  feasibilityTolerance_pos : ∀ k, 0 < feasibilityTolerance k
  optimalityTolerance_tendsto : Tendsto optimalityTolerance atTop (𝓝 0)
  feasibilityTolerance_tendsto : Tendsto feasibilityTolerance atTop (𝓝 0)
  residual_le : ∀ k,
    ‖fderiv ℝ (augmentedLagrangian f c (multiplier k) (parameter k)) (iterate k)‖ ≤
      optimalityTolerance k
  parameter_le : ∀ k, parameter (k + 1) ≤ parameter k
  parameter_reduce : ∀ k, feasibilityTolerance k < ‖c (iterate k)‖ →
    parameter (k + 1) ≤ reduction * parameter k

namespace AugmentedLagrangianRun

variable {f : G → ℝ} {c : G → F} (run : AugmentedLagrangianRun f c)

/-- Algorithm 14.4.1 uses the first-order estimate on Step 2 and keeps
its current multiplier on Step 3. -/
def IsBasic : Prop :=
  ∀ k, run.multiplier (k + 1) =
    if ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k then
      firstOrderMultiplier c (run.multiplier k) (run.parameter k) (run.iterate k)
    else run.multiplier k

/-- Algorithm 14.4.3 accepts any proposed multiplier satisfying the
safeguard, on either branch. The candidate for iteration `k+1` is indexed
by `k` in the supplied proposal sequence. -/
def IsAlternative (proposal : ℕ → F) (ν γ : ℝ) (θ : ℕ → ℝ) : Prop :=
  0 < ν ∧ 0 < γ ∧ γ < 1 ∧ (∀ k, 0 ≤ θ k) ∧ Tendsto θ atTop (𝓝 0) ∧
    ∀ k, run.multiplier (k + 1) =
      if ‖proposal k‖ ≤ ν * (run.parameter (k + 1)) ^ (-γ) + θ (k + 1) then
        proposal k
      else run.multiplier k

/-- The reset and multiplicative tolerance updates of Algorithm 14.4.2. -/
def HasToleranceUpdates (ω η αω αη βω βη : ℝ) : Prop :=
  0 < ω ∧ 0 < η ∧ 0 < αω ∧ 0 < αη ∧ 0 < βω ∧ 0 < βη ∧
    run.optimalityTolerance 0 = ω * run.parameter 0 ^ αω ∧
    run.feasibilityTolerance 0 = η * run.parameter 0 ^ αη ∧
    ∀ k,
      if ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k then
        run.optimalityTolerance (k + 1) =
          run.optimalityTolerance k * run.parameter (k + 1) ^ βω ∧
        run.feasibilityTolerance (k + 1) =
          run.feasibilityTolerance k * run.parameter (k + 1) ^ βη
      else
        run.optimalityTolerance (k + 1) = ω * run.parameter (k + 1) ^ αω ∧
        run.feasibilityTolerance (k + 1) = η * run.parameter (k + 1) ^ αη

/-- The AA.9 budget between consecutive Step 3 indices. The final failed
test is included in the tolerance sum, as in the source. -/
def HasReductionBudget (r : ℕ → ℕ) (κ α : ℝ) : Prop :=
  StrictMono r ∧ 0 < κ ∧ 0 < α ∧
    (∀ i, run.feasibilityTolerance (r i) < ‖c (run.iterate (r i))‖) ∧
    (∀ i k, r i < k → k < r (i + 1) → ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k) ∧
    ∀ i, ∑ k ∈ Finset.Ioc (r i) (r (i + 1)), run.feasibilityTolerance k ≤
      κ * run.parameter (r i + 1) ^ α

/-- AA.10 requires that sufficiently late Step 2 iterations keep the penalty fixed. -/
def EventuallyKeepsPenalty : Prop :=
  ∀ᶠ k in atTop, ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k →
    run.parameter (k + 1) = run.parameter k

end AugmentedLagrangianRun

variable {f : G → ℝ} {c : G → F}

/-- Lemma 14.4.4. The safeguarded multiplier times the penalty parameter
tends to zero, whether or not the proposed estimates are accepted infinitely often. -/
theorem lemma_14_4_4 (run : AugmentedLagrangianRun f c) {proposal : ℕ → F}
    {ν γ : ℝ} {θ : ℕ → ℝ} (h : run.IsAlternative proposal ν γ θ)
    (hμ : Tendsto run.parameter atTop (𝓝 0)) :
    Tendsto (fun k ↦ run.parameter k * ‖run.multiplier k‖) atTop (𝓝 0) := by
  obtain ⟨hν, hγ, hγ₁, _, hθ, hupdate⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hθ.eventually (gt_mem_nhds zero_lt_one))
  let C := ‖run.multiplier N‖
  let cap : ℕ → ℝ := fun k ↦ ν * run.parameter k ^ (-γ) + 1
  have hcap : Monotone cap := by
    intro i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (run.parameter_pos j)
        ((antitone_nat_of_succ_le run.parameter_le) hij) (neg_nonpos.mpr hγ.le)) hν.le) le_rfl
  have hb (k : ℕ) (hk : N ≤ k) : ‖run.multiplier k‖ ≤ max C (cap k) := by
    induction k, hk using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ k hk ih =>
      rw [hupdate k]
      split_ifs with ha
      · exact (ha.trans (add_le_add le_rfl (hN (k + 1) (by omega)).le)).trans (le_max_right _ _)
      · exact ih.trans (max_le_max le_rfl (hcap (Nat.le_succ k)))
  have hpow : Tendsto (fun k ↦ run.parameter k ^ (1 - γ)) atTop (𝓝 0) := by
    have hh := (Real.continuousAt_rpow_const 0 (1 - γ) (Or.inr (by linarith))).tendsto.comp hμ
    simpa only [Function.comp_def, Real.zero_rpow (sub_ne_zero.mpr hγ₁.ne')] using hh
  have hlim : Tendsto (fun k ↦ max (run.parameter k * C)
      (ν * run.parameter k ^ (1 - γ) + run.parameter k)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, zero_add, max_self] using
      (hμ.mul_const C).max ((hpow.const_mul ν).add hμ)
  refine squeeze_zero' (Eventually.of_forall fun k ↦
    mul_nonneg (run.parameter_pos k).le (norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop N] with k hk
  have he : run.parameter k * (run.parameter k ^ (-γ)) = run.parameter k ^ (1 - γ) := by
    rw [sub_eq_add_neg, Real.rpow_add (run.parameter_pos k), Real.rpow_one]
  have hh := mul_le_mul_of_nonneg_left (hb k hk) (run.parameter_pos k).le
  rw [mul_max_of_nonneg _ _ (run.parameter_pos k).le] at hh
  simpa only [cap, mul_add, mul_one, mul_left_comm (run.parameter k) ν, he] using hh

private theorem AugmentedLagrangianRun.parameter_tendsto_of_budget
    (run : AugmentedLagrangianRun f c) {r : ℕ → ℕ} {κ α : ℝ}
    (h : run.HasReductionBudget r κ α) :
    Tendsto run.parameter atTop (𝓝 0) := by
  obtain ⟨hr, _, _, hfail, _, _⟩ := h
  have ha := antitone_nat_of_succ_le run.parameter_le
  have hs (i : ℕ) : run.parameter (r (i + 1)) ≤ run.reduction * run.parameter (r i) :=
    (ha (hr (Nat.lt_succ_self i))).trans (run.parameter_reduce (r i) (hfail i))
  have hg (i : ℕ) : run.parameter (r i) ≤ run.parameter (r 0) * run.reduction ^ i := by
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        _ ≤ run.reduction * run.parameter (r i) := hs i
        _ ≤ run.reduction * (run.parameter (r 0) * run.reduction ^ i) :=
          mul_le_mul_of_nonneg_left ih run.reduction_pos.le
        _ = _ := by rw [pow_succ]; ring
  have hsub : Tendsto (run.parameter ∘ r) atTop (𝓝 0) := by
    refine squeeze_zero (fun i ↦ (run.parameter_pos (r i)).le) hg ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      run.reduction_pos.le run.reduction_lt_one).const_mul (run.parameter (r 0))
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨i, hi⟩ := Metric.tendsto_atTop.1 hsub ε hε
  refine ⟨r i, fun k hk ↦ ?_⟩
  have hε' := hi i le_rfl
  rw [Function.comp_apply, Real.dist_eq, sub_zero, abs_of_pos (run.parameter_pos _)] at hε'
  rw [Real.dist_eq, sub_zero, abs_of_pos (run.parameter_pos _)]
  exact (ha hk).trans_lt hε'

/-- Lemma 14.4.1. The cumulative tolerance budget between successive
penalty reductions controls the scaled multiplier. This also allows
nonincreasing penalty parameters between the designated reductions.
The multiplier update subtracts the constraint term in the printed (14.4.10). -/
theorem lemma_14_4_1 (run : AugmentedLagrangianRun f c) (hbasic : run.IsBasic)
    {r : ℕ → ℕ} {κ α : ℝ} (h : run.HasReductionBudget r κ α) :
    Tendsto (fun k ↦ run.parameter k * ‖run.multiplier k‖) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun k ↦ run.parameter k * ‖run.multiplier k‖
  have ha (k : ℕ) : 0 ≤ a k := mul_nonneg (run.parameter_pos k).le (norm_nonneg _)
  have hμ := run.parameter_tendsto_of_budget h
  obtain ⟨hr, _, hα, hfail, hgood, hbudget⟩ := h
  have hstep (k : ℕ) (hk : ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k) :
      a (k + 1) ≤ a k + run.feasibilityTolerance k := by
    dsimp only [a]
    rw [hbasic k, ite_eq_left hk, firstOrderMultiplier]
    have hscale := mul_le_mul_of_nonneg_right (run.parameter_le k)
      (norm_nonneg (run.multiplier k - (run.parameter k)⁻¹ • c (run.iterate k)))
    refine hscale.trans ?_
    have htri := mul_le_mul_of_nonneg_left (norm_sub_le (run.multiplier k)
      ((run.parameter k)⁻¹ • c (run.iterate k))) (run.parameter_pos k).le
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (run.parameter_pos k).le),
      mul_add, ← mul_assoc, mul_inv_cancel₀ (run.parameter_pos k).ne', one_mul] at htri
    exact htri.trans (add_le_add le_rfl hk)
  have hreset (i : ℕ) : a (r i + 1) ≤ run.reduction * a (r i) := by
    dsimp only [a]
    rw [hbasic (r i), ite_eq_right (not_le.mpr (hfail i)), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (run.parameter_reduce (r i) (hfail i)) (norm_nonneg _)
  have hblock (i k : ℕ) (hl : r i + 1 ≤ k) (hu : k ≤ r (i + 1)) :
      a k ≤ run.reduction * a (r i) + κ * run.parameter (r i + 1) ^ α := by
    have hb (j : ℕ) (hj : r i + 1 ≤ j) :
        j ≤ r (i + 1) → a j ≤ run.reduction * a (r i) +
          ∑ k ∈ Finset.Ico (r i + 1) j, run.feasibilityTolerance k := by
      induction j, hj using Nat.le_induction with
      | base => intro _; simpa using hreset i
      | succ j hj ih =>
        intro hhi
        rw [Finset.sum_Ico_succ_top hj]
        have hh := hstep j (hgood i j (by omega) (by omega))
        linarith only [hh, ih (by omega)]
    refine (hb k hl hu).trans (add_le_add le_rfl ?_)
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ ↦
      (run.feasibilityTolerance_pos j).le)).trans (hbudget i)
    intro j hj
    simp only [Finset.mem_Ico, Finset.mem_Ioc] at hj ⊢
    omega
  let b : ℕ → ℝ := fun i ↦ κ * run.parameter (r i + 1) ^ α
  have hrTop : Tendsto r atTop atTop := hr.tendsto_atTop
  have hbLim : Tendsto b atTop (𝓝 0) := by
    have hp := hμ.comp ((tendsto_add_atTop_nat 1).comp hrTop)
    have ht := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp hp
    simpa only [b, Function.comp_apply, Real.zero_rpow hα.ne', mul_zero] using ht.const_mul κ
  have hrec (i : ℕ) : a (r (i + 1)) ≤ run.reduction * a (r i) + b i :=
    hblock i _ (hr (Nat.lt_succ_self i)) le_rfl
  have hsub : Tendsto (a ∘ r) atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    let d := (1 - run.reduction) * (ε / 2)
    have hd : 0 < d := mul_pos (sub_pos.mpr run.reduction_lt_one) (half_pos hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hbLim.eventually (gt_mem_nhds hd))
    have hgeo (j : ℕ) : a (r (N + j)) ≤ run.reduction ^ j * a (r N) + ε / 2 := by
      induction j with
      | zero => simp; positivity
      | succ j ih =>
        have h₁ := hrec (N + j)
        have h₂ := mul_le_mul_of_nonneg_left ih run.reduction_pos.le
        have h₃ := (hN (N + j) (by omega)).le
        rw [Nat.add_succ, pow_succ]
        dsimp only [d] at h₃
        linarith only [h₁, h₂, h₃,
          mul_add run.reduction (run.reduction ^ j * a (r N)) (ε / 2),
          mul_left_comm run.reduction (run.reduction ^ j) (a (r N)),
          mul_assoc (run.reduction ^ j) run.reduction (a (r N))]
    have hdec := (tendsto_pow_atTop_nhds_zero_of_lt_one
      run.reduction_pos.le run.reduction_lt_one).mul_const (a (r N))
    rw [zero_mul] at hdec
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdec.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N + J, fun k hk ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, Function.comp_apply, abs_of_nonneg (ha _)]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ k by omega)
    linarith only [hgeo j, hJ j (by omega)]
  have hmajor : Tendsto (fun i ↦ run.reduction * a (r i) + b i) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, Function.comp_apply] using (hsub.const_mul run.reduction).add hbLim
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmajor.eventually (gt_mem_nhds hε))
  refine ⟨r N + 1, fun k hk ↦ ?_⟩
  have hex : ∃ i, k ≤ r (i + 1) := by
    obtain ⟨i, hi⟩ := (hrTop.eventually (eventually_ge_atTop k)).exists
    exact ⟨i, hi.trans (hr.monotone (Nat.le_succ i))⟩
  let i := Nat.find hex
  have hui : k ≤ r (i + 1) := Nat.find_spec hex
  have hli : r i + 1 ≤ k := by
    by_cases hz : i = 0
    · rw [hz]
      exact (Nat.succ_le_succ (hr.monotone (Nat.zero_le N))).trans hk
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hz
      by_contra! hn
      have hkr : k ≤ r (j + 1) := by
        change k ≤ r j.succ
        rw [← hj]
        omega
      have hmin : i ≤ j := Nat.find_min' hex hkr
      omega
  have hNi : N ≤ i := by
    by_contra! hn
    exact (not_le.mpr (show r N < k by omega)) (hui.trans (hr.monotone (by omega)))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha k)]
  exact (hblock i k hli hui).trans_lt (hN i hNi)

private theorem AugmentedLagrangianRun.parameter_tendsto_or_feasible
    (run : AugmentedLagrangianRun f c) :
    Tendsto run.parameter atTop (𝓝 0) ∨
      ∀ᶠ k in atTop, ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k := by
  let μstar := ⨅ k, run.parameter k
  have hb : BddBelow (Set.range run.parameter) := ⟨0, by
    rintro _ ⟨k, rfl⟩
    exact (run.parameter_pos k).le⟩
  have hlim := tendsto_atTop_ciInf (antitone_nat_of_succ_le run.parameter_le) hb
  have hn : 0 ≤ μstar := le_ciInf (fun k ↦ (run.parameter_pos k).le)
  rcases hn.eq_or_lt with he | hp
  · exact Or.inl (he ▸ hlim)
  · right
    have hsmall : μstar < μstar / run.reduction :=
      (lt_div_iff₀ run.reduction_pos).2
        ((mul_lt_mul_of_pos_left run.reduction_lt_one hp).trans_eq (mul_one _))
    filter_upwards [hlim.eventually (gt_mem_nhds hsmall)] with k hk
    by_contra! hf
    have hstep := run.parameter_reduce k hf
    have hlo : μstar ≤ run.parameter (k + 1) := ciInf_le hb _
    have hmul := (lt_div_iff₀ run.reduction_pos).1 hk
    linarith

variable [CompleteSpace G] [CompleteSpace F]

private theorem feasible_of_augmented_run [FiniteDimensional ℝ F]
    (run : AugmentedLagrangianRun f c) (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) {xstar : G}
    (hx : Tendsto (run.iterate ∘ r) atTop (𝓝 xstar))
    (hA : Function.Surjective (fderiv ℝ c xstar))
    (hscaled : (¬ ∀ᶠ k in atTop, ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k) →
      Tendsto run.parameter atTop (𝓝 0) → Tendsto (fun k ↦ run.parameter k * ‖run.multiplier k‖) atTop (𝓝 0)) :
    c xstar = 0 := by
  have hω := run.optimalityTolerance_tendsto.comp hr
  have hη := run.feasibilityTolerance_tendsto.comp hr
  have hnorm : Tendsto (fun k ↦ ‖c (run.iterate (r k))‖) atTop (𝓝 ‖c xstar‖) :=
    (hc.continuous.continuousAt.tendsto.comp hx).norm
  suffices ht : Tendsto (fun k ↦ ‖c (run.iterate (r k))‖) atTop (𝓝 0) by
    exact norm_eq_zero.mp (tendsto_nhds_unique hnorm ht)
  by_cases hηbound : ∀ᶠ k in atTop, ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k
  · exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) (hr.eventually hηbound) hη
  · have hμ := run.parameter_tendsto_or_feasible.resolve_right hηbound
    let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
    have hu := multiplierGram_isUnit_of_surjective hA
    obtain ⟨K₁, h₁, K₂, h₂, hb⟩ := lemma_14_2_2_i
      (y := run.multiplier ∘ r) hf hc hu hx
      (fun k ↦ run.parameter_pos (r k)) (fun k ↦ run.residual_le (r k))
    have hμr := hμ.comp hr
    have hscaledr := (hscaled hηbound hμ).comp hr
    have hxnorm := tendsto_iff_norm_sub_tendsto_zero.mp hx
    have hbase := hμr.mul (((hω.const_mul K₁).add_const ‖ystar‖).add
      (hxnorm.const_mul K₂))
    have hlim : Tendsto (fun k ↦ run.parameter (r k) *
        (K₁ * run.optimalityTolerance (r k) + ‖ystar‖ + K₂ * ‖run.iterate (r k) - xstar‖) +
        run.parameter (r k) * ‖run.multiplier (r k)‖) atTop (𝓝 0) := by
      simpa only [zero_mul, zero_add, Function.comp_apply] using hbase.add hscaledr
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [hb] with k hk
    have htri : ‖run.multiplier (r k) - ystar‖ ≤ ‖run.multiplier (r k)‖ + ‖ystar‖ :=
      norm_sub_le _ _
    have hprod := mul_le_mul_of_nonneg_left htri (run.parameter_pos (r k)).le
    have hk := hk.2.2
    change ‖c (run.iterate (r k))‖ ≤ run.parameter (r k) *
      (K₁ * run.optimalityTolerance (r k) + ‖run.multiplier (r k) - ystar‖ +
        K₂ * ‖run.iterate (r k) - xstar‖) at hk
    linarith only [hk, hprod]

/-- Theorem 14.4.2. In the vanishing-penalty branch the proof uses the
AA.9 budget on the successive reductions. Each full-row-rank subsequential
limit is feasible and stationary, and both multiplier estimates converge. -/
theorem theorem_14_4_2 [FiniteDimensional ℝ F] (run : AugmentedLagrangianRun f c)
    (h : run.IsBasic)
    (hbudget : (¬ ∀ᶠ k in atTop, ‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k) →
      ∃ (s : ℕ → ℕ) (κ α : ℝ), run.HasReductionBudget s κ α)
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) {xstar : G}
    (hx : Tendsto (run.iterate ∘ r) atTop (𝓝 xstar))
    (hA : Function.Surjective (fderiv ℝ c xstar)) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    IsEqualityKKT f c xstar (ls xstar) ∧
      Tendsto (fun k ↦ firstOrderMultiplier c (run.multiplier (r k)) (run.parameter (r k))
        (run.iterate (r k))) atTop (𝓝 (ls xstar)) ∧
      Tendsto (ls ∘ run.iterate ∘ r) atTop (𝓝 (ls xstar)) := by
  have hfeas := feasible_of_augmented_run run hf hc hr hx hA fun hfail _ ↦ by
    obtain ⟨s, κ, α, hs⟩ := hbudget hfail
    exact lemma_14_4_1 run h hs
  obtain ⟨hy, hls, hkkt⟩ := lemma_14_2_2_ii (y := run.multiplier ∘ r) hf hc
    (multiplierGram_isUnit_of_surjective hA) hx (fun k ↦ run.parameter_pos (r k))
    (fun k ↦ run.residual_le (r k)) (run.optimalityTolerance_tendsto.comp hr)
  exact ⟨hkkt hfeas, hy, hls⟩

/-- Theorem 14.4.5. Every subsequential limit with a surjective constraint
Jacobian is feasible and stationary. Both multiplier estimates converge. -/
theorem theorem_14_4_5 [FiniteDimensional ℝ F] (run : AugmentedLagrangianRun f c)
    {proposal : ℕ → F} {ν γ : ℝ} {θ : ℕ → ℝ} (h : run.IsAlternative proposal ν γ θ)
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) {xstar : G}
    (hx : Tendsto (run.iterate ∘ r) atTop (𝓝 xstar))
    (hA : Function.Surjective (fderiv ℝ c xstar)) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    IsEqualityKKT f c xstar (ls xstar) ∧
      Tendsto (fun k ↦ firstOrderMultiplier c (run.multiplier (r k)) (run.parameter (r k))
        (run.iterate (r k))) atTop (𝓝 (ls xstar)) ∧
      Tendsto (ls ∘ run.iterate ∘ r) atTop (𝓝 (ls xstar)) := by
  have hfeas := feasible_of_augmented_run run hf hc hr hx hA (fun _ ↦ lemma_14_4_4 run h)
  obtain ⟨hy, hls, hkkt⟩ := lemma_14_2_2_ii (y := run.multiplier ∘ r) hf hc
    (multiplierGram_isUnit_of_surjective hA) hx (fun k ↦ run.parameter_pos (r k))
    (fun k ↦ run.residual_le (r k)) (run.optimalityTolerance_tendsto.comp hr)
  exact ⟨hkkt hfeas, hy, hls⟩

/-- Corollary 14.4.6. Any proposed estimate with the error bound (14.4.32)
inherits the small-parameter bounds in Lemma 14.2.2(iii). -/
theorem corollary_14_4_6 [FiniteDimensional ℝ F]
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) {xstar : G}
    (hfeas : c xstar = 0) {x : ℕ → G} (hx : Tendsto x atTop (𝓝 xstar))
    {y proposal : ℕ → F} {μ ω : ℕ → ℝ} (hμ : ∀ k, 0 < μ k)
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c (y k) (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0))
    (hK : IsUnit (penaltyKKTJacobian f c
      (xstar, leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar))))
    {K₁₃ K₁₄ : ℝ} (h₁₃ : 0 < K₁₃) (_h₁₄ : 0 < K₁₄)
    (hproposal : ∀ᶠ k in atTop,
      ‖proposal k - leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)‖ ≤
        K₁₃ * ‖x k - xstar‖ + K₁₄ * ω k) :
    let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
    ∃ μmax > 0, ∃ K₃ > 0, ∃ K₄ > 0, ∃ K₅ > 0, ∃ K₆ > 0,
      ∀ᶠ k in atTop, μ k ≤ μmax →
        ‖x k - xstar‖ ≤ K₃ * ω k + K₄ * μ k * ‖y k - ystar‖ ∧
        ‖proposal k - ystar‖ ≤ K₅ * ω k + K₆ * μ k * ‖y k - ystar‖ ∧
        ‖c (x k)‖ ≤ K₅ * μ k * ω k + (μ k + K₆ * μ k ^ 2) * ‖y k - ystar‖ := by
  dsimp only
  obtain ⟨μmax, hmax, K₃, h₃, K₄, h₄, K₅, h₅, K₆, h₆, K₇, h₇, hb⟩ :=
    lemma_14_2_2_iii hf hc hfeas hx hμ hres hω hK
  refine ⟨μmax, hmax, K₃, h₃, K₄, h₄, max K₅ (K₁₃ * K₃ + K₁₄), h₅.trans_le (le_max_left _ _),
    max K₆ (K₁₃ * K₄), h₆.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hb, hproposal] with k hk hp
  intro hsmall
  obtain ⟨hX, _, _, hC⟩ := hk hsmall
  have hw : 0 ≤ ω k := (norm_nonneg _).trans (hres k)
  have hy : 0 ≤ ‖y k - leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)‖ :=
    norm_nonneg _
  have hμy := mul_nonneg (hμ k).le hy
  refine ⟨hX, hp.trans ?_, hC.trans ?_⟩
  · have he := mul_le_mul_of_nonneg_left hX h₁₃.le
    have hω' := mul_le_mul_of_nonneg_right (le_max_right K₅ (K₁₃ * K₃ + K₁₄)) hw
    have hY' := mul_le_mul_of_nonneg_right (le_max_right K₆ (K₁₃ * K₄)) hμy
    linarith only [he, hω', hY']
  · refine add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left K₅ (K₁₃ * K₃ + K₁₄)) (hμ k).le) hw) ?_
    exact mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left K₆ (K₁₃ * K₄))
        (sq_nonneg _))) hy

private theorem rpow_tendsto_zero {μ : ℕ → ℝ} (hμ : Tendsto μ atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) : Tendsto (fun k ↦ μ k ^ a) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.zero_rpow ha.ne'] using
    (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.comp hμ

omit [CompleteSpace G] [CompleteSpace F] in
private theorem penalty_bounded_of_local_updates
    (run : AugmentedLagrangianRun f c) {ω η αω αη βω βη : ℝ}
    (ht : run.HasToleranceUpdates ω η αω αη βω βη)
    (hkeep : run.EventuallyKeepsPenalty)
    (ha₁ : αη < 1) (ha₂ : αη < αω)
    (hb₁ : βη < 1) (hb₂ : βη < βω)
    (hlocal : Tendsto run.parameter atTop (𝓝 0) →
      ∃ (e : ℕ → ℝ) (B K : ℝ), 0 ≤ B ∧ 0 < K ∧
        ∀ᶠ k in atTop, e k ≤ B ∧
          (‖c (run.iterate k)‖ ≤ run.feasibilityTolerance k →
            e (k + 1) ≤ K * run.optimalityTolerance k + K * run.parameter k * e k) ∧
          ‖c (run.iterate k)‖ ≤ K * run.parameter k * run.optimalityTolerance k +
            (run.parameter k + K * run.parameter k ^ 2) * e k) :
    ∃ μstar > 0, ∀ k, μstar ≤ run.parameter k := by
  by_contra! hn
  let μ := run.parameter
  let ωk := run.optimalityTolerance
  let ηk := run.feasibilityTolerance
  let Ck := fun k ↦ ‖c (run.iterate k)‖
  have hanti := antitone_nat_of_succ_le run.parameter_le
  have hμ : Tendsto μ atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    obtain ⟨n, hn'⟩ := hn ε hε
    refine ⟨n, fun k hk ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (run.parameter_pos k)]
    exact (hanti hk).trans_lt hn'
  have hfail : ∃ᶠ k in atTop, ηk k < Ck k := by
    simp only [← not_le, ← not_eventually]
    intro he
    obtain ⟨N, hN⟩ := eventually_atTop.mp (he.and hkeep)
    have hconstant (j : ℕ) : μ (N + j) = μ N := by
      induction j with
      | zero => rfl
      | succ j ih =>
        change run.parameter (N + j + 1) = μ N
        exact ((hN (N + j) (by omega)).2 (hN (N + j) (by omega)).1).trans ih
    obtain ⟨k, hk⟩ := hn (μ N) (run.parameter_pos N)
    rcases le_total k N with hkn | hnk
    · exact (not_lt_of_ge (hanti hkn)) hk
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
      exact (lt_irrefl _ (hconstant j ▸ hk))
  obtain ⟨e, B, K, hB, hK, he⟩ := hlocal hμ
  obtain ⟨hω, hη, hαω, _, _, hβη, _, _, hup⟩ := ht
  let q := fun k ↦ μ k ^ βη
  let W := fun k ↦ ω * μ k ^ αω
  let D := fun k ↦ B + 2 * K * W k / q k
  have hq (k : ℕ) : 0 < q k := Real.rpow_pos_of_pos (run.parameter_pos k) _
  have hW (k : ℕ) : 0 ≤ W k := mul_nonneg hω.le (Real.rpow_nonneg (run.parameter_pos k).le _)
  have hD (k : ℕ) : 0 ≤ D k :=
    add_nonneg hB (div_nonneg (mul_nonneg (by positivity) (hW k)) (hq k).le)
  have hμq : ∀ᶠ k in atTop, K * μ k ≤ q k / 2 := by
    have hlim := (rpow_tendsto_zero hμ (sub_pos.mpr hb₁)).const_mul K
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
    change K * μ k ^ (1 - βη) < 1 / 2 at hk
    rw [Real.rpow_sub (run.parameter_pos k), Real.rpow_one, ← mul_div_assoc] at hk
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
      have hh := (div_lt_iff₀ (hq k)).1 hk
      linarith)
  have hsmall : ∀ᶠ k in atTop, μ k * (K * W k + 2 * D k) ≤ η * μ k ^ αη := by
    have ht₁ := (rpow_tendsto_zero hμ (by linarith : 0 < 1 + αω - αη)).const_mul (K * ω)
    have ht₂ := (rpow_tendsto_zero hμ (sub_pos.mpr ha₁)).const_mul (2 * B)
    have ht₃ := (rpow_tendsto_zero hμ (by linarith : 0 < 1 + αω - βη - αη)).const_mul (4 * K * ω)
    have hlim := (ht₁.add ht₂).add ht₃
    simp only [mul_zero, add_zero] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hη)] with k hk
    let m := μ k
    have hm : 0 < m := run.parameter_pos k
    have hα : 0 < m ^ αη := Real.rpow_pos_of_pos hm _
    change K * ω * m ^ (1 + αω - αη) + 2 * B * m ^ (1 - αη) +
      4 * K * ω * m ^ (1 + αω - βη - αη) < η at hk
    have hm₁ : m ^ (1 + αω - αη) * m ^ αη = m * m ^ αω := by
      rw [← Real.rpow_add hm, sub_add_cancel, Real.rpow_add hm, Real.rpow_one]
    have hm₂ : m ^ (1 - αη) * m ^ αη = m := by
      rw [← Real.rpow_add hm, sub_add_cancel, Real.rpow_one]
    have hm₃ : m ^ (1 + αω - βη - αη) * m ^ αη = (m * m ^ αω) / m ^ βη := by
      rw [← Real.rpow_add hm, sub_add_cancel, Real.rpow_sub hm, Real.rpow_add hm, Real.rpow_one]
    have hh := mul_le_mul_of_nonneg_right hk.le hα.le
    rw [add_mul, add_mul, mul_assoc (K * ω), mul_assoc (2 * B),
      mul_assoc (4 * K * ω), hm₁, hm₂, hm₃] at hh
    change m * (K * (ω * m ^ αω) + 2 * (B + 2 * K * (ω * m ^ αω) / m ^ βη)) ≤ η * m ^ αη
    convert hh using 1; ring
  have hKμ : ∀ᶠ k in atTop, K * μ k ≤ 1 := by
    have hh := hμ.const_mul K
    rw [mul_zero] at hh
    exact (hh.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h ↦ h.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (he.and (hkeep.and (hμq.and (hsmall.and hKμ))))
  obtain ⟨j, hj, hjf⟩ := (hfail.and_eventually (eventually_ge_atTop N)).exists
  let n := j + 1
  have hnN : N ≤ n := by dsimp [n]; omega
  have hreset := hup j
  rw [ite_eq_right (not_le.mpr hj)] at hreset
  have hpow_nonneg (t : ℕ) : 0 ≤ q n ^ t := pow_nonneg (hq n).le _
  have hstable (t : ℕ) :
      μ (n + t) = μ n ∧
      ωk (n + t) ≤ W n * q n ^ t ∧
      ηk (n + t) = η * μ n ^ αη * q n ^ t ∧
      e (n + t) ≤ D n * q n ^ t := by
    induction t with
    | zero =>
      simp only [Nat.add_zero, pow_zero, mul_one]
      exact ⟨True.intro, hreset.1.le, hreset.2,
        (hN n hnN).1.1.trans (le_add_of_nonneg_right (by
          exact div_nonneg (mul_nonneg (by positivity) (hW n)) (hq n).le))⟩
    | succ t ih =>
      let k := n + t
      have hkN : N ≤ k := by dsimp [k]; omega
      obtain ⟨hμk, hωk, hηk, hek⟩ := ih
      have hKμk : K * μ k ≤ 1 := by
        rw [show μ k = μ n from hμk]
        exact (hN n hnN).2.2.2.2
      have hc₀ := (hN k hkN).1.2.2
      have hc₁ : μ k + K * μ k ^ 2 ≤ 2 * μ k := by
        have hh := mul_le_mul_of_nonneg_right hKμk (run.parameter_pos k).le
        nlinarith only [hh]
      have hc₂ := mul_le_mul_of_nonneg_left hek
        (show 0 ≤ μ k + K * μ k ^ 2 by
          exact add_nonneg (run.parameter_pos k).le (mul_nonneg hK.le (sq_nonneg _)))
      have hc₃ := mul_le_mul_of_nonneg_right hc₁
        (mul_nonneg (hD n) (hpow_nonneg t))
      have hc₄ := mul_le_mul_of_nonneg_left hωk (mul_nonneg hK.le (run.parameter_pos k).le)
      have hc₅ := mul_le_mul_of_nonneg_right ((hN n hnN).2.2.2.1) (hpow_nonneg t)
      have hcGood : Ck k ≤ ηk k := by
        change ωk k ≤ W n * q n ^ t at hωk
        change Ck k ≤ K * μ k * ωk k + (μ k + K * μ k ^ 2) * e k at hc₀
        change ηk k = η * μ n ^ αη * q n ^ t at hηk
        change μ k = μ n at hμk
        change K * μ k * ωk k ≤ K * μ k * (W n * q n ^ t) at hc₄
        rw [hμk] at hc₀ hc₂ hc₃ hc₄
        rw [hηk]
        nlinarith only [hc₀, hc₂, hc₃, hc₄, hc₅]
      have hμnext := (hN k hkN).2.1 hcGood
      have hτ := hup k
      rw [ite_eq_left hcGood, hμnext, show run.parameter k = μ n from hμk] at hτ
      have hpow : μ n ^ βω ≤ q n :=
        Real.rpow_le_rpow_of_exponent_ge (run.parameter_pos n)
          (hanti (Nat.zero_le n) |>.trans run.parameter_zero_lt_one.le) hb₂.le
      have hhalf := (hN n hnN).2.2.1
      have hωhalf : K * W n ≤ q n / 2 * D n := by
        have hh : (2 * K * W n / q n) * q n = 2 * K * W n :=
          div_mul_cancel₀ _ (hq n).ne'
        dsimp only [D]
        nlinarith only [hh, mul_nonneg hB (hq n).le]
      change μ (k + 1) = μ n ∧ ωk (k + 1) ≤ W n * q n ^ (t + 1) ∧
        ηk (k + 1) = η * μ n ^ αη * q n ^ (t + 1) ∧
        e (k + 1) ≤ D n * q n ^ (t + 1)
      refine ⟨hμnext.trans hμk, ?_, ?_, ?_⟩
      · rw [show ωk (k + 1) = ωk k * μ n ^ βω from hτ.1, pow_succ, ← mul_assoc]
        exact mul_le_mul hωk hpow (Real.rpow_nonneg (run.parameter_pos n).le _)
          (mul_nonneg (hW n) (hpow_nonneg t))
      · rw [show ηk (k + 1) = ηk k * μ n ^ βη from hτ.2, hηk, pow_succ, ← mul_assoc]
      · have hrec := (hN k hkN).1.2.1 hcGood
        change e (k + 1) ≤ K * ωk k + K * μ k * e k at hrec
        rw [hμk] at hrec
        have h₁ := mul_le_mul_of_nonneg_left hωk hK.le
        have h₂ := mul_le_mul_of_nonneg_left hek (mul_nonneg hK.le (run.parameter_pos n).le)
        have h₃ := mul_le_mul_of_nonneg_right hhalf (mul_nonneg (hD n) (hpow_nonneg t))
        have h₄ := mul_le_mul_of_nonneg_right hωhalf (hpow_nonneg t)
        rw [pow_succ]
        nlinarith only [hrec, h₁, h₂, h₃, h₄]
  obtain ⟨k, hk⟩ := hn (μ n) (run.parameter_pos n)
  rcases le_total k n with hkn | hnk
  · exact (not_lt_of_ge (hanti hkn)) hk
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnk
    exact (lt_irrefl _ ((hstable t).1 ▸ hk))

omit [InnerProductSpace ℝ F] [CompleteSpace F] in
private theorem multiplier_error_bounded {y proposal : ℕ → F} {ystar : F}
    (hproposal : Tendsto proposal atTop (𝓝 ystar))
    (hupdate : ∀ k, y (k + 1) = y k ∨ y (k + 1) = proposal k) :
    ∃ B ≥ 0, ∀ᶠ k in atTop, ‖y k - ystar‖ ≤ B := by
  have hl := tendsto_iff_norm_sub_tendsto_zero.1 hproposal
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hl.eventually (gt_mem_nhds zero_lt_one))
  let B := max ‖y N - ystar‖ 1
  refine ⟨B, zero_le_one.trans (le_max_right _ _), eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_max_left _ _
  | succ k hk ih =>
    rcases hupdate k with he | he
    · rwa [he]
    · rw [he]
      exact (hN k hk).le.trans (le_max_right _ _)

/-- Theorem 14.4.3. With the specified tolerance exponents and eventually
constant penalties on Step 2, the basic augmented-Lagrangian penalty
sequence stays bounded away from zero. -/
theorem theorem_14_4_3 [FiniteDimensional ℝ F] (run : AugmentedLagrangianRun f c)
    (hbasic : run.IsBasic) {ω η αω αη βω βη : ℝ}
    (ht : run.HasToleranceUpdates ω η αω αη βω βη) (hkeep : run.EventuallyKeepsPenalty)
    (ha : αη < min 1 αω) (hb : βη < min 1 βω)
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {xstar : G} (hx : Tendsto run.iterate atTop (𝓝 xstar))
    (hK : IsUnit (penaltyKKTJacobian f c
      (xstar, leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)))) :
    ∃ μstar > 0, ∀ k, μstar ≤ run.parameter k := by
  let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
  let proposal := fun k ↦ firstOrderMultiplier c (run.multiplier k) (run.parameter k) (run.iterate k)
  have hA := surjective_of_penaltyKKTJacobian_isUnit hK
  have hprop : Tendsto proposal atTop (𝓝 ystar) :=
    (lemma_14_2_2_ii hf hc (multiplierGram_isUnit_of_surjective hA) hx
      run.parameter_pos run.residual_le run.optimalityTolerance_tendsto).1
  obtain ⟨B, hB, hbound⟩ := multiplier_error_bounded hprop (y := run.multiplier) (fun k ↦ by
    rw [hbasic k]
    split_ifs <;> simp [proposal])
  apply penalty_bounded_of_local_updates run ht hkeep
    (ha.trans_le (min_le_left _ _)) (ha.trans_le (min_le_right _ _))
    (hb.trans_le (min_le_left _ _)) (hb.trans_le (min_le_right _ _))
  intro hμ
  have hfeas := feasible_of_augmented_run run hf hc tendsto_id hx hA (fun _ hp ↦ by
    have hh := hp.mul_const B
    rw [zero_mul] at hh
    have he : Tendsto (fun k ↦ run.parameter k * ‖run.multiplier k - ystar‖) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun k ↦
        mul_nonneg (run.parameter_pos k).le (norm_nonneg _))
        (hbound.mono fun k hk ↦ mul_le_mul_of_nonneg_left hk (run.parameter_pos k).le) hh
    have hh' := hp.mul_const ‖ystar‖
    rw [zero_mul] at hh'
    refine squeeze_zero' (Eventually.of_forall fun k ↦
      mul_nonneg (run.parameter_pos k).le (norm_nonneg _)) ?_ (by simpa using he.add hh')
    exact Eventually.of_forall fun k ↦ by
      have hh := norm_add_le (run.multiplier k - ystar) ystar
      rw [sub_add_cancel] at hh
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hh (run.parameter_pos k).le)
  obtain ⟨μmax, hmax, _, _, _, _, K₅, h₅, K₆, _, _, _, hbounds⟩ :=
    lemma_14_2_2_iii hf hc hfeas hx run.parameter_pos run.residual_le
      run.optimalityTolerance_tendsto hK
  let K := max K₅ K₆
  refine ⟨fun k ↦ ‖run.multiplier k - ystar‖, B, K, hB, h₅.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hbound, hbounds, hμ.eventually (gt_mem_nhds hmax)] with k hbk hbk' hmk
  refine ⟨hbk, ?_, ?_⟩
  · intro hg
    rw [hbasic k, ite_eq_left hg]
    exact (hbk' hmk.le).2.1.trans (add_le_add
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (run.optimalityTolerance_pos k).le)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (run.parameter_pos k).le) (norm_nonneg _)))
  · exact (hbk' hmk.le).2.2.2.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (run.parameter_pos k).le)
        (run.optimalityTolerance_pos k).le)
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))) (norm_nonneg _)))

/-- Theorem 14.4.7. The alternative algorithm also keeps a positive
penalty lower bound when the proposed estimates satisfy (14.4.32). -/
theorem theorem_14_4_7 [FiniteDimensional ℝ F] (run : AugmentedLagrangianRun f c)
    {proposal : ℕ → F} {ν γ : ℝ} {θ : ℕ → ℝ} (halt : run.IsAlternative proposal ν γ θ)
    {ω η αω αη βω βη : ℝ} (ht : run.HasToleranceUpdates ω η αω αη βω βη)
    (hkeep : run.EventuallyKeepsPenalty) (ha : αη < min 1 αω) (hb : βη < min 1 βω)
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {xstar : G} (hx : Tendsto run.iterate atTop (𝓝 xstar))
    (hK : IsUnit (penaltyKKTJacobian f c
      (xstar, leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar))))
    {K₁₃ K₁₄ : ℝ} (h₁₃ : 0 < K₁₃) (h₁₄ : 0 < K₁₄)
    (hproposal : ∀ᶠ k in atTop,
      ‖proposal k - leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)‖ ≤
        K₁₃ * ‖run.iterate k - xstar‖ + K₁₄ * run.optimalityTolerance k) :
    ∃ μstar > 0, ∀ k, μstar ≤ run.parameter k := by
  let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
  have hA := surjective_of_penaltyKKTJacobian_isUnit hK
  have hscaled := lemma_14_4_4 run halt
  obtain ⟨hν, hγ, _, hθ, _, hupdate⟩ := halt
  have hprop : Tendsto proposal atTop (𝓝 ystar) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have h₁ := (tendsto_iff_norm_sub_tendsto_zero.1 hx).const_mul K₁₃
    have h₂ := run.optimalityTolerance_tendsto.const_mul K₁₄
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hproposal
      (by simpa only [mul_zero, add_zero] using h₁.add h₂)
  obtain ⟨B, hB, hbound⟩ := multiplier_error_bounded hprop (y := run.multiplier) (fun k ↦ by
    rw [hupdate k]
    split_ifs <;> simp)
  apply penalty_bounded_of_local_updates run ht hkeep
    (ha.trans_le (min_le_left _ _)) (ha.trans_le (min_le_right _ _))
    (hb.trans_le (min_le_left _ _)) (hb.trans_le (min_le_right _ _))
  intro hμ
  have hfeas := feasible_of_augmented_run run hf hc tendsto_id hx hA
    (fun _ ↦ hscaled)
  have haccept : ∀ᶠ k in atTop,
      ‖proposal k‖ ≤ ν * run.parameter (k + 1) ^ (-γ) + θ (k + 1) := by
    let C := ‖ystar‖ + 1
    have hn : ∀ᶠ k in atTop, ‖proposal k‖ ≤ C := by
      have h := tendsto_iff_norm_sub_tendsto_zero.1 hprop
      filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with k hk
      have hh := norm_add_le (proposal k - ystar) ystar
      rw [sub_add_cancel] at hh
      dsimp [C]
      linarith only [hh, hk]
    have hs := (rpow_tendsto_zero (hμ.comp (tendsto_add_atTop_nat 1)) hγ).const_mul C
    rw [mul_zero] at hs
    filter_upwards [hn, hs.eventually (gt_mem_nhds hν)] with k hk hk'
    have hp := Real.rpow_pos_of_pos (run.parameter_pos (k + 1)) γ
    have hcap : C ≤ ν * run.parameter (k + 1) ^ (-γ) := by
      rw [Real.rpow_neg (run.parameter_pos (k + 1)).le, ← div_eq_mul_inv, le_div_iff₀ hp]
      exact hk'.le
    exact hk.trans (hcap.trans (le_add_of_nonneg_right (hθ (k + 1))))
  obtain ⟨μmax, hmax, _, _, _, _, K₅, h₅, K₆, _, hbounds⟩ :=
    corollary_14_4_6 hf hc hfeas hx run.parameter_pos run.residual_le
      run.optimalityTolerance_tendsto hK h₁₃ h₁₄ hproposal
  let K := max K₅ K₆
  refine ⟨fun k ↦ ‖run.multiplier k - ystar‖, B, K, hB, h₅.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hbound, hbounds, hμ.eventually (gt_mem_nhds hmax), haccept]
    with k hbk hbk' hmk hac
  refine ⟨hbk, fun _ ↦ ?_, ?_⟩
  · rw [hupdate k, ite_eq_left hac]
    exact (hbk' hmk.le).2.1.trans (add_le_add
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (run.optimalityTolerance_pos k).le)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (run.parameter_pos k).le) (norm_nonneg _)))
  · exact (hbk' hmk.le).2.2.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (run.parameter_pos k).le)
        (run.optimalityTolerance_pos k).le)
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))) (norm_nonneg _)))

end ConnGouldToint.Chapter14
