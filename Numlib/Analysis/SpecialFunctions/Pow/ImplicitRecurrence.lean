import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Implicit nonnegative power recurrences

The canonical root update is proved to exist uniquely. Nonnegative subsolutions
converge to zero and admit the exact implicit recurrence as an upper envelope,
with superlinear, linear and sublinear regimes.
-/

open Set Filter Topology
namespace ImplicitGap

/-- A positive power plus the identity is strictly increasing on nonnegative inputs. -/
theorem strictMonoOn_update {c τ : ℝ} (hc : 0 ≤ c) (hτ : 0 ≤ τ) :
    StrictMonoOn (fun u : ℝ => u + c * u ^ τ) (Ici 0) := by
  intro a ha b hb hab
  have hh := Real.rpow_le_rpow ha hab.le hτ
  nlinarith

/-- Every nonnegative right side has a unique nonnegative implicit power update. -/
theorem existsUnique_step {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a) :
    ∃! u : ℝ, 0 ≤ u ∧ u + c * u ^ τ = a := by
  have hf : Continuous (fun u : ℝ => u + c * u ^ τ) :=
    continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hτ.le))
  have hzero : (0 : ℝ) + c * 0 ^ τ = 0 := by rw [Real.zero_rpow hτ.ne']; ring
  have hupper : a ≤ a + c * a ^ τ := le_add_of_nonneg_right
    (mul_nonneg hc.le (Real.rpow_nonneg ha τ))
  obtain ⟨u, hu, he⟩ := intermediate_value_Icc ha hf.continuousOn
    (show a ∈ Icc ((0 : ℝ) + c * 0 ^ τ) (a + c * a ^ τ) by rw [hzero]; exact ⟨ha, hupper⟩)
  refine ⟨u, ⟨hu.1, he⟩, ?_⟩
  intro v hv
  exact (strictMonoOn_update hc.le hτ.le).injOn hv.1 hu.1 (hv.2.trans he.symm)

/-- The canonical implicit update; inadmissible parameters have default value zero. -/
noncomputable def step (c τ a : ℝ) : ℝ :=
  if h : 0 < c ∧ 0 < τ ∧ 0 ≤ a then
    (existsUnique_step h.1 h.2.1 h.2.2).exists.choose else 0

/-- The canonical update has its genuine nonnegative solution equation. -/
theorem step_spec {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a) :
    0 ≤ step c τ a ∧ step c τ a + c * step c τ a ^ τ = a := by
  rw [step, dite_eq_left ⟨hc, hτ, ha⟩]
  exact (existsUnique_step hc hτ ha).exists.choose_spec

/-- A positive right side has a strictly positive implicit update. -/
theorem step_pos {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 < a) :
    0 < step c τ a := by
  have hs := step_spec hc hτ ha.le
  by_contra hh
  have hz : step c τ a = 0 := le_antisymm (not_lt.mp hh) hs.1
  rw [hz, Real.zero_rpow hτ.ne'] at hs
  linarith [hs.2]

/-- Any nonnegative subsolution is bounded by the genuine implicit update. -/
theorem le_step {c τ a b : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : b + c * b ^ τ ≤ a) : b ≤ step c τ a := by
  have hs := step_spec hc hτ ha
  by_contra hn
  have hh := strictMonoOn_update hc.le hτ.le hs.1 hb (lt_of_not_ge hn)
  linarith [hs.2]

/-- The actual implicit update is nondecreasing in its nonnegative right side. -/
theorem step_mono {c τ a b : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a) (hab : a ≤ b) :
    step c τ a ≤ step c τ b :=
  le_step hc hτ (ha.trans hab) (step_spec hc hτ ha).1
    ((step_spec hc hτ ha).2.le.trans hab)

/-- The actual implicit power recurrence, initialized at the specified gap. -/
noncomputable def orbit (c τ a : ℝ) (n : ℕ) : ℝ := (step c τ)^[n] a

/-- The canonical orbit starts at its specified initial gap. -/
@[simp] theorem orbit_zero (c τ a : ℝ) : orbit c τ a 0 = a := rfl

/-- Each next orbit value is the canonical implicit update of the previous value. -/
theorem orbit_succ (c τ a : ℝ) (n : ℕ) :
    orbit c τ a (n + 1) = step c τ (orbit c τ a n) := Function.iterate_succ_apply' _ _ _

/-- The genuine implicit recurrence stays nonnegative. -/
theorem orbit_nonneg {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ orbit c τ a n := by
  induction n with
  | zero => exact ha
  | succ n ih => rw [orbit_succ]; exact (step_spec hc hτ ih).1

/-- A positive initial gap gives a positive implicit recurrence at every finite index. -/
theorem orbit_pos {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 < a) (n : ℕ) :
    0 < orbit c τ a n := by
  induction n with
  | zero => exact ha
  | succ n ih => rw [orbit_succ]; exact step_pos hc hτ ih

/-- The exact scalar equation defining every implicit recurrence step. -/
theorem orbit_equation {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a) (n : ℕ) :
    orbit c τ a (n + 1) + c * orbit c τ a (n + 1) ^ τ = orbit c τ a n := by
  rw [orbit_succ]
  exact (step_spec hc hτ (orbit_nonneg hc hτ ha n)).2

/-- Every nonnegative sequence with an implicit power decrease tends to zero. -/
theorem tendsto_zero {b : ℕ → ℝ} {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hb : ∀ n, 0 ≤ b n) (hstep : ∀ n, b (n + 1) + c * b (n + 1) ^ τ ≤ b n) :
    Tendsto b atTop (𝓝 0) := by
  have hanti : Antitone b := antitone_nat_of_succ_le fun n => by
    have hh := hstep n
    have := mul_nonneg hc.le (Real.rpow_nonneg (hb (n + 1)) τ)
    linarith
  have hbound : BddBelow (range b) := ⟨0, by rintro y ⟨n, rfl⟩; exact hb n⟩
  have ht := tendsto_atTop_ciInf hanti hbound
  let l := ⨅ n, b n
  have hl : 0 ≤ l := le_ciInf hb
  have hshift : Tendsto (fun n => b (n + 1)) atTop (𝓝 l) :=
    ht.comp (show Tendsto (fun n : ℕ => n + 1) atTop atTop from
      (strictMono_nat_of_lt_succ (by omega)).tendsto_atTop)
  have hlim := le_of_tendsto_of_tendsto
    ((tendsto_const_nhds (x := c)).mul (hshift.rpow_const (Or.inr hτ.le))) (ht.sub hshift)
    (Eventually.of_forall (fun n => by linarith [hstep n]))
  have hz : l = 0 := by
    by_contra hn
    have hp := mul_pos hc (Real.rpow_pos_of_pos (lt_of_le_of_ne hl (Ne.symm hn)) τ)
    change c * l ^ τ ≤ l - l at hlim
    linarith
  simpa only [← hz] using ht

/-- An implicit power-decreasing sequence lies below the canonical exact recurrence. -/
theorem le_orbit {b : ℕ → ℝ} {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hb : ∀ n, 0 ≤ b n) (hstep : ∀ n, b (n + 1) + c * b (n + 1) ^ τ ≤ b n) (n : ℕ) :
    b n ≤ orbit c τ (b 0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orbit_succ]
    exact (le_step hc hτ (hb n) (hb (n + 1)) (hstep n)).trans
      (step_mono hc hτ (hb n) ih)

/-- The canonical exact recurrence converges to zero. -/
theorem orbit_tendsto_zero {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a) :
    Tendsto (orbit c τ a) atTop (𝓝 0) :=
  tendsto_zero hc hτ (orbit_nonneg hc hτ ha)
    (fun n => (orbit_equation hc hτ ha n).le)

/-- An implicit decrease controls the next gap by a superlinear power when the exponent is
  below one. -/
theorem next_le_power {b : ℕ → ℝ} {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hb : ∀ n, 0 ≤ b n) (hstep : ∀ n, b (n + 1) + c * b (n + 1) ^ τ ≤ b n) (n : ℕ) :
    b (n + 1) ≤ (b n / c) ^ (1 / τ) := by
  have hh : b (n + 1) ^ τ ≤ b n / c :=
    (le_div_iff₀ hc).mpr (by nlinarith [hstep n, hb (n + 1)])
  have ht := Real.rpow_le_rpow (Real.rpow_nonneg (hb (n + 1)) τ) hh
    (show 0 ≤ 1 / τ by positivity)
  rwa [← Real.rpow_mul (hb (n + 1)), mul_one_div_cancel hτ.ne', Real.rpow_one] at ht

/-- Subunit exponents give Q-superlinear convergence, with division interpreted as zero
once the gap vanishes. -/
theorem superlinear {b : ℕ → ℝ} {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hb : ∀ n, 0 ≤ b n) (hstep : ∀ n, b (n + 1) + c * b (n + 1) ^ τ ≤ b n) :
    Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 0) := by
  have hq : 0 < 1 / τ - 1 := by rw [sub_pos]; exact (lt_div_iff₀ hτ).mpr (by linarith)
  have hbound (n : ℕ) : b (n + 1) / b n ≤ c ^ (-(1 / τ)) * b n ^ (1 / τ - 1) := by
    by_cases hz : b n = 0
    · simp only [hz, div_zero]
      positivity
    · have hp : 0 < b n := lt_of_le_of_ne (hb n) (Ne.symm hz)
      apply (div_le_iff₀ hp).mpr
      have he : (b n / c) ^ (1 / τ) =
          c ^ (-(1 / τ)) * b n ^ (1 / τ - 1) * b n := by
        rw [Real.div_rpow (hb n) hc.le, Real.rpow_neg hc.le]
        have hh : b n ^ (1 / τ - 1) * b n = b n ^ (1 / τ) := by
          calc _ = b n ^ (1 / τ - 1) * b n ^ (1 : ℝ) := by rw [Real.rpow_one]
               _ = b n ^ ((1 / τ - 1) + 1) := (Real.rpow_add hp _ _).symm
               _ = _ := by congr 1; ring
        rw [mul_assoc, hh]
        ring
      rw [← he]
      exact next_le_power hc hτ hb hstep n
  have ht := (tendsto_const_nhds (x := c ^ (-(1 / τ)))).mul
    ((tendsto_zero hc hτ hb hstep).rpow_const (Or.inr hq.le))
  have ht0 : Tendsto (fun n => c ^ (-(1 / τ)) * b n ^ (1 / τ - 1)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hq.ne', mul_zero] using ht
  exact squeeze_zero (fun n => div_nonneg (hb _) (hb _)) hbound ht0

/-- Unit exponents give the exact uniform linear contraction factor. -/
theorem linear_step {b : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hstep : ∀ n, b (n + 1) + c * b (n + 1) ^ (1 : ℝ) ≤ b n) (n : ℕ) :
    b (n + 1) ≤ (1 + c)⁻¹ * b n := by
  have hh := hstep n
  rw [Real.rpow_one] at hh
  have hp : 0 < 1 + c := by linarith
  rw [← div_eq_inv_mul, le_div_iff₀ hp]
  nlinarith

/-- The exact implicit recurrence has a ratio tending to one above unit exponent. -/
theorem orbit_sublinear_ratio {c τ a : ℝ} (hc : 0 < c) (hτ : 1 < τ) (ha : 0 < a) :
    Tendsto (fun n => orbit c τ a (n + 1) / orbit c τ a n) atTop (𝓝 1) := by
  have ht : 0 < τ := by linarith
  have hr : 0 < τ - 1 := by linarith
  have he (n : ℕ) : orbit c τ a (n + 1) / orbit c τ a n =
      (1 + c * orbit c τ a (n + 1) ^ (τ - 1))⁻¹ := by
    have hp := orbit_pos hc ht ha (n + 1)
    have hpow : orbit c τ a (n + 1) ^ τ =
        orbit c τ a (n + 1) * orbit c τ a (n + 1) ^ (τ - 1) := by
      calc _ = orbit c τ a (n + 1) ^ (1 + (τ - 1)) := by congr 1; ring
           _ = _ := by rw [Real.rpow_add hp, Real.rpow_one]
    rw [← orbit_equation hc ht ha.le n, hpow]
    have hfac : 0 < 1 + c * orbit c τ a (n + 1) ^ (τ - 1) := by positivity
    field_simp
  simp_rw [he]
  have hshift := (orbit_tendsto_zero hc ht ha.le).comp
    (show Tendsto (fun n : ℕ => n + 1) atTop atTop from
      (strictMono_nat_of_lt_succ (by omega)).tendsto_atTop)
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := c)).mul (hshift.rpow_const (Or.inr hr.le)))
  have hs : Tendsto (fun n => 1 + c * orbit c τ a (n + 1) ^ (τ - 1)) atTop (𝓝 1) := by
    simpa only [Function.comp_apply, Real.zero_rpow hr.ne', mul_zero, add_zero] using hlim
  simpa only [inv_one] using hs.inv₀ one_ne_zero

/-- Positive target accuracies are reached in finitely many implicit updates. -/
theorem exists_hitting {c τ a ε : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a)
    (hε : 0 < ε) : ∃ n : ℕ, orbit c τ a n ≤ ε := by
  have hh := (tendsto_order.mp (orbit_tendsto_zero hc hτ ha)).2 ε hε
  obtain ⟨n, hn⟩ := hh.exists
  exact ⟨n, hn.le⟩

/-- The first implicit gap iterate below the target; invalid data use zero. -/
noncomputable def hittingTime (c τ a ε : ℝ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, orbit c τ a n ≤ ε then Nat.find h else 0

/-- The canonical hitting time really reaches the target and is minimal. -/
theorem hittingTime_spec {c τ a ε : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a)
    (hε : 0 < ε) : orbit c τ a (hittingTime c τ a ε) ≤ ε ∧
      ∀ n < hittingTime c τ a ε, ε < orbit c τ a n := by
  classical
  have he := exists_hitting hc hτ ha hε
  rw [hittingTime, dite_eq_left he]
  exact ⟨Nat.find_spec he, fun n hn => lt_of_not_ge (Nat.find_min he hn)⟩

/-- The zero initial gap has hitting time zero at every positive accuracy. -/
theorem hittingTime_zero {c τ ε : ℝ} (hε : 0 < ε) : hittingTime c τ 0 ε = 0 := by
  classical
  have he : ∃ n : ℕ, orbit c τ 0 n ≤ ε := ⟨0, hε.le⟩
  rw [hittingTime, dite_eq_left he]
  exact (Nat.find_eq_zero he).mpr hε.le
end ImplicitGap
