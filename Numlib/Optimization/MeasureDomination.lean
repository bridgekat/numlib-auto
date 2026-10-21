import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Numlib.Optimization.EvaluationComplexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Measure domination and scalar descent

Domination bounds a nonnegative objective gap by a power of a nonnegative measure on a set.
The scalar consequences distinguish whether descent uses the old or the new measure.
All convergence rates below are upper bounds, allowing faster convergence and exact zeros.
-/

namespace Optimization.MeasureDomination

/-- On `D`, the nonnegative gap above `fstar` is bounded by a positive multiple of a
positive power of the nonnegative stationarity measure `ψ`. -/
structure IsMeasureDominated {X : Type*} (D : Set X) (f ψ : X → ℝ)
    (fstar C μ : ℝ) : Prop where
  const_pos : 0 < C
  exponent_pos : 0 < μ
  measure_nonneg : ∀ x ∈ D, 0 ≤ ψ x
  gap_nonneg : ∀ x ∈ D, 0 ≤ f x - fstar
  gap_le : ∀ x ∈ D, f x - fstar ≤ C * (ψ x) ^ μ

namespace IsMeasureDominated

variable {X : Type*} {D E : Set X} {f ψ : X → ℝ} {fstar C μ : ℝ}

/-- Domination restricts to any smaller domain. -/
theorem mono (h : IsMeasureDominated D f ψ fstar C μ) (hED : E ⊆ D) :
    IsMeasureDominated E f ψ fstar C μ :=
  ⟨h.const_pos, h.exponent_pos, fun x hx => h.measure_nonneg x (hED hx),
    fun x hx => h.gap_nonneg x (hED hx), fun x hx => h.gap_le x (hED hx)⟩

/-- The reference objective is a lower bound throughout the domain. -/
theorem lower_bound (h : IsMeasureDominated D f ψ fstar C μ) {x : X} (hx : x ∈ D) :
    fstar ≤ f x := sub_nonneg.mp (h.gap_nonneg x hx)

end IsMeasureDominated

/-- Raising a domination inequality to a nonnegative power controls any nonnegative
multiple of the corresponding gap power. -/
theorem scaled_gap_rpow_le {g p C μ ν c : ℝ} (hg : 0 ≤ g) (hp : 0 ≤ p)
    (hC : 0 < C) (hμ : 0 < μ) (hν : 0 ≤ ν) (hc : 0 ≤ c)
    (hgap : g ≤ C * p ^ μ) :
    (c / C ^ (ν / μ)) * g ^ (ν / μ) ≤ c * p ^ ν := by
  have ht : 0 ≤ ν / μ := div_nonneg hν hμ.le
  have hpow := Real.rpow_le_rpow hg hgap ht
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hp _),
    ← Real.rpow_mul hp] at hpow
  have he : μ * (ν / μ) = ν := by field_simp
  rw [he] at hpow
  have hden : 0 < C ^ (ν / μ) := Real.rpow_pos_of_pos hC _
  have hdiv : g ^ (ν / μ) / C ^ (ν / μ) ≤ p ^ ν :=
    (div_le_iff₀ hden).2 (by simpa [mul_comm] using hpow)
  convert mul_le_mul_of_nonneg_left hdiv hc using 1
  ring

/-- Successor-measure descent yields an implicit scalar recurrence for the objective gap. -/
theorem implicit_gap_decrease {X : Type*} {D : Set X} {f ψ : X → ℝ}
    {fstar C μ ν c : ℝ} (h : IsMeasureDominated D f ψ fstar C μ)
    (hν : 0 ≤ ν) (hc : 0 ≤ c) {x y : X} (hy : y ∈ D)
    (hdescent : c * (ψ y) ^ ν ≤ f x - f y) :
    (f y - fstar) + (c / C ^ (ν / μ)) * (f y - fstar) ^ (ν / μ) ≤
      f x - fstar := by
  have hs := scaled_gap_rpow_le (h.gap_nonneg y hy) (h.measure_nonneg y hy)
    h.const_pos h.exponent_pos hν hc (h.gap_le y hy)
  linarith

/-- Current-measure descent yields an explicit scalar recurrence for the objective gap. -/
theorem explicit_gap_decrease {X : Type*} {D : Set X} {f ψ : X → ℝ}
    {fstar C μ ν c : ℝ} (h : IsMeasureDominated D f ψ fstar C μ)
    (hν : 0 ≤ ν) (hc : 0 ≤ c) {x y : X} (hx : x ∈ D)
    (hdescent : c * (ψ x) ^ ν ≤ f x - f y) :
    f y - fstar ≤ (f x - fstar) -
      (c / C ^ (ν / μ)) * (f x - fstar) ^ (ν / μ) := by
  have hs := scaled_gap_rpow_le (h.gap_nonneg x hx) (h.measure_nonneg x hx)
    h.const_pos h.exponent_pos hν hc (h.gap_le x hx)
  linarith

/-- Iteration of a scalar contraction. No sign assumption on the sequence is needed. -/
theorem geometric_bound {u : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ k, u (k + 1) ≤ q * u k) (k : ℕ) : u k ≤ u 0 * q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      u (k + 1) ≤ q * u k := hstep k
      _ ≤ q * (u 0 * q ^ k) := mul_le_mul_of_nonneg_left ih hq
      _ = u 0 * q ^ (k + 1) := by ring

/-- Linear implicit descent gives the geometric upper bound `(1+a)⁻ᵏ`. -/
theorem implicit_recurrence_linear_bound {u : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ≤ u k) (k : ℕ) :
    u k ≤ u 0 * (1 + a) ^ (-(k : ℝ)) := by
  have hb : 0 < 1 + a := by linarith
  have hs : ∀ k, u (k + 1) ≤ (1 + a)⁻¹ * u k := by
    intro k
    rw [mul_comm ((1 + a)⁻¹), ← div_eq_mul_inv]
    apply (le_div_iff₀ hb).2
    convert hstep k using 1
    ring
  simpa only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast] using
    geometric_bound (inv_nonneg.mpr hb.le) hs k

/-- The tolerance count is zero when the starting gap is already small enough. Otherwise
it is the natural ceiling of the logarithmic real-valued bound. -/
noncomputable def geometricIterationCount (v b ε : ℝ) : ℕ :=
  if v ≤ ε then 0 else ⌈Real.log (v / ε) / Real.log b⌉₊

/-- A denominator-form geometric upper bound yields a genuine finite iteration count,
with the ceiling handling integer rounding. -/
theorem geometric_tolerance {u : ℕ → ℝ} {v b ε : ℝ}
    (hb : 1 < b) (hε : 0 < ε) (hbound : ∀ k, u k ≤ v / b ^ k)
    {k : ℕ} (hk : geometricIterationCount v b ε ≤ k) : u k ≤ ε := by
  have hb0 : 0 < b := by linarith
  have hbk : 1 ≤ b ^ k := one_le_pow₀ hb.le
  by_cases hv : v ≤ ε
  · refine (hbound k).trans ?_
    by_cases hv0 : 0 ≤ v
    · exact (div_le_self hv0 hbk).trans hv
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv0) (pow_nonneg hb0.le _)).trans
        hε.le
  · have hv0 : 0 < v := lt_trans hε (lt_of_not_ge hv)
    have hlog : 0 < Real.log b := Real.log_pos hb
    have hcount : Real.log (v / ε) / Real.log b ≤ (k : ℝ) := by
      exact (Nat.le_ceil _).trans (by exact_mod_cast (by
        simpa only [geometricIterationCount, ite_eq_right hv] using hk))
    have hlogbound : Real.log (v / ε) ≤ (k : ℝ) * Real.log b :=
      (div_le_iff₀ hlog).mp hcount
    have hpow : v / ε ≤ b ^ k := Real.le_pow_of_log_le hb0 hlogbound
    have hvbound : v ≤ ε * b ^ k := by
      have hh := (div_le_iff₀ hε).mp hpow
      simpa [mul_comm] using hh
    exact (hbound k).trans ((div_le_iff₀ (pow_pos hb0 _)).2 (by
      simpa [mul_comm] using hvbound))

/-- Explicit finite tolerance bound for linear implicit descent. -/
theorem implicit_recurrence_linear_tolerance {u : ℕ → ℝ} {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ≤ u k)
    {k : ℕ} (hk : geometricIterationCount (u 0) (1 + a) ε ≤ k) : u k ≤ ε := by
  apply geometric_tolerance (by linarith : 1 < 1 + a) hε (fun k => ?_) hk
  simpa [Real.rpow_neg (by linarith : 0 ≤ 1 + a), Real.rpow_natCast,
    div_eq_mul_inv] using implicit_recurrence_linear_bound ha hstep k

/-- Explicit linear descent has the geometric upper bound with factor `1-a`.
This factor gives decay when `0 < a < 1`. -/
theorem explicit_recurrence_linear_bound_of_lt_one {u : ℕ → ℝ} {a : ℝ}
    (ha : a < 1) (hstep : ∀ k, u (k + 1) ≤ u k - a * u k) (k : ℕ) :
    u k ≤ u 0 * (1 - a) ^ k := by
  apply geometric_bound (by linarith : 0 ≤ 1 - a)
  intro k
  convert hstep k using 1
  ring

/-- At and above the exceptional parameter `a=1`, every successor gap is exactly zero. -/
theorem explicit_recurrence_eq_zero_of_one_le {u : ℕ → ℝ} {a : ℝ}
    (ha : 1 ≤ a) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k) (k : ℕ) : u (k + 1) = 0 := by
  have hp := mul_nonneg (sub_nonneg.mpr ha) (hu k)
  exact le_antisymm (by nlinarith [hstep k]) (hu (k + 1))

/-- Explicit linear descent includes a geometric upper bound for `a<1` and immediate
termination for `a≥1`. The geometric bound gives decay when `0 < a < 1`. -/
theorem explicit_recurrence_linear_bound {u : ℕ → ℝ} {a : ℝ}
    (hu : ∀ k, 0 ≤ u k) (hstep : ∀ k, u (k + 1) ≤ u k - a * u k) :
    (a < 1 ∧ ∀ k, u k ≤ u 0 * (1 - a) ^ k) ∨
      (1 ≤ a ∧ ∀ k, u (k + 1) = 0) := by
  rcases lt_or_ge a 1 with hlt | hge
  · exact Or.inl ⟨hlt, explicit_recurrence_linear_bound_of_lt_one hlt hstep⟩
  · exact Or.inr ⟨hge, explicit_recurrence_eq_zero_of_one_le hge hu hstep⟩

/-- For `a>1`, a positive current gap would make the successor negative, so even the
initial gap must be zero. -/
theorem explicit_recurrence_eq_zero_of_one_lt {u : ℕ → ℝ} {a : ℝ}
    (ha : 1 < a) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k) (k : ℕ) : u k = 0 := by
  have hmul : (a - 1) * u k ≤ 0 := by linarith [hstep k, hu (k + 1)]
  have : u k ≤ 0 := nonpos_of_mul_nonpos_right hmul (by linarith : 0 < a - 1)
  exact le_antisymm this (hu k)

/-- Explicit descent of a nonnegative sequence is monotone. -/
theorem explicit_recurrence_antitone {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 ≤ a) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * (u k) ^ τ) : Antitone u := by
  apply antitone_nat_of_succ_le
  intro k
  have hp := mul_nonneg ha (Real.rpow_nonneg (hu k) τ)
  linarith [hstep k]

/-- The explicit linear tolerance count includes immediate termination for `a≥1`. -/
noncomputable def explicitLinearIterationCount (v a ε : ℝ) : ℕ :=
  if v ≤ ε then 0 else if a < 1 then geometricIterationCount v (1 - a)⁻¹ ε else 1

/-- Finite tolerance guarantee for explicit linear descent, including exceptional parameters. -/
theorem explicit_recurrence_linear_tolerance {u : ℕ → ℝ} {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * u k)
    {k : ℕ} (hk : explicitLinearIterationCount (u 0) a ε ≤ k) : u k ≤ ε := by
  by_cases hstart : u 0 ≤ ε
  · have hm : Antitone u := by
      apply antitone_nat_of_succ_le
      intro j
      nlinarith [hstep j, hu j]
    exact (hm (Nat.zero_le k)).trans hstart
  · by_cases hlt : a < 1
    · have hb : 1 < (1 - a)⁻¹ := by
        rw [inv_eq_one_div, lt_div_iff₀ (by linarith : 0 < 1 - a)]
        linarith
      apply geometric_tolerance hb hε (fun j => ?_) (by
        simpa only [explicitLinearIterationCount, ite_eq_right hstart,
          ite_eq_left hlt] using hk)
      simpa only [inv_pow, div_eq_mul_inv, inv_inv] using
        explicit_recurrence_linear_bound_of_lt_one hlt hstep j
    · have hk1 : 1 ≤ k := by
        simpa only [explicitLinearIterationCount, ite_eq_right hstart,
          ite_eq_right hlt] using hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [explicit_recurrence_eq_zero_of_one_le (le_of_not_gt hlt) hu hstep j]
      exact hε.le

/-- The elementary superlinear one-step estimate. The full eventual rate additionally
requires an entry threshold and iteration-count analysis. -/
theorem implicit_recurrence_rpow_step {v w a τ : ℝ} (hw : 0 ≤ w)
    (ha : 0 < a) (hτ : 0 < τ) (hstep : w + a * w ^ τ ≤ v) :
    w ≤ (v / a) ^ (1 / τ) := by
  have hpow : w ^ τ ≤ v / a := (le_div_iff₀ ha).2 (by nlinarith)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hw τ) hpow
    (by positivity : 0 ≤ 1 / τ)
  have he : τ * (1 / τ) = 1 := by field_simp
  rwa [← Real.rpow_mul hw, he, Real.rpow_one] at hh

/-- A positive gap in a nonnegative explicit recurrence with exponent below one cannot
be smaller than the extinction threshold. -/
theorem explicit_recurrence_positive_gap_lower_bound {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : τ < 1) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * (u k) ^ τ)
    {k : ℕ} (hk : 0 < u k) : a ^ (1 / (1 - τ)) ≤ u k := by
  have hpower : a ≤ (u k) ^ (1 - τ) := by
    rw [Real.rpow_sub hk, Real.rpow_one]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hk τ)).2
    linarith [hstep k, hu (k + 1)]
  have hh := Real.rpow_le_rpow ha.le hpower (by positivity : 0 ≤ 1 / (1 - τ))
  have he : (1 - τ) * (1 / (1 - τ)) = 1 := by
    field_simp [ne_of_gt (sub_pos.mpr hτ)]
  rwa [← Real.rpow_mul hk.le, he, Real.rpow_one] at hh

/-- A monotone nonnegative sequence with a fixed positive decrement at every nonzero
entry vanishes by any index strictly larger than the initial value divided by that decrement. -/
theorem eq_zero_of_uniform_decrease {u : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hu : ∀ k, 0 ≤ u k) (hm : Antitone u)
    (hdec : ∀ k, u k ≠ 0 → δ ≤ u k - u (k + 1))
    {N : ℕ} (hN : u 0 / δ < (N : ℝ)) : u N = 0 := by
  obtain ⟨k, hk, hzero, -⟩ := EvaluationComplexity.exists_first_of_decrease
    (P := fun k => u k = 0) hδ hu (fun n hn => hdec n (hn n le_rfl))
  simp only [sub_zero] at hk
  have hfloor : (⌊u 0 / δ⌋₊ : ℝ) ≤ u 0 / δ :=
    Nat.floor_le (div_nonneg (hu 0) hδ.le)
  have hkN : k ≤ N := by
    exact_mod_cast ((Nat.cast_le.mpr hk).trans hfloor).trans hN.le
  have hle := hm hkN
  rw [hzero] at hle
  exact le_antisymm hle (hu N)

/-- For an explicit recurrence with exponent strictly between zero and one, exact zero
occurs after finitely many steps, independently of any requested tolerance. This conservative
count uses the positive-gap threshold; no claim of an optimal extinction count is made. -/
theorem explicit_recurrence_finite_termination {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ u k - a * (u k) ^ τ) :
    ∀ k, ⌊u 0 / a ^ (1 / (1 - τ))⌋₊ + 1 ≤ k → u k = 0 := by
  let δ : ℝ := a ^ (1 / (1 - τ))
  have hδ : 0 < δ := Real.rpow_pos_of_pos ha _
  have hδpow : δ ^ (1 - τ) = a := by
    dsimp [δ]
    rw [← Real.rpow_mul ha.le]
    have he : (1 / (1 - τ)) * (1 - τ) = 1 := by
      field_simp [ne_of_gt (sub_pos.mpr hτ1)]
    rw [he, Real.rpow_one]
  have hδid : a * δ ^ τ = δ := by
    rw [← hδpow, ← Real.rpow_add hδ, sub_add_cancel, Real.rpow_one]
  have hm := explicit_recurrence_antitone ha.le hu hstep
  have hdec : ∀ k, u k ≠ 0 → δ ≤ u k - u (k + 1) := by
    intro k hk
    have hkpos : 0 < u k := lt_of_le_of_ne (hu k) (Ne.symm hk)
    have hthreshold : δ ≤ u k :=
      explicit_recurrence_positive_gap_lower_bound ha hτ1 hu hstep hkpos
    have hpower := Real.rpow_le_rpow hδ.le hthreshold hτ0.le
    have hmul := mul_le_mul_of_nonneg_left hpower ha.le
    rw [hδid] at hmul
    linarith [hstep k]
  have hN : u (⌊u 0 / δ⌋₊ + 1) = 0 := by
    apply eq_zero_of_uniform_decrease hδ hu hm hdec
    exact_mod_cast Nat.lt_floor_add_one (u 0 / δ)
  intro k hk
  have hle := hm hk
  change u k ≤ u (⌊u 0 / δ⌋₊ + 1) at hle
  rw [hN] at hle
  exact le_antisymm hle (hu k)

end Optimization.MeasureDomination
