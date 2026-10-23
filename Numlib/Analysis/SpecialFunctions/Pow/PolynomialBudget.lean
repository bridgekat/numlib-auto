import Numlib.Analysis.SpecialFunctions.Pow.ImplicitRecurrence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Polynomial hitting bounds for genuine implicit power orbits

A mean-value estimate for reciprocal powers yields a positive uniform inverse
increment. Telescoping the actual update equations gives an explicit ceiling
budget at every positive accuracy, including a zero initial gap.
-/

open Set Filter Topology
namespace ImplicitGap

/-- The exact reciprocal-power increment dominates the right-endpoint derivative slope. -/
theorem inverse_power_increment {u v r : ℝ} (hu : 0 < u) (huv : u < v) (hr : 0 < r) :
    r * v ^ (-r - 1) * (v - u) ≤ u ^ (-r) - v ^ (-r) := by
  obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope
    (fun t : ℝ => t ^ (-r)) (fun t : ℝ => -r * t ^ (-r - 1)) huv
    (fun y hy => (Real.hasDerivAt_rpow_const (Or.inl (hu.trans_le
      hy.1).ne')).continuousAt.continuousWithinAt)
    (fun y hy => Real.hasDerivAt_rpow_const (Or.inl (hu.trans hy.1).ne'))
  have hm := (eq_div_iff (sub_pos.mpr huv).ne').mp he
  have hp := Real.rpow_le_rpow_of_nonpos (hu.trans hξ.1) hξ.2.le
    (show -r - 1 ≤ 0 by linarith)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hr.le)
    (sub_nonneg.mpr huv.le)
  nlinarith

/-- A positive implicit orbit decreases strictly at every finite step. -/
theorem orbit_strictAnti {c τ a : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 < a) :
    StrictAnti (orbit c τ a) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hh := orbit_equation hc hτ ha.le n
  have hp := mul_pos hc (Real.rpow_pos_of_pos (orbit_pos hc hτ ha (n + 1)) τ)
  linarith

/-- Above unit exponent each exact implicit step has a uniform inverse-power increment. -/
theorem orbit_inverse_increment {c τ a : ℝ} (hc : 0 < c) (hτ : 1 < τ) (ha : 0 < a) (n : ℕ) :
    (τ - 1) * c / (1 + c * a ^ (τ - 1)) ^ τ ≤
      orbit c τ a (n + 1) ^ (-(τ - 1)) - orbit c τ a n ^ (-(τ - 1)) := by
  let u := orbit c τ a (n + 1)
  let v := orbit c τ a n
  let D := 1 + c * a ^ (τ - 1)
  have ht : 0 < τ := by linarith
  have hr : 0 < τ - 1 := by linarith
  have hu : 0 < u := orbit_pos hc ht ha (n + 1)
  have hv : 0 < v := orbit_pos hc ht ha n
  have hD : 0 < D := by positivity
  have huv : u < v := orbit_strictAnti hc ht ha (Nat.lt_succ_self n)
  have hua : u ≤ a := by
    have hh := (orbit_strictAnti hc ht ha).antitone (Nat.zero_le (n + 1))
    simpa only [orbit_zero] using hh
  have he : v = u + c * u ^ τ := (orbit_equation hc ht ha.le n).symm
  have hupow : u ^ τ = u * u ^ (τ - 1) := by
    calc _ = u ^ (1 + (τ - 1)) := by congr 1; ring
         _ = _ := by rw [Real.rpow_add hu, Real.rpow_one]
  have hvu : v ≤ D * u := by
    have hh := Real.rpow_le_rpow hu.le hua hr.le
    have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hc.le hu.le)
    rw [he, hupow]
    dsimp [D]
    nlinarith
  have hp := Real.rpow_le_rpow_of_nonpos hv hvu (show -τ ≤ 0 by linarith)
  have hprod : v ^ (-τ) * u ^ τ ≥ (D ^ τ)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hu.le τ)
    have hz : (D * u) ^ (-τ) * u ^ τ = (D ^ τ)⁻¹ := by
      rw [Real.mul_rpow hD.le hu.le, Real.rpow_neg hD.le, Real.rpow_neg hu.le]
      field_simp
    rwa [hz] at hh
  have hinc := inverse_power_increment hu huv hr
  have hepow : -(τ - 1) - 1 = -τ := by ring
  rw [hepow] at hinc
  have hdiff : v - u = c * u ^ τ := by linarith
  rw [hdiff] at hinc
  have hh := mul_le_mul_of_nonneg_left hprod (mul_nonneg hr.le hc.le)
  calc _ = ((τ - 1) * c) * (D ^ τ)⁻¹ := by rfl
       _ ≤ ((τ - 1) * c) * (v ^ (-τ) * u ^ τ) := hh
       _ = (τ - 1) * v ^ (-τ) * (c * u ^ τ) := by ring
       _ ≤ _ := hinc

/-- Initial-gap order is preserved by every genuine implicit update. -/
theorem orbit_mono_initial {c τ a b : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ha : 0 ≤ a)
    (hab : a ≤ b) (n : ℕ) : orbit c τ a n ≤ orbit c τ b n := by
  induction n with
  | zero => exact hab
  | succ n ih =>
    rw [orbit_succ, orbit_succ]
    exact step_mono hc hτ (orbit_nonneg hc hτ ha n) ih

/-- Uniform positive inverse increments yield an actual polynomial gap-hitting budget. -/
theorem exists_polynomial_budget {c τ a ε : ℝ} (hc : 0 < c) (hτ : 1 < τ)
    (ha : 0 ≤ a) (hε : 0 < ε) :
    let R := max 1 a
    let δ := (τ - 1) * c / (1 + c * R ^ (τ - 1)) ^ τ
    ∃ N : ℕ, orbit c τ a N ≤ ε ∧
      (N : ℝ) ≤ (1 / δ) * ε ^ (-(τ - 1)) + 1 := by
  let R := max 1 a
  let δ := (τ - 1) * c / (1 + c * R ^ (τ - 1)) ^ τ
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have ht : 0 < τ := by linarith
  have hr : 0 < τ - 1 := by linarith
  have hδ : 0 < δ := by positivity
  have hsum (N : ℕ) : (N : ℝ) * δ ≤
      orbit c τ R N ^ (-(τ - 1)) - R ^ (-(τ - 1)) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hh := orbit_inverse_increment hc hτ hR N
      change δ ≤ _ at hh
      push_cast
      nlinarith
  let N : ℕ := ⌈ε ^ (-(τ - 1)) / δ⌉₊
  have hN : ε ^ (-(τ - 1)) ≤ (N : ℝ) * δ :=
    (div_le_iff₀ hδ).mp (Nat.le_ceil _)
  have hpower : ε ^ (-(τ - 1)) ≤ orbit c τ R N ^ (-(τ - 1)) := by
    have hp := Real.rpow_pos_of_pos hR (-(τ - 1))
    linarith [hsum N]
  have htarget : orbit c τ R N ≤ ε :=
    (Real.rpow_le_rpow_iff_of_neg hε (orbit_pos hc ht hR N) (by linarith)).mp hpower
  refine ⟨N, (orbit_mono_initial hc ht ha (le_max_right 1 a) N).trans htarget, ?_⟩
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ ε ^ (-(τ - 1)) / δ by positivity)).le
  change (N : ℝ) ≤ _ at hceil
  convert hceil using 1
  ring
end ImplicitGap
