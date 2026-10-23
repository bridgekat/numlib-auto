import Numlib.Optimization.MeasureDomination.Blocks

/-!
# Full polynomial gap and measure complexity

A true implicit recurrence bounds the gap. After gap is at most κψ ε^μ, a
finite block of failed measure tests would each consume κν ε^ν, yielding the
sharper measure exponent ν−μ. Both upper rates permit faster convergence and
finite attainment, and all cost constants precede every accuracy.
-/

open Set Filter Topology
namespace MeasureDomination
variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ}
  {x : ℕ → E} {S : Set ℕ}

/-- Four constants fixed before every accuracy bound actual first attainment and
initialized function and derivative counts by the specified inverse power. -/
def PowerCost (q : ℝ) (target : ℕ → ℝ) (S : Set ℕ) : Prop :=
  ∃ B > 0, ∃ C > 0, ∃ D > 0, ∃ F > 0, ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, target K ≤ ε ∧ (∀ k < K, ε < target k) ∧
      ((K + 1 : ℕ) : ℝ) ≤ B * ε ^ (-q) + C ∧
      ((EvaluationComplexity.successfulIterations S K).card + 1 : ℕ) ≤ D * ε ^ (-q) + F

/-- Above the domination level, the exact implicit orbit gives the full gap power cost. -/
theorem ARRun.gap_power_cost (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    PowerCost ((ν - μ) / μ) (fun k => gap f fstar (x k)) S := by
  let c := κν / κψ ^ (ν / μ)
  let τ := ν / μ
  let R := max 1 (gap f fstar (x 0))
  let δ := (τ - 1) * c / (1 + c * R ^ (τ - 1)) ^ τ
  have hμ : 0 < μ := zero_lt_one.trans_le hd.level_ge_one
  have hc : 0 < c := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht : 1 < τ := (one_lt_div hμ).mpr hμν
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hκR : 0 < κR := zero_lt_one.trans_le hr.density_factor
  have hκA : 0 ≤ κA := hr.density_additive
  have he : τ - 1 = (ν - μ) / μ := by dsimp [τ]; field_simp
  refine ⟨κR / δ, by positivity, κR + κA + 1, by positivity,
    1 / δ, by positivity, 2, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨M, htarg, hM⟩ := ImplicitGap.exists_polynomial_budget hc ht (hd.gap_nonneg (x 0)) hε
  change (M : ℝ) ≤ (1 / δ) * ε ^ (-(τ - 1)) + 1 at hM
  rw [he] at hM
  obtain ⟨K, hs, hfirst, hcard, hK⟩ := hr.first_gap_budget hd hε htarg
  refine ⟨K, hs, hfirst, ?_, ?_⟩
  · push_cast
    calc (K : ℝ) + 1 ≤ κR * M + κA + 1 := by linarith
      _ ≤ κR * ((1 / δ) * ε ^ (-((ν - μ) / μ)) + 1) + κA + 1 := by gcongr
      _ = _ := by ring
  · push_cast
    have hh : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ M :=
      by exact_mod_cast hcard
    linarith

/-- A finite block after a small true gap gives the sharper source measure power cost. -/
theorem ARRun.measure_power_cost (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    PowerCost (ν - μ) (fun k => ψ (x k)) S := by
  let c := κν / κψ ^ (ν / μ)
  let τ := ν / μ
  let r := τ - 1
  let R := max 1 (gap f fstar (x 0))
  let δ := r * c / (1 + c * R ^ r) ^ τ
  let A := (1 / δ) * κψ ^ (-r) + κψ / κν
  have hμ : 0 < μ := zero_lt_one.trans_le hd.level_ge_one
  have hc : 0 < c := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht : 1 < τ := (one_lt_div hμ).mpr hμν
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hA : 0 < A := add_pos
    (mul_pos (one_div_pos.mpr hδ) (Real.rpow_pos_of_pos hd.coefficient_pos _))
    (div_pos hd.coefficient_pos hr.coefficient_pos)
  have hκR : 0 < κR := zero_lt_one.trans_le hr.density_factor
  have hκA : 0 ≤ κA := hr.density_additive
  have hν : 0 < ν := zero_lt_one.trans_le hr.exponent_ge_one
  have her : μ * r = ν - μ := by dsimp [r, τ]; field_simp
  refine ⟨κR * A, by positivity, 3 * κR + κA + 1, by positivity,
    A, hA, 4, by norm_num, ?_⟩
  intro ε hε
  let G := κψ * ε ^ μ
  let d := κν * ε ^ ν
  have hG : 0 < G := mul_pos hd.coefficient_pos (Real.rpow_pos_of_pos hε μ)
  have hdpos : 0 < d := mul_pos hr.coefficient_pos (Real.rpow_pos_of_pos hε ν)
  obtain ⟨M, htarg, hM⟩ := ImplicitGap.exists_polynomial_budget hc ht (hd.gap_nonneg (x 0)) hG
  change (M : ℝ) ≤ (1 / δ) * G ^ (-r) + 1 at hM
  let J : ℕ := ⌈G / d⌉₊ + 1
  have hJ : G < (J : ℝ) * d := by
    have hh : G ≤ (⌈G / d⌉₊ : ℝ) * d := (div_le_iff₀ hdpos).mp (Nat.le_ceil _)
    dsimp [J]
    push_cast
    nlinarith
  obtain ⟨K, hs, hfirst, hcard, hK⟩ := hr.first_measure_block hd hε htarg hJ
  have hJb : (J : ℝ) ≤ G / d + 2 := by
    have hh := (Nat.ceil_lt_add_one (div_nonneg hG.le hdpos.le)).le
    dsimp [J]
    push_cast
    linarith
  have hGpow : G ^ (-r) = κψ ^ (-r) * ε ^ (-(ν - μ)) := by
    dsimp [G]
    rw [Real.mul_rpow hd.coefficient_pos.le (Real.rpow_nonneg hε.le μ),
      ← Real.rpow_mul hε.le]
    rw [show μ * (-r) = -(ν - μ) by nlinarith [her]]
  have hratio : G / d = (κψ / κν) * ε ^ (-(ν - μ)) := by
    dsimp [G, d]
    rw [show -(ν - μ) = μ - ν by ring, Real.rpow_sub hε]
    ring
  have hsum : (M : ℝ) + J ≤ A * ε ^ (-(ν - μ)) + 3 := by
    rw [hGpow] at hM
    rw [hratio] at hJb
    dsimp [A]
    nlinarith
  refine ⟨K, hs, hfirst, ?_, ?_⟩
  · push_cast at hK ⊢
    calc (K : ℝ) + 1 ≤ κR * (M + J) + κA + 1 := by linarith
      _ ≤ κR * (A * ε ^ (-(ν - μ)) + 3) + κA + 1 := by gcongr
      _ = _ := by ring
  · push_cast
    have hh : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ (M : ℝ) + J :=
      by exact_mod_cast hcard
    linarith

/-- Actual successful measures have a genuine sublinear upper envelope above the domination
  level. -/
theorem ARRun.measure_sublinear_envelope (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    (∀ n, ψ (x (successIndex S (n + 1))) = 0) ∨
      ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧
        (∀ n, ψ (x (successIndex S (n + 1))) ≤ t n) ∧ Tendsto t atTop (𝓝 0) ∧
        Tendsto (fun n => t (n + 1) / t n) atTop (𝓝 1) := by
  let b := successfulGap f fstar x S
  let c := κν / κψ ^ (ν / μ)
  let τ := ν / μ
  let q := 1 / ν
  have hc : 0 < c := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht1 : 1 < τ := (one_lt_div (zero_lt_one.trans_le hd.level_ge_one)).mpr hμν
  have ht : 0 < τ := by linarith
  have hq : 0 < q := div_pos zero_lt_one (zero_lt_one.trans_le hr.exponent_ge_one)
  rcases (hd.gap_nonneg (x (successIndex S 0))).eq_or_lt with hz | hp
  · left
    intro n
    have hh := hr.gap_antitone hd
      ((successIndex_strictMono hr.infinite_success).monotone (Nat.zero_le n))
    change b n ≤ b 0 at hh
    have hzero : b n = 0 := le_antisymm (hh.trans_eq hz.symm) (hd.gap_nonneg _)
    have hu := hr.successful_measure_le hd n
    change _ ≤ (b n / κν) ^ q at hu
    rw [hzero, zero_div, Real.zero_rpow hq.ne'] at hu
    exact le_antisymm hu (hd.measure_nonneg _)
  · right
    change 0 < b 0 at hp
    have hbnonneg : ∀ n, 0 ≤ b n := fun _ => hd.gap_nonneg _
    let t : ℕ → ℝ := fun n => (ImplicitGap.orbit c τ (b 0) n / κν) ^ q
    have htpos (n : ℕ) : 0 < t n := Real.rpow_pos_of_pos
      (div_pos (ImplicitGap.orbit_pos hc ht hp n) hr.coefficient_pos) q
    have hbound (n : ℕ) : ψ (x (successIndex S (n + 1))) ≤ t n := by
      apply (hr.successful_measure_le hd n).trans
      exact Real.rpow_le_rpow (div_nonneg (hd.gap_nonneg _) hr.coefficient_pos.le)
        (div_le_div_of_nonneg_right (ImplicitGap.le_orbit (b := b) hc ht hbnonneg
          (hr.successful_implicit_decrease hd) n) hr.coefficient_pos.le) hq.le
    have hlim := ((ImplicitGap.orbit_tendsto_zero hc ht hp.le).div_const κν).rpow_const
      (Or.inr hq.le)
    have htlim : Tendsto t atTop (𝓝 0) := by
      simpa only [t, zero_div, Real.zero_rpow hq.ne'] using hlim
    have he (n : ℕ) : t (n + 1) / t n =
        (ImplicitGap.orbit c τ (b 0) (n + 1) / ImplicitGap.orbit c τ (b 0) n) ^ q := by
      dsimp [t]
      have hu₁ : 0 ≤ ImplicitGap.orbit c τ (b 0) (n + 1) / κν :=
        div_nonneg (ImplicitGap.orbit_nonneg hc ht hp.le _) hr.coefficient_pos.le
      have hu₀ : 0 ≤ ImplicitGap.orbit c τ (b 0) n / κν :=
        div_nonneg (ImplicitGap.orbit_nonneg hc ht hp.le _) hr.coefficient_pos.le
      rw [← Real.div_rpow hu₁ hu₀]
      congr 1
      have hκne : κν ≠ 0 := hr.coefficient_pos.ne'
      have hbne : ImplicitGap.orbit c τ (b 0) n ≠ 0 := (ImplicitGap.orbit_pos hc ht hp n).ne'
      field_simp
    have hratio := (ImplicitGap.orbit_sublinear_ratio hc ht1 hp).rpow_const (p := q) (Or.inl
      one_ne_zero)
    refine ⟨t, htpos, hbound, htlim, ?_⟩
    simp_rw [he]
    simpa only [Real.one_rpow] using hratio
end MeasureDomination
