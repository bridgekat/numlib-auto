/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Algebra.Spectrum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Spectral radius and convergence of powers

In a complex unital Banach algebra, `ρ(a) < 1 ↔ aⁿ → 0`, the Neumann series `∑ aⁿ` converges iff
`ρ(a) < 1`, and powers decay geometrically at any rate above the spectral radius. All three are
classical consequences of Gelfand's formula for the spectral radius, which Mathlib provides as
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`.

`spectralRadius_smul` records the absolute homogeneity `ρ(c • a) = ‖c‖ ρ(a)`, which needs no
analytic input and holds in any algebra over a normed field.
-/

open Filter Topology
open scoped ENNReal NNReal

section Homogeneous

open scoped Pointwise

variable {𝕜 B : Type*} [NormedField 𝕜] [Ring B] [Algebra 𝕜 B]

/-- The spectral radius is absolutely homogeneous: `ρ(c • a) = ‖c‖ ρ(a)`.

This is purely algebraic, a restatement of `spectrum.unit_smul_eq_smul`
(`spectrum 𝕜 (c • a) = c • spectrum 𝕜 a` for `c ≠ 0`); neither completeness of the algebra nor
submultiplicativity of its norm is used. -/
theorem spectralRadius_smul (c : 𝕜) (a : B) :
    spectralRadius 𝕜 (c • a) = ‖c‖₊ * spectralRadius 𝕜 a := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hset : spectrum 𝕜 (c • a) = c • spectrum 𝕜 a := by
      simpa [Units.smul_def] using spectrum.unit_smul_eq_smul a (Units.mk0 c hc)
    simp only [spectralRadius, hset, ← Set.image_smul, iSup_image, smul_eq_mul, nnnorm_mul,
      ENNReal.coe_mul, ENNReal.mul_iSup]

end Homogeneous

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

omit [NormOneClass A] in
/-- Gelfand's formula turns `ρ(a) < r` into the eventual bound `‖aⁿ‖ ≤ rⁿ`. -/
private theorem eventually_norm_pow_le_of_spectralRadius_lt (a : A) {r : NNReal}
    (hr : spectralRadius ℂ a < r) : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ (r : ℝ) ^ n := by
  have h := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a).eventually_lt_const hr
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hn0 : n ≠ 0 := by omega
  have key : (‖a ^ n‖₊ : ℝ≥0∞) < (r : ℝ≥0∞) ^ n :=
    calc (‖a ^ n‖₊ : ℝ≥0∞) = ((‖a ^ n‖₊ : ℝ≥0∞) ^ ((n : ℝ)⁻¹)) ^ n :=
          (ENNReal.rpow_inv_natCast_pow hn0 _).symm
      _ < (r : ℝ≥0∞) ^ n := ENNReal.pow_lt_pow_left hn0 (by rwa [one_div] at hn)
  rw [← ENNReal.coe_pow, ENNReal.coe_lt_coe] at key
  exact_mod_cast key.le

omit [NormOneClass A] in
/-- Geometric decay of powers at any rate `r > ρ(a)`. -/
theorem exists_norm_pow_le_of_spectralRadius_lt (a : A) {r : NNReal}
    (hr : spectralRadius ℂ a < r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a ^ n‖ ≤ C * (r : ℝ) ^ n := by
  have hrne : r ≠ 0 := by rintro rfl; simp at hr
  have hr0 : (0 : ℝ) < r := by
    have : (0 : ℝ≥0) < r := pos_iff_ne_zero.mpr hrne
    exact_mod_cast this
  obtain ⟨N, hN⟩ :=
    eventually_atTop.mp (eventually_norm_pow_le_of_spectralRadius_lt a hr)
  set S : ℝ := ∑ i ∈ Finset.range N, ‖a ^ i‖ / (r : ℝ) ^ i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨1 + S, by linarith, fun n => ?_⟩
  have hrn : (0 : ℝ) < (r : ℝ) ^ n := by positivity
  rcases lt_or_ge n N with hn | hn
  · have h1 : ‖a ^ n‖ / (r : ℝ) ^ n ≤ S :=
      hS ▸ Finset.single_le_sum (f := fun i => ‖a ^ i‖ / (r : ℝ) ^ i)
        (fun i _ => by positivity) (Finset.mem_range.mpr hn)
    rw [div_le_iff₀ hrn] at h1
    nlinarith
  · have := hN n hn
    nlinarith

private theorem spectralRadius_lt_one_of_norm_pow_lt_one {a : A} {n : ℕ} (h : ‖a ^ n‖ < 1) :
    spectralRadius ℂ a < 1 := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  rcases lt_or_ge (spectralRadius ℂ a) 1 with h' | hc
  · exact h'
  have h1 : (1 : ℝ≥0∞) ≤ spectralRadius ℂ (a ^ n) :=
    (one_le_pow₀ hc).trans (spectrum.spectralRadius_pow_le a n hn)
  have h2 : spectralRadius ℂ (a ^ n) ≤ (‖a ^ n‖₊ : ℝ≥0∞) := spectrum.spectralRadius_le_nnnorm _
  have h3 : (‖a ^ n‖₊ : ℝ≥0∞) < 1 := by
    rw [ENNReal.coe_lt_one_iff]
    exact_mod_cast h
  exact absurd (h1.trans_lt (h2.trans_lt h3)) (lt_irrefl 1)

/-- `ρ(a) < 1 ↔ aⁿ → 0`. -/
theorem spectralRadius_lt_one_iff_tendsto_pow (a : A) :
    spectralRadius ℂ a < 1 ↔ Tendsto (fun n => a ^ n) atTop (𝓝 0) := by
  constructor
  · intro h
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    obtain ⟨C, _, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt a hr1
    have hrlt : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.mp hr2
    refine squeeze_zero_norm hC ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hrlt).const_mul C
  · intro h
    have hnorm : Tendsto (fun n => ‖a ^ n‖) atTop (𝓝 0) := by simpa using h.norm
    obtain ⟨n, hn⟩ := (hnorm.eventually_lt_const one_pos).exists
    exact spectralRadius_lt_one_of_norm_pow_lt_one hn

theorem spectralRadius_lt_one_of_norm_lt_one {a : A} (h : ‖a‖ < 1) : spectralRadius ℂ a < 1 :=
  spectralRadius_lt_one_of_norm_pow_lt_one (n := 1) (by rwa [pow_one])

/-- `ρ(a) < 1 ↔ ‖aⁿ‖ < 1` for some `n`. -/
theorem spectralRadius_lt_one_iff_exists_norm_pow_lt_one (a : A) :
    spectralRadius ℂ a < 1 ↔ ∃ n, ‖a ^ n‖ < 1 := by
  refine ⟨fun h => ?_, fun ⟨_, hn⟩ => spectralRadius_lt_one_of_norm_pow_lt_one hn⟩
  have hnorm : Tendsto (fun n => ‖a ^ n‖) atTop (𝓝 0) := by
    simpa using ((spectralRadius_lt_one_iff_tendsto_pow a).mp h).norm
  exact (hnorm.eventually_lt_const one_pos).exists

/-- The Neumann series `∑ aⁿ` converges iff `ρ(a) < 1`. -/
theorem summable_pow_iff_spectralRadius_lt_one (a : A) :
    Summable (fun n => a ^ n) ↔ spectralRadius ℂ a < 1 := by
  refine ⟨fun h => (spectralRadius_lt_one_iff_tendsto_pow a).mpr h.tendsto_atTop_zero, fun h => ?_⟩
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  obtain ⟨C, _, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt a hr1
  have hrlt : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.mp hr2
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one r.coe_nonneg hrlt).mul_left C) hC

/-- When `ρ(a) < 1`, `1 - a` is a unit with inverse the Neumann series. -/
theorem isUnit_one_sub_of_spectralRadius_lt_one {a : A} (h : spectralRadius ℂ a < 1) :
    IsUnit (1 - a) :=
  have hs : Summable (a ^ ·) := (summable_pow_iff_spectralRadius_lt_one a).mpr h
  ⟨⟨1 - a, ∑' n : ℕ, a ^ n, hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩, rfl⟩
