/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Algebra.Spectrum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Spectral radius and convergence of powers

In a complex unital Banach algebra, `ρ(a) < 1 ↔ aⁿ → 0`, the Neumann series `∑ aⁿ` converges iff
`ρ(a) < 1`, and powers decay geometrically at any rate above the spectral radius. All three are
classical consequences of Gelfand's formula for the spectral radius, which Mathlib provides as
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`.

`spectralRadius_smul` records the absolute homogeneity `ρ(c • a) = ‖c‖ ρ(a)`, which needs no
analytic input and holds in any algebra over a normed field.

`spectralRadius_le_algebraNorm` bounds the spectral radius by an *arbitrary* algebra norm on a
finite-dimensional algebra — "`|λ| ≤ ‖A‖` for any consistent matrix norm" — with no analysis and
no relation to the norm the algebra already carries.
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

omit [NormOneClass A] in
/-- Powers of an element of spectral radius `< 1` tend to `0`.  This half of
`spectralRadius_lt_one_iff_tendsto_pow` needs no `‖1‖ = 1`, which matters for the operator algebra
`E →L[𝕜] E`, a `NormOneClass` only for nontrivial `E`. -/
theorem tendsto_pow_of_spectralRadius_lt_one {a : A} (h : spectralRadius ℂ a < 1) :
    Tendsto (fun n => a ^ n) atTop (𝓝 0) := by
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  obtain ⟨C, _, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt a hr1
  have hrlt : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.mp hr2
  refine squeeze_zero_norm hC ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hrlt).const_mul C

/-- `ρ(a) < 1 ↔ aⁿ → 0`. -/
theorem spectralRadius_lt_one_iff_tendsto_pow (a : A) :
    spectralRadius ℂ a < 1 ↔ Tendsto (fun n => a ^ n) atTop (𝓝 0) := by
  refine ⟨tendsto_pow_of_spectralRadius_lt_one, fun h => ?_⟩
  have hnorm : Tendsto (fun n => ‖a ^ n‖) atTop (𝓝 0) := by simpa using h.norm
  obtain ⟨n, hn⟩ := (hnorm.eventually_lt_const one_pos).exists
  exact spectralRadius_lt_one_of_norm_pow_lt_one hn

/-- A contraction has spectral radius `< 1`. The converse fails — a nilpotent matrix of large
norm has spectral radius `0` — and the right converse is
`spectralRadius_lt_one_iff_exists_norm_pow_lt_one`, which asks only for *some* power to be a
contraction. -/
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

/-! ### An arbitrary algebra norm bounds the spectral radius

The bound `ρ(a) ≤ N a` holds for *every* algebra norm on a finite-dimensional algebra, not only
for the norm the algebra carries as a normed algebra.  The norm is bundled as an `AlgebraNorm`
rather than supplied as an instance, because a second `NormedRing` instance on the same type would
bring its own ring structure, unrelated to the one the spectrum is computed from.

No analysis enters: in finite dimension an element that is a zero divisor on neither side is a
unit, and submultiplicativity of `N` makes `μ • 1 - a` such an element as soon as `N a < ‖μ‖`. -/

section AlgebraNorm

variable {𝕜 B : Type*} [NormedField 𝕜] [Ring B] [Algebra 𝕜 B]

/-- In a finite-dimensional algebra an element that is a zero divisor on neither side is a unit:
both multiplications by it are injective, hence surjective. -/
private theorem isUnit_of_mul_ne_zero [FiniteDimensional 𝕜 B] {x : B}
    (hl : ∀ y : B, y ≠ 0 → x * y ≠ 0) (hr : ∀ y : B, y ≠ 0 → y * x ≠ 0) : IsUnit x := by
  have hL : Function.Surjective (LinearMap.mulLeft 𝕜 x) :=
    LinearMap.injective_iff_surjective.mp <|
      (injective_iff_map_eq_zero _).mpr fun y hy => by by_contra hy0; exact hl y hy0 hy
  have hR : Function.Surjective (LinearMap.mulRight 𝕜 x) :=
    LinearMap.injective_iff_surjective.mp <|
      (injective_iff_map_eq_zero _).mpr fun y hy => by by_contra hy0; exact hr y hy0 hy
  obtain ⟨y, hy⟩ := hL 1
  obtain ⟨z, hz⟩ := hR 1
  rw [LinearMap.mulLeft_apply] at hy
  rw [LinearMap.mulRight_apply] at hz
  refine ⟨⟨x, y, hy, ?_⟩, rfl⟩
  calc y * x = z * x * (y * x) := by rw [hz, one_mul]
    _ = z * (x * y * x) := by simp only [mul_assoc]
    _ = z * x := by rw [hy, one_mul]
    _ = 1 := hz

/-- **The spectral radius is at most any algebra norm**: `ρ(a) ≤ N a` for every algebra norm `N`
on a finite-dimensional algebra over a normed field.

This is the general form of "`|λ| ≤ ‖A‖` for any consistent matrix norm": consistency is exactly
submultiplicativity of `N`, and no relation between `N` and a norm the algebra may already carry is
needed.  Positive definiteness of `N` is used and cannot be dropped — on two-by-two matrices
`B ↦ |det B| ^ (1 / 2)` is submultiplicative and absolutely homogeneous, sends `1` to `1`, and
vanishes on a rank-one matrix of spectral radius `1`. -/
theorem spectralRadius_le_algebraNorm [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B) (a : B) :
    spectralRadius 𝕜 a ≤ ENNReal.ofReal (N a) := by
  refine iSup₂_le fun μ hμ => ?_
  have hle : ‖μ‖ ≤ N a := by
    by_contra hcon
    have hlt : N a < ‖μ‖ := not_le.mp hcon
    have hpos : ∀ y : B, y ≠ 0 → 0 < N y := fun y hy =>
      lt_of_le_of_ne (apply_nonneg N y) fun h => hy (eq_zero_of_map_eq_zero N h.symm)
    have hleft : ∀ y : B, (‖μ‖ - N a) * N y ≤ N ((algebraMap 𝕜 B μ - a) * y) := by
      intro y
      have hsplit : algebraMap 𝕜 B μ * y = (algebraMap 𝕜 B μ - a) * y + a * y := by noncomm_ring
      have h1 : N (algebraMap 𝕜 B μ * y) ≤ N ((algebraMap 𝕜 B μ - a) * y) + N (a * y) := by
        rw [hsplit]; exact map_add_le_add N _ _
      have h2 : N (algebraMap 𝕜 B μ * y) = ‖μ‖ * N y := by
        rw [← Algebra.smul_def]; exact map_smul_eq_mul N _ _
      have h3 : N (a * y) ≤ N a * N y := map_mul_le_mul N _ _
      nlinarith
    have hright : ∀ y : B, (‖μ‖ - N a) * N y ≤ N (y * (algebraMap 𝕜 B μ - a)) := by
      intro y
      have hsplit : y * algebraMap 𝕜 B μ = y * (algebraMap 𝕜 B μ - a) + y * a := by noncomm_ring
      have h1 : N (y * algebraMap 𝕜 B μ) ≤ N (y * (algebraMap 𝕜 B μ - a)) + N (y * a) := by
        rw [hsplit]; exact map_add_le_add N _ _
      have h2 : N (y * algebraMap 𝕜 B μ) = ‖μ‖ * N y := by
        rw [← Algebra.commutes, ← Algebra.smul_def]; exact map_smul_eq_mul N _ _
      have h3 : N (y * a) ≤ N y * N a := map_mul_le_mul N _ _
      nlinarith
    refine spectrum.mem_iff.mp hμ
      (isUnit_of_mul_ne_zero (𝕜 := 𝕜) (fun y hy h0 => ?_) fun y hy h0 => ?_)
    · have h := hleft y
      rw [h0, map_zero] at h
      nlinarith [hpos y hy]
    · have h := hright y
      rw [h0, map_zero] at h
      nlinarith [hpos y hy]
  calc (‖μ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖μ‖ := (ofReal_norm μ).symm
    _ ≤ ENNReal.ofReal (N a) := ENNReal.ofReal_le_ofReal hle

end AlgebraNorm

omit [NormOneClass A] in
/-- If some algebra norm of `a` is `< 1`, the powers of `a` tend to `0`: the convergence criterion
for an arbitrary consistent matrix norm.  Only submultiplicativity of the norm relates it to the
algebra; the convergence is in the topology of `A`. -/
theorem tendsto_pow_of_algebraNorm_lt_one [FiniteDimensional ℂ A] (N : AlgebraNorm ℂ A) {a : A}
    (h : N a < 1) : Tendsto (fun n => a ^ n) atTop (𝓝 0) :=
  tendsto_pow_of_spectralRadius_lt_one
    ((spectralRadius_le_algebraNorm N a).trans_lt (ENNReal.ofReal_lt_one.mpr h))
