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
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Spectral radius and convergence of powers

In a complex unital Banach algebra, `ρ(a) < 1 ↔ aⁿ → 0`, the Neumann series `∑ aⁿ` converges iff
`ρ(a) < 1`, and powers decay geometrically at any rate above the spectral radius. All three are
classical consequences of Gelfand's formula for the spectral radius, which Mathlib provides as
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`.

## Main statements

* `spectralRadius_smul`, the absolute homogeneity `ρ(c • a) = ‖c‖ ρ(a)`, which needs no analytic
  input and holds in any algebra over a normed field, with `spectralRadius_star` and
  `spectralRadius_eq_iSup_diff_singleton_zero` (the star and the eigenvalue `0` do not change it);
* `spectralRadius_lt_one_iff_tendsto_pow`, `spectralRadius_lt_one_iff_exists_norm_pow_lt_one` and
  `summable_pow_iff_spectralRadius_lt_one`, the three criteria in terms of the powers;
* `exists_norm_pow_le_of_spectralRadius_lt`, geometric decay of the powers at any rate above the
  spectral radius;
* `spectrum.spectralRadius_ne_top` and
  `spectrum.pow_norm_pow_one_div_tendsto_nhds_toReal_spectralRadius`, finiteness of the spectral
  radius and Gelfand's formula as a limit in `ℝ`;
* `spectralRadius_pow`, the power rule `ρ(aⁿ) = ρ(a)ⁿ`, from the spectral mapping theorem;
* `hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one`, the Neumann series `∑ aⁿ = (1 - a)⁻¹`
  under `ρ(a) < 1` alone;
* `spectralRadius_le_algebraNorm`, bounding the spectral radius by an *arbitrary* algebra norm on
  a finite-dimensional algebra — "`|λ| ≤ ‖A‖` for any consistent matrix norm" — with no analysis
  and no relation to the norm the algebra already carries;
* `isUnit_one_sub_of_algebraNorm_lt_one` with `AlgebraNorm.norm_inverse_one_sub_le_of_lt_one` and
  `AlgebraNorm.one_div_one_add_le_norm_inverse_one_sub`, the two-sided bound
  `1 / (1 + N a) ≤ N ((1 - a)⁻¹) ≤ 1 / (1 - N a)` for an arbitrary unital algebra norm with
  `N a < 1`, [quarteroni2000numerical] (1.26).
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
    simp only [spectralRadius_eq_of_unital, hset, ← Set.image_smul, iSup_image, smul_eq_mul,
      nnnorm_mul, ENNReal.coe_mul, ENNReal.mul_iSup]

/-- The spectral radius does not see the eigenvalue `0`: `ρ(a)` is the supremum of `‖λ‖₊` over
`σ(a) ∖ {0}`, since `‖0‖₊ = 0` contributes nothing to a supremum in `ℝ≥0∞`. -/
theorem spectralRadius_eq_iSup_diff_singleton_zero (a : B) :
    spectralRadius 𝕜 a = ⨆ μ ∈ spectrum 𝕜 a \ {0}, (‖μ‖₊ : ℝ≥0∞) := by
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ =>
    le_iSup₂ (f := fun μ (_ : μ ∈ spectrum 𝕜 a) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) μ hμ.1)
  rcases eq_or_ne μ 0 with rfl | h0
  · simp
  · exact le_iSup₂ (f := fun μ (_ : μ ∈ spectrum 𝕜 a \ {0}) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) μ ⟨hμ, h0⟩

/-- The spectral radius is invariant under the star: `ρ(star a) = ρ(a)`, because
`σ(star a) = star σ(a)` (`spectrum.map_star`) and the norm is star-invariant. -/
theorem spectralRadius_star [StarRing 𝕜] [NormedStarGroup 𝕜] [StarRing B] [StarModule 𝕜 B]
    (a : B) : spectralRadius 𝕜 (star a) = spectralRadius 𝕜 a := by
  have key : ∀ b : B, spectralRadius 𝕜 (star b) ≤ spectralRadius 𝕜 b := fun b => by
    rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
    refine iSup₂_le fun k hk => ?_
    rw [spectrum.map_star, Set.mem_star] at hk
    calc ((‖k‖₊ : ℝ≥0) : ℝ≥0∞) = ‖star k‖₊ := by rw [nnnorm_star]
      _ ≤ ⨆ k ∈ spectrum 𝕜 b, ((‖k‖₊ : ℝ≥0) : ℝ≥0∞) :=
        le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 b) => ((‖k‖₊ : ℝ≥0) : ℝ≥0∞)) (star k) hk
  exact le_antisymm (key a) (by simpa using key (star a))

/-- The power rule `ρ(aⁿ) = ρ(a)ⁿ` for an element with nonempty spectrum of an algebra over an
algebraically closed normed field: the spectral mapping theorem `spectrum.map_pow_of_nonempty`
gives `σ(aⁿ) = (· ^ n) '' σ(a)`, and `‖·‖₊ ^ n` commutes with the supremum. Nonemptiness is only
needed at `n = 0`, where it makes the algebra nontrivial. -/
theorem spectralRadius_pow_of_nonempty [IsAlgClosed 𝕜] {a : B} (ha : (spectrum 𝕜 a).Nonempty)
    (n : ℕ) : spectralRadius 𝕜 (a ^ n) = spectralRadius 𝕜 a ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Nontrivial B := by
      obtain ⟨z, hz⟩ := ha
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact spectrum.mem_iff.mp hz (isUnit_of_subsingleton _)
    simp
  refine le_antisymm ?_ (spectrum.spectralRadius_pow_le a n hn.ne')
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital, spectrum.map_pow_of_nonempty ha n]
  refine iSup₂_le fun z hz => ?_
  obtain ⟨w, hw, rfl⟩ := hz
  calc (‖w ^ n‖₊ : ℝ≥0∞) = (‖w‖₊ : ℝ≥0∞) ^ n := by rw [nnnorm_pow, ENNReal.coe_pow]
    _ ≤ (⨆ k ∈ spectrum 𝕜 a, (‖k‖₊ : ℝ≥0∞)) ^ n :=
        pow_le_pow_left' (le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 a) => (‖k‖₊ : ℝ≥0∞)) w hw) n

end Homogeneous

section Finite

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-- The spectral radius of an element of a complete normed algebra is finite: the spectrum lies
in the closed ball of radius `‖a‖ ‖1‖` (`spectrum.spectralRadius_le_pow_nnnorm_pow_one_div` at
`n = 0`). -/
theorem spectrum.spectralRadius_ne_top (a : A) : spectralRadius 𝕜 a ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top))
    (spectrum.spectralRadius_le_pow_nnnorm_pow_one_div 𝕜 a 0)

end Finite

section Conjugate

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- The spectral radius of an operator is at most the norm of any conjugate `v P v⁻¹` of it:
similarity preserves the spectrum, and the spectral radius is at most the norm. -/
theorem spectralRadius_le_nnnorm_conj {v : E →L[𝕜] E} (hv : IsUnit v) (P : E →L[𝕜] E) :
    spectralRadius 𝕜 P ≤ ‖v * P * Ring.inverse v‖₊ := by
  obtain ⟨u, rfl⟩ := hv
  rw [Ring.inverse_unit]
  rcases subsingleton_or_nontrivial E with _ | _
  · have : Subsingleton (E →L[𝕜] E) := ⟨fun _ _ => by ext x; exact Subsingleton.elim _ _⟩
    simp [spectralRadius]
  · rw [spectralRadius_eq_of_unital, ← spectrum.units_conjugate (a := P) (u := u)]
    exact iSup₂_le fun k hk => mod_cast spectrum.norm_le_norm_of_mem hk

end Conjugate

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

omit [NormOneClass A] in
/-- **Gelfand's formula, real-valued**: `‖aⁿ‖ ^ (1 / n) → ρ(a)` in `ℝ`, the spectral radius
being finite (`spectrum.spectralRadius_ne_top`). This is Mathlib's
`spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius` with the `ENNReal` coercions
removed, the form in which every norm-independent limit argument uses it. -/
theorem spectrum.pow_norm_pow_one_div_tendsto_nhds_toReal_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 (spectralRadius ℂ a).toReal) := by
  have h := (ENNReal.tendsto_toReal (spectrum.spectralRadius_ne_top a)).comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a)
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

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
  have h2 : spectralRadius ℂ (a ^ n) ≤ (‖a ^ n‖₊ : ℝ≥0∞) := spectralRadius_le_nnnorm _
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

/-- The Neumann series under the spectral-radius hypothesis alone: when `ρ(a) < 1`,
`∑ aⁿ` sums to `(1 - a)⁻¹`. Mathlib's `NormedRing.tsum_geometric_of_norm_lt_one` and
`geom_series_eq_inverse` ask for `‖a‖ < 1`; this is [quarteroni2000numerical] Theorem 1.5,
display (1.25). -/
theorem hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one {a : A}
    (h : spectralRadius ℂ a < 1) : HasSum (fun n => a ^ n) (Ring.inverse (1 - a)) := by
  have hs : Summable (a ^ ·) := (summable_pow_iff_spectralRadius_lt_one a).mpr h
  let u : Aˣ := ⟨1 - a, ∑' n : ℕ, a ^ n, hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩
  have hu : Ring.inverse (1 - a) = ∑' n : ℕ, a ^ n := Ring.inverse_unit u
  rw [hu]
  exact hs.hasSum

/-- The power rule `ρ(aⁿ) = ρ(a)ⁿ` in a complex Banach algebra; the case of nonempty spectrum
of `spectralRadius_pow_of_nonempty`, nonemptiness being `spectrum.nonempty`. Mathlib has the
inequality `spectrum.spectralRadius_pow_le`. [quarteroni2000numerical] §1.7. -/
theorem spectralRadius_pow (a : A) (n : ℕ) :
    spectralRadius ℂ (a ^ n) = spectralRadius ℂ a ^ n :=
  have : Nontrivial A := NormOneClass.nontrivial
  spectralRadius_pow_of_nonempty (spectrum.nonempty a) n

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
  rw [spectralRadius_eq_of_unital]
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

/-- If some algebra norm of `a` is `< 1`, then `1 - a` is a unit: `1 ∉ σ(a)` because
`ρ(a) ≤ N a < 1 = ‖1‖`. Finite dimension replaces completeness; no topology on `B` enters. -/
theorem isUnit_one_sub_of_algebraNorm_lt_one [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B) {a : B}
    (h : N a < 1) : IsUnit (1 - a) := by
  have h1 : (1 : 𝕜) ∈ resolventSet 𝕜 a :=
    spectrum.mem_resolventSet_of_spectralRadius_lt <|
      (spectralRadius_le_algebraNorm N a).trans_lt (by simpa using ENNReal.ofReal_lt_one.mpr h)
  simpa using spectrum.mem_resolventSet_iff.mp h1

namespace AlgebraNorm

/-- The Neumann bound for an arbitrary algebra norm with `N a < 1`, in the form that does not
assume `N 1 = 1`: `N ((1 - a)⁻¹) ≤ N 1 / (1 - N a)`, from `(1 - a)⁻¹ = 1 + a (1 - a)⁻¹`. -/
theorem norm_inverse_one_sub_le_div_of_lt_one [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B) {a : B}
    (h : N a < 1) : N (Ring.inverse (1 - a)) ≤ N 1 / (1 - N a) := by
  have hu := isUnit_one_sub_of_algebraNorm_lt_one N h
  set u := Ring.inverse (1 - a) with hu_def
  have key : u = 1 + a * u := by
    have := Ring.mul_inverse_cancel (1 - a) hu
    rw [← hu_def] at this
    calc u = (1 - a) * u + a * u := by noncomm_ring
      _ = 1 + a * u := by rw [this]
  have hle : N u ≤ 1 * N 1 + N a * N u := by
    calc N u = N (1 + a * u) := by rw [← key]
      _ ≤ N 1 + N (a * u) := map_add_le_add N _ _
      _ ≤ 1 * N 1 + N a * N u := by rw [one_mul]; gcongr; exact map_mul_le_mul N _ _
  rw [le_div_iff₀ (by linarith)]
  nlinarith [apply_nonneg N u]

/-- The lower bound for the inverse of a unit `1 - a` under an arbitrary algebra norm, in the
form that does not assume `N 1 = 1`: `N 1 / (N 1 + N a) ≤ N ((1 - a)⁻¹)`, from
`N 1 = N ((1 - a) (1 - a)⁻¹) ≤ (N 1 + N a) N ((1 - a)⁻¹)`. -/
theorem div_add_le_norm_inverse_one_sub (N : AlgebraNorm 𝕜 B) {a : B} (hu : IsUnit (1 - a)) :
    N 1 / (N 1 + N a) ≤ N (Ring.inverse (1 - a)) := by
  set u := Ring.inverse (1 - a) with hu_def
  have hmul : (1 - a) * u = 1 := Ring.mul_inverse_cancel (1 - a) hu
  have h1 : N 1 ≤ (N 1 + N a) * N u := by
    calc N 1 = N ((1 - a) * u) := by rw [hmul]
      _ ≤ N (1 - a) * N u := map_mul_le_mul N _ _
      _ ≤ (N 1 + N a) * N u := by gcongr; exact map_sub_le_add N 1 a
  rcases (add_nonneg (apply_nonneg N 1) (apply_nonneg N a)).lt_or_eq with hpos | hzero
  · exact (div_le_iff₀ hpos).mpr (by linarith)
  · rw [← hzero, div_zero]; exact apply_nonneg N u

/-- **The upper bound of [quarteroni2000numerical] (1.26)** for an arbitrary unital algebra norm
`N` (`N 1 = 1`) on a finite-dimensional algebra: `N a < 1` makes `1 - a` a unit with
`N ((1 - a)⁻¹) ≤ 1 / (1 - N a)`. For the norm the algebra carries this is
`NormedRing.norm_inverse_one_sub_le`; here `N` is unrelated to any topology on `B`. -/
theorem norm_inverse_one_sub_le_of_lt_one [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B)
    (h1 : N 1 = 1) {a : B} (h : N a < 1) : N (Ring.inverse (1 - a)) ≤ 1 / (1 - N a) :=
  h1 ▸ norm_inverse_one_sub_le_div_of_lt_one N h

/-- **The lower bound of [quarteroni2000numerical] (1.26)** for an arbitrary unital algebra norm
`N` (`N 1 = 1`) on a finite-dimensional algebra: if `N a < 1` then
`1 / (1 + N a) ≤ N ((1 - a)⁻¹)`. -/
theorem one_div_one_add_le_norm_inverse_one_sub [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B)
    (h1 : N 1 = 1) {a : B} (h : N a < 1) : 1 / (1 + N a) ≤ N (Ring.inverse (1 - a)) :=
  h1 ▸ div_add_le_norm_inverse_one_sub N (isUnit_one_sub_of_algebraNorm_lt_one N h)

end AlgebraNorm

end AlgebraNorm

omit [NormOneClass A] in
/-- If some algebra norm of `a` is `< 1`, the powers of `a` tend to `0`: the convergence criterion
for an arbitrary consistent matrix norm.  Only submultiplicativity of the norm relates it to the
algebra; the convergence is in the topology of `A`. -/
theorem tendsto_pow_of_algebraNorm_lt_one [FiniteDimensional ℂ A] (N : AlgebraNorm ℂ A) {a : A}
    (h : N a < 1) : Tendsto (fun n => a ^ n) atTop (𝓝 0) :=
  tendsto_pow_of_spectralRadius_lt_one
    ((spectralRadius_le_algebraNorm N a).trans_lt (ENNReal.ofReal_lt_one.mpr h))
