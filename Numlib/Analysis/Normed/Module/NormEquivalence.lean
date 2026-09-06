/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.FiniteDimension`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Equivalence of norms on a finite-dimensional real normed space

Mathlib records that all norms on a finite-dimensional space over a complete nontrivially normed
field induce the same topology, but not the two-sided inequality itself: "it would mean having two
norms on a single space, which is not the way type classes work"
(`Mathlib/Analysis/Normed/Module/FiniteDimension.lean`). The inequality is what a theorem
quantifying over *an arbitrary* norm needs — Gelfand's formula `‖A^k‖^{1/k} → ρ(A)`, say, whose
limit is the same for every matrix norm although only the ambient one is convenient to prove it
for — so it is proved here for a second norm given unbundled, as a `Seminorm ℝ E` together with
definiteness.

The upper bound `p x ≤ C ‖x‖` is the elementary half: expand `x` in a basis and use subadditivity.
The lower bound `c ‖x‖ ≤ p x` is where finite-dimensionality really enters: `p` is then Lipschitz,
hence continuous, and the unit sphere is compact, so `p` attains a positive minimum on it.

A norm on a complex vector space is in particular a `Seminorm ℝ` on the underlying real space, and
finite complex dimension is finite real dimension, so the real statement covers the complex case.

## Main results

* `Seminorm.exists_le_mul_norm`: `∃ C > 0, ∀ x, p x ≤ C ‖x‖`, for any seminorm on a
  finite-dimensional space.
* `Seminorm.exists_mul_norm_le`: `∃ c > 0, ∀ x, c ‖x‖ ≤ p x`, for a *definite* one.
* `Seminorm.exists_bounds`: the two together, which is the equivalence of the two norms.
* `Seminorm.tendsto_rpow_one_div`: the `k`-th root growth rate `‖f k‖ ^ (1 / k)` of a sequence has
  the same limit for every norm, which is the form the Gelfand-type statements want.
-/

open Filter Metric Topology

namespace Seminorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Any seminorm on a finite-dimensional real normed space is bounded by a multiple of the norm.
The proof expands a vector in a basis: the coordinate functionals are continuous because the space
is finite-dimensional, and subadditivity does the rest. -/
theorem exists_le_mul_norm (p : Seminorm ℝ E) : ∃ C : ℝ, 0 < C ∧ ∀ x, p x ≤ C * ‖x‖ := by
  classical
  set b := Module.finBasis ℝ E with hb
  have hcoord : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, |b.repr x i| ≤ K * ‖x‖ := by
    intro i
    refine ⟨‖LinearMap.toContinuousLinearMap (b.coord i)‖, norm_nonneg _, fun x => ?_⟩
    simpa [Real.norm_eq_abs] using (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm x
  choose K hK hKle using hcoord
  refine ⟨(∑ i, K i * p (b i)) + 1, ?_, fun x => ?_⟩
  · have hnn : (0 : ℝ) ≤ ∑ i, K i * p (b i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hK i) (apply_nonneg p _)
    linarith
  · have hx : p x ≤ ∑ i, p (b.repr x i • b i) := by
      conv_lhs => rw [← b.sum_repr x]
      exact Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
    have hstep : ∀ i, p (b.repr x i • b i) ≤ (K i * ‖x‖) * p (b i) := by
      intro i
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hKle i x) (apply_nonneg p _)
    have hsum : ∑ i, p (b.repr x i • b i) ≤ (∑ i, K i * p (b i)) * ‖x‖ := by
      refine (Finset.sum_le_sum fun i _ => hstep i).trans_eq ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hnorm := norm_nonneg x
    nlinarith [hx.trans hsum]

/-- A seminorm on a finite-dimensional real normed space is continuous: the bound of
`Seminorm.exists_le_mul_norm` makes it Lipschitz. -/
theorem continuous_of_finiteDimensional (p : Seminorm ℝ E) : Continuous p := by
  obtain ⟨C, hC, hle⟩ := p.exists_le_mul_norm
  refine LipschitzWith.continuous (K := Real.toNNReal C)
    (LipschitzWith.of_dist_le_mul fun x y => ?_)
  have hxy : p x ≤ p (x - y) + p y := by
    simpa using map_add_le_add p (x - y) y
  have hyx : p y ≤ p (y - x) + p x := by
    simpa using map_add_le_add p (y - x) x
  have h₁ := hle (x - y)
  have h₂ := hle (y - x)
  rw [norm_sub_rev] at h₂
  rw [Real.coe_toNNReal C hC.le, Real.dist_eq, dist_eq_norm]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A **definite** seminorm on a finite-dimensional real normed space dominates a multiple of the
norm.  This is the half that needs compactness: `p` is continuous and positive on the unit sphere,
which is compact, so it has a positive minimum there, and homogeneity spreads the bound. -/
theorem exists_mul_norm_le (p : Seminorm ℝ E) (hp : ∀ x : E, p x = 0 → x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ p x := by
  rcases subsingleton_or_nontrivial E with _ | _
  · refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]
    simp
  · have hcpt : IsCompact (sphere (0 : E) 1) := isCompact_sphere 0 1
    have hne : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
    obtain ⟨x₀, hx₀, hmin⟩ :=
      hcpt.exists_isMinOn hne p.continuous_of_finiteDimensional.continuousOn
    have hx₀norm : ‖x₀‖ = 1 := mem_sphere_zero_iff_norm.1 hx₀
    have hx₀ne : x₀ ≠ 0 := fun h => by simp [h] at hx₀norm
    have hpos : 0 < p x₀ := lt_of_le_of_ne (apply_nonneg p _) fun h => hx₀ne (hp x₀ h.symm)
    refine ⟨p x₀, hpos, fun x => ?_⟩
    rcases eq_or_ne x 0 with rfl | hxne
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hxne
      have hmem : ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
        field_simp
      have hle : p x₀ ≤ p (‖x‖⁻¹ • x) := hmin hmem
      rw [map_smul_eq_mul, norm_inv, norm_norm] at hle
      rw [mul_comm]
      calc ‖x‖ * p x₀ ≤ ‖x‖ * (‖x‖⁻¹ * p x) := mul_le_mul_of_nonneg_left hle hxpos.le
        _ = p x := by field_simp

/-- **Equivalence of norms in finite dimension.** A definite seminorm on a finite-dimensional real
normed space is bounded above and below by multiples of the norm. -/
theorem exists_bounds (p : Seminorm ℝ E) (hp : ∀ x : E, p x = 0 → x = 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ≤ p x ∧ p x ≤ C * ‖x‖ := by
  obtain ⟨c, hc, hcle⟩ := p.exists_mul_norm_le hp
  obtain ⟨C, hC, hCle⟩ := p.exists_le_mul_norm
  exact ⟨c, C, hc, hC, fun x => ⟨hcle x, hCle x⟩⟩

/-! ### Root asymptotics are the same for every norm -/

/-- A positive constant has `k`-th roots tending to `1`, which is why the factor between two
equivalent norms is invisible to a `k`-th root asymptotic. -/
private theorem tendsto_const_rpow_one_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => c ^ (1 / k : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => Real.log c * (1 / k : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log c)
  simpa [Function.comp_def, Real.rpow_def_of_pos hc] using
    (Real.continuous_exp.tendsto 0).comp h

/-- **A `k`-th root growth rate does not depend on the norm.**  If `‖f k‖ ^ (1 / k) → L` then
`p (f k) ^ (1 / k) → L` for every norm `p` on the same finite-dimensional space: by
`Seminorm.exists_bounds` the two differ by factors `c ^ (1 / k)` and `C ^ (1 / k)`, and both tend
to `1`.  No submultiplicativity is used, so this upgrades a Gelfand-type limit
`‖A ^ k‖ ^ (1 / k) → ρ(A)`, proved for one convenient norm, to an arbitrary norm at once. -/
theorem tendsto_rpow_one_div (p : Seminorm ℝ E) (hp : ∀ x : E, p x = 0 → x = 0) {f : ℕ → E}
    {L : ℝ} (hf : Tendsto (fun k : ℕ => ‖f k‖ ^ (1 / k : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun k : ℕ => p (f k) ^ (1 / k : ℝ)) atTop (𝓝 L) := by
  obtain ⟨c, C, hc, hC, hb⟩ := p.exists_bounds hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun k : ℕ => c ^ (1 / k : ℝ) * ‖f k‖ ^ (1 / k : ℝ))
    (h := fun k : ℕ => C ^ (1 / k : ℝ) * ‖f k‖ ^ (1 / k : ℝ))
    (by simpa using (tendsto_const_rpow_one_div hc).mul hf)
    (by simpa using (tendsto_const_rpow_one_div hC).mul hf) (fun k => ?_) fun k => ?_
  · dsimp only
    rw [← Real.mul_rpow hc.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (hb (f k)).1 (by positivity)
  · dsimp only
    rw [← Real.mul_rpow hC.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (apply_nonneg p _) (hb (f k)).2 (by positivity)

end Seminorm
