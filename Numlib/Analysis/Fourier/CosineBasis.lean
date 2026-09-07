/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Fourier.AddCircle` or a file beside it.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The half-range cosine system as a Hilbert basis of `L²(0, π)`

The system

`e₀ = 1/√π`, `eₖ = √(2/π) cos (k x)` for `k ≥ 1`

is orthonormal and complete in `L²(0, π)`. It is the cosine half of the trigonometric system of
`Numlib.Analysis.Fourier.TrigonometricBasis`, and it is what a cosine series on a half period
expands in; [han2009theoretical] state it as Example 1.3.14.

The classical proof extends a function of `L²(0, π)` evenly to `L²(-π, π)` and reads off the
completeness from the full trigonometric system. The proof here is the other classical one, and is
shorter in this setting: the span of `{x ↦ cos (k x)}` is a *subalgebra* of `C([0, π], ℝ)`, by the
product-to-sum formula alone, and it separates the points of `[0, π]` because `cos` is injective
there (`Real.injOn_cos`). Stone–Weierstrass then makes it dense in `C([0, π], ℝ)`, and continuous
functions are dense in `L²`. No even-extension isometry and no Chebyshev expansion of `cosᵏ` is
needed.

## Main definitions

* `halfRangeMeasure`, Lebesgue measure on `[0, π]` read on the subtype, the measure of `L²(0, π)`;
* `cosMap k : C([0, π], ℝ)`, the raw system `x ↦ cos (k x)`;
* `cosNorm k` and `cosFun k`, the normalizing constants `1/√π`, `√(2/π)` and the normalized system;
* `cosLp k : Lp ℝ 2 halfRangeMeasure`, the system inside `L²(0, π)`;
* `cosSubalgebra`, the span of the raw system as a subalgebra of `C([0, π], ℝ)`;
* `cosBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 halfRangeMeasure)`.

## Main statements

* `integral_cos_nat_mul_cos_nat_mul`, the orthogonality relations on `[0, π]`;
* `orthonormal_cosLp`, the system is orthonormal;
* `dense_span_cosMap`, Stone–Weierstrass for the cosine polynomials on `[0, π]`;
* `orthogonal_span_cosLp_eq_bot`, the completeness, and `cosBasis` assembling the two.

## References

[han2009theoretical], Example 1.3.14.
-/


open MeasureTheory Set Submodule

open scoped ENNReal Real

/-- Lebesgue measure on `[0, π]`, read on the subtype: the measure of `L²(0, π)`. -/
noncomputable def halfRangeMeasure : Measure (Icc (0 : ℝ) π) := Measure.comap Subtype.val volume

instance : IsFiniteMeasure halfRangeMeasure where
  measure_univ_lt_top := by
    have h : halfRangeMeasure univ = (volume.restrict (Icc (0 : ℝ) π)) univ := by
      rw [halfRangeMeasure, ← map_comap_subtype_coe (measurableSet_Icc (a := (0:ℝ)) (b := π))
        (volume : Measure ℝ), Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
        Set.preimage_univ]
    rw [h, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

/-- An integral over the subtype `[0, π]` is an interval integral. -/
theorem integral_halfRangeMeasure (f : ℝ → ℝ) :
    ∫ x : Icc (0 : ℝ) π, f x ∂halfRangeMeasure = ∫ x in (0 : ℝ)..π, f x := by
  rw [halfRangeMeasure, integral_subtype_comap measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]

/-- `∫_0^π cos (m x) dx` is `π` at `m = 0` and `0` at every other integer frequency. -/
theorem integral_cos_int_mul (m : ℤ) :
    ∫ x in (0 : ℝ)..π, Real.cos (m * x) = if m = 0 then π else 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hm0 : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm0, integral_cos]
    simp [Real.sin_int_mul_pi, hm]

/-- **The half-range cosine system is orthogonal on `[0, π]`**, with `π` and `π/2` as the squared
norms of the constant and of the higher cosines. -/
theorem integral_cos_nat_mul_cos_nat_mul (j k : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.cos (j * x) * Real.cos (k * x)
      = if j = k then (if j = 0 then π else π / 2) else 0 := by
  have hprod : ∀ x ∈ uIcc (0 : ℝ) π, Real.cos (j * x) * Real.cos (k * x)
      = (Real.cos (((j : ℤ) + k : ℤ) * x) + Real.cos (((j : ℤ) - k : ℤ) * x)) / 2 := by
    intro x _
    have h1 := Real.cos_add (j * x) (k * x)
    have h2 := Real.cos_sub (j * x) (k * x)
    have e1 : (((j : ℤ) + k : ℤ) : ℝ) * x = j * x + k * x := by push_cast; ring
    have e2 : (((j : ℤ) - k : ℤ) : ℝ) * x = j * x - k * x := by push_cast; ring
    rw [e1, e2, h1, h2]
    ring
  rw [intervalIntegral.integral_congr hprod]
  have hi1 : IntervalIntegrable (fun x => Real.cos (((j : ℤ) + k : ℤ) * x)) volume 0 π :=
    (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => Real.cos (((j : ℤ) - k : ℤ) * x)) volume 0 π :=
    (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2,
    integral_cos_int_mul, integral_cos_int_mul]
  by_cases hjk : j = k
  · subst hjk
    by_cases hj : j = 0
    · subst hj; norm_num
    · have h1 : ((j : ℤ) + j) ≠ 0 := by
        have hj' : (j : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hj
        omega
      simp [h1, hj]
  · have h1 : ((j : ℤ) + k : ℤ) ≠ 0 := by
      have hj' : (0 : ℤ) ≤ j := Int.natCast_nonneg j
      have hk' : (0 : ℤ) ≤ k := Int.natCast_nonneg k
      have : (j : ℤ) ≠ k := by exact_mod_cast fun h => hjk (Nat.cast_injective h)
      omega
    have h2 : ((j : ℤ) - k : ℤ) ≠ 0 := by
      simpa [sub_eq_zero, Nat.cast_inj] using hjk
    simp [h1, h2, hjk]

/-- The raw cosine system `x ↦ cos (k x)` on `[0, π]`. -/
noncomputable def cosMap (k : ℕ) : C(Icc (0 : ℝ) π, ℝ) := ⟨fun x => Real.cos (k * x), by fun_prop⟩

/-- The normalizing constants of the half-range cosine system: `1/√π` for the constant term and
`√(2/π)` for the rest. -/
noncomputable def cosNorm (k : ℕ) : ℝ := if k = 0 then 1 / √π else √(2 / π)

/-- The constant term of the system is normalized by `1/√π`. -/
theorem cosNorm_zero : cosNorm 0 = 1 / √π := by simp [cosNorm]

/-- Every cosine of positive frequency is normalized by `√(2/π)`. -/
theorem cosNorm_of_ne_zero {k : ℕ} (hk : k ≠ 0) : cosNorm k = √(2 / π) := by simp [cosNorm, hk]

/-- The normalizing constants are nonzero, so `cosFun` and `cosMap` span the same space. -/
theorem cosNorm_ne_zero (k : ℕ) : cosNorm k ≠ 0 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; rw [cosNorm_zero]; positivity
  · rw [cosNorm_of_ne_zero hk]; positivity

/-- The half-range cosine system, as continuous functions on `[0, π]`. -/
noncomputable def cosFun (k : ℕ) : C(Icc (0 : ℝ) π, ℝ) := cosNorm k • cosMap k

/-- The half-range cosine system as an orthonormal family in `L²(0, π)`. -/
noncomputable def cosLp (k : ℕ) : Lp ℝ 2 halfRangeMeasure :=
  ContinuousMap.toLp 2 halfRangeMeasure ℝ (cosFun k)

/-- The normalized system is a nonzero multiple of the raw one, inside `L²(0, π)`. -/
theorem cosLp_eq_smul (k : ℕ) :
    cosLp k = cosNorm k • ContinuousMap.toLp 2 halfRangeMeasure ℝ (cosMap k) := by
  rw [cosLp, cosFun, map_smul]

/-- The inner products of the half-range cosine system: it is orthonormal. -/
theorem inner_cosLp (j k : ℕ) : inner ℝ (cosLp j) (cosLp k) = if j = k then 1 else 0 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hae : ∀ m : ℕ, (cosLp m : Icc (0 : ℝ) π → ℝ) =ᵐ[halfRangeMeasure] cosFun m :=
    fun m => ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (𝕜 := ℝ) halfRangeMeasure (cosFun m)
  rw [MeasureTheory.L2.inner_def]
  have key : ∫ x, inner ℝ ((cosLp j : Icc (0 : ℝ) π → ℝ) x) ((cosLp k : Icc (0 : ℝ) π → ℝ) x)
        ∂halfRangeMeasure
      = ∫ x : Icc (0 : ℝ) π, (cosNorm j * cosNorm k) *
          (Real.cos (j * (x : ℝ)) * Real.cos (k * (x : ℝ))) ∂halfRangeMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [hae j, hae k] with x hxj hxk
    rw [hxj, hxk, RCLike.inner_apply]
    simp only [cosFun, cosMap, ContinuousMap.smul_apply, ContinuousMap.coe_mk, smul_eq_mul,
      conj_trivial]
    ring
  rw [key, integral_const_mul,
    integral_halfRangeMeasure (fun t => Real.cos (j * t) * Real.cos (k * t)),
    integral_cos_nat_mul_cos_nat_mul]
  rcases eq_or_ne j k with hjk | hjk
  · subst hjk
    have hite : (if j = j then (if j = 0 then π else π / 2) else 0)
        = if j = 0 then π else π / 2 := by simp
    have hgoal : (if j = j then (1 : ℝ) else 0) = 1 := by simp
    rw [hite, hgoal]
    rcases eq_or_ne j 0 with hj | hj
    · subst hj
      have h2 : (if (0 : ℕ) = 0 then π else π / 2) = π := by simp
      rw [cosNorm_zero, h2,
        show (1 : ℝ) / √π * (1 / √π) * π = π / (√π * √π) by ring,
        Real.mul_self_sqrt hπ.le, div_self hπ.ne']
    · have h2 : (if j = 0 then π else π / 2) = π / 2 := by simp [hj]
      rw [cosNorm_of_ne_zero hj, h2,
        show √(2 / π) * √(2 / π) * (π / 2) = (√(2 / π) * √(2 / π)) * (π / 2) by ring,
        Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 / π)]
      field_simp
  · simp [hjk]

/-- **The half-range cosine system is orthonormal in `L²(0, π)`.** -/
theorem orthonormal_cosLp : Orthonormal ℝ cosLp := orthonormal_iff_ite.2 inner_cosLp

/-- The product-to-sum formula: the span of the cosine system is closed under multiplication. -/
theorem cosMap_mul (m n : ℕ) :
    cosMap m * cosMap n = (2 : ℝ)⁻¹ • (cosMap (m + n) + cosMap (max m n - min m n)) := by
  ext x
  simp only [cosMap, ContinuousMap.mul_apply, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
    ContinuousMap.add_apply, smul_eq_mul]
  have hadd : ((m + n : ℕ) : ℝ) * (x : ℝ) = m * (x : ℝ) + n * (x : ℝ) := by push_cast; ring
  rcases le_total n m with h | h
  · have hsub : ((max m n - min m n : ℕ) : ℝ) * (x : ℝ) = m * (x : ℝ) - n * (x : ℝ) := by
      rw [max_eq_left h, min_eq_right h, Nat.cast_sub h]; ring
    rw [hadd, hsub, Real.cos_add, Real.cos_sub]
    ring
  · have hsub : ((max m n - min m n : ℕ) : ℝ) * (x : ℝ) = n * (x : ℝ) - m * (x : ℝ) := by
      rw [max_eq_right h, min_eq_left h, Nat.cast_sub h]; ring
    rw [hadd, hsub, Real.cos_add, Real.cos_sub]
    ring

/-- The constant function is the `k = 0` member of the raw cosine system. -/
theorem one_mem_span_cosMap : (1 : C(Icc (0 : ℝ) π, ℝ)) ∈ span ℝ (Set.range cosMap) := by
  have h : cosMap 0 = 1 := by ext x; simp [cosMap]
  rw [← h]
  exact subset_span ⟨0, rfl⟩

/-- The span of the raw cosine system is closed under multiplication. -/
theorem mul_mem_span_cosMap {f g : C(Icc (0 : ℝ) π, ℝ)} (hf : f ∈ span ℝ (Set.range cosMap))
    (hg : g ∈ span ℝ (Set.range cosMap)) : f * g ∈ span ℝ (Set.range cosMap) := by
  have hgen : ∀ m : ℕ, ∀ y ∈ span ℝ (Set.range cosMap),
      cosMap m * y ∈ span ℝ (Set.range cosMap) := by
    intro m y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨n, rfl⟩ := hz
        rw [cosMap_mul]
        exact Submodule.smul_mem _ _
          (Submodule.add_mem _ (subset_span ⟨_, rfl⟩) (subset_span ⟨_, rfl⟩))
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
  induction hf using Submodule.span_induction with
  | mem z hz => obtain ⟨m, rfl⟩ := hz; exact hgen m g hg
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

/-- The span of the cosine system, as a subalgebra of `C([0, π], ℝ)`. -/
noncomputable def cosSubalgebra : Subalgebra ℝ C(Icc (0 : ℝ) π, ℝ) :=
  (span ℝ (Set.range cosMap)).toSubalgebra one_mem_span_cosMap
    fun _ _ hx hy => mul_mem_span_cosMap hx hy

/-- The cosine polynomials separate the points of `[0, π]`, because `cos` is injective there. -/
theorem separatesPoints_cosSubalgebra : cosSubalgebra.SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨cosMap 1, subset_span ⟨1, rfl⟩, rfl⟩, ?_⟩
  simp only [cosMap, ContinuousMap.coe_mk, Nat.cast_one, one_mul]
  intro h
  exact hxy (Subtype.ext (Real.injOn_cos x.2 y.2 h))

/-- **Stone–Weierstrass on `[0, π]`**: the cosine polynomials are dense in `C([0, π], ℝ)`, because
they form a subalgebra containing the constants, and `cos` is injective on `[0, π]`. -/
theorem dense_span_cosMap :
    Dense ((span ℝ (Set.range cosMap) : Submodule ℝ C(Icc (0 : ℝ) π, ℝ)) :
      Set C(Icc (0 : ℝ) π, ℝ)) := by
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints cosSubalgebra
    separatesPoints_cosSubalgebra
  have h2 : closure ((cosSubalgebra : Subalgebra ℝ C(Icc (0 : ℝ) π, ℝ)) :
      Set C(Icc (0 : ℝ) π, ℝ)) = Set.univ := by
    rw [← Subalgebra.topologicalClosure_coe, h]
    rfl
  rw [dense_iff_closure_eq]
  exact h2

/-- **The half-range cosine system is complete in `L²(0, π)`**: a function orthogonal to every
member is orthogonal to every continuous function, hence to everything, hence zero. -/
theorem orthogonal_span_cosLp_eq_bot : (span ℝ (Set.range cosLp))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  set T : C(Icc (0 : ℝ) π, ℝ) →L[ℝ] Lp ℝ 2 halfRangeMeasure :=
    ContinuousMap.toLp 2 halfRangeMeasure ℝ with hT
  set L : C(Icc (0 : ℝ) π, ℝ) →L[ℝ] ℝ := (innerSL ℝ f).comp T with hLdef
  have hgen : ∀ k : ℕ, L (cosMap k) = 0 := by
    intro k
    have h1 : inner ℝ f (cosLp k) = 0 :=
      (Submodule.mem_orthogonal' _ _).mp hf _ (subset_span ⟨k, rfl⟩)
    rw [cosLp_eq_smul, real_inner_smul_right] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (cosNorm_ne_zero k)
    · exact h
  have hspan : Set.EqOn (L : C(Icc (0 : ℝ) π, ℝ) → ℝ) (fun _ => 0)
      ((span ℝ (Set.range cosMap) : Submodule ℝ C(Icc (0 : ℝ) π, ℝ)) :
        Set C(Icc (0 : ℝ) π, ℝ)) := by
    intro y hy
    have hle : span ℝ (Set.range cosMap) ≤ LinearMap.ker (L : C(Icc (0 : ℝ) π, ℝ) →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hgen k
    exact hle hy
  have hL0 : ∀ y, L y = 0 :=
    congrFun (Continuous.ext_on dense_span_cosMap L.continuous continuous_const hspan)
  have hdense : DenseRange (T : C(Icc (0 : ℝ) π, ℝ) → Lp ℝ 2 halfRangeMeasure) :=
    ContinuousMap.toLp_denseRange ℝ halfRangeMeasure ℝ (by norm_num)
  have hall : ∀ z : Lp ℝ 2 halfRangeMeasure, inner ℝ f z = 0 := by
    refine congrFun (Continuous.ext_on hdense (innerSL ℝ f).continuous continuous_const ?_)
    rintro _ ⟨y, rfl⟩
    exact hL0 y
  exact inner_self_eq_zero.mp (hall f)

/-- **The half-range cosine system is a Hilbert basis of `L²(0, π)`.** -/
noncomputable def cosBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 halfRangeMeasure) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_cosLp orthogonal_span_cosLp_eq_bot

/-- The Hilbert basis `cosBasis` is the half-range cosine system. -/
@[simp]
theorem coe_cosBasis : ⇑cosBasis = cosLp := HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The span of the half-range cosine system is dense in `L²(0, π)`. -/
theorem dense_span_cosLp : (span ℝ (Set.range cosLp)).topologicalClosure = ⊤ := by
  have h := cosBasis.dense_span
  rwa [coe_cosBasis] at h

/-- The constant member of the system is `1/√π`. -/
theorem cosFun_zero_apply (x : Icc (0 : ℝ) π) : cosFun 0 x = 1 / √π := by
  simp [cosFun, cosMap, cosNorm]

/-- The member of frequency `k ≥ 1` is `√(2/π) cos (k x)`. -/
theorem cosFun_apply_of_ne_zero {k : ℕ} (hk : k ≠ 0) (x : Icc (0 : ℝ) π) :
    cosFun k x = √(2 / π) * Real.cos (k * (x : ℝ)) := by
  simp [cosFun, cosMap, cosNorm_of_ne_zero hk]
