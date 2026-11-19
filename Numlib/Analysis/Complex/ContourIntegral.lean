/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Analytic.IsolatedZeros
import Numlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Cauchy

/-!
# Resolvent integrals along complex paths

The integral of the resolvent around a piecewise continuously differentiable closed curve is
a sum of the spectral idempotents weighted by winding numbers. For a holomorphic scalar weight,
the coefficients of the higher-order poles contribute Taylor coefficients. This yields a
path-integral representation of the primary functional calculus.

## Main definitions

* `Path.IsPiecewiseC1` describes concatenations of continuously differentiable paths.
* `complexLineIntegral` is the complex integral along a path of a Banach-space-valued function.
* `complexPathIndex` is the integral of the simple pole divided by $2\pi i$.

## Main results

* `complexLineIntegral_resolvent` evaluates the normalized resolvent integral for a piecewise
  $C^1$ loop.
* `normalized_complexLineIntegral_div_sub_pow` is Cauchy's formula for derivatives along
  piecewise $C^1$ loops in open convex sets.
* `pfc_eq_sum_complexLineIntegral` recovers the primary functional calculus from finitely many
  such loops with total winding number one at every spectral value.
-/

open Complex Polynomial Set MeasureTheory
open scoped Real Interval

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

private noncomputable def complexForm (f : ℂ → V) (z : ℂ) : ℂ →L[ℂ] V :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (f z)

/-- A piecewise continuously differentiable path is a finite concatenation of paths with
a continuous derivative on their closed parameter intervals. -/
inductive Path.IsPiecewiseC1 : {a b : ℂ} → Path a b → Prop
  | single {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend unitInterval) :
      Path.IsPiecewiseC1 γ
  | trans {a b c : ℂ} {γ₁ : Path a b} {γ₂ : Path b c}
      (h₁ : Path.IsPiecewiseC1 γ₁) (h₂ : Path.IsPiecewiseC1 γ₂) :
      Path.IsPiecewiseC1 (γ₁.trans γ₂)

/-- The complex line integral of $f$ along $\gamma$, integrating $f(\gamma(t))\,d\gamma(t)$. -/
noncomputable def complexLineIntegral {a b : ℂ} (γ : Path a b) (f : ℂ → V) : V :=
  curveIntegral (complexForm f) γ

/-- The winding integral of $\gamma$ about $w$, divided by $2\pi i$. -/
noncomputable def complexPathIndex {a : ℂ} (γ : Path a a) (w : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * complexLineIntegral γ (fun z => (z - w)⁻¹)

private theorem curveIntegralFun_complexForm {a b : ℂ} (γ : Path a b) (f : ℂ → V) :
    curveIntegralFun (complexForm f) γ =
      fun t => derivWithin γ.extend unitInterval t • f (γ.extend t) := by
  funext t
  simp only [curveIntegralFun_def, complexForm, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]

private theorem complexLineIntegral_eq_interval {a b : ℂ} (γ : Path a b) (f : ℂ → V) :
    complexLineIntegral γ f =
      ∫ t in 0..1, derivWithin γ.extend unitInterval t • f (γ.extend t) := by
  rw [complexLineIntegral, curveIntegral_def, curveIntegralFun_complexForm]

/-- The parameter integrand of a continuous function along a piecewise $C^1$ path is integrable. -/
theorem complexLineIntegral_intervalIntegrable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseC1)
    {f : ℂ → X} (hf : ContinuousOn f (Set.range γ)) :
    IntervalIntegrable (fun t => derivWithin γ.extend unitInterval t • f (γ.extend t))
      volume 0 1 := by
  let ω (z : ℂ) := (ContinuousLinearMap.id ℂ ℂ).smulRight (f z)
  have hEq {a b : ℂ} (γ' : Path a b) : curveIntegralFun ω γ' =
      fun t => derivWithin γ'.extend unitInterval t • f (γ'.extend t) := by
    funext t
    rw [curveIntegralFun_def]
    rfl
  have hCI : CurveIntegrable ω γ := by
    revert hf
    induction hγ with
    | single γ hγ =>
      intro hf
      rw [CurveIntegrable, hEq]
      refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
      apply (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).smul
      exact hf.comp hγ.continuousOn (fun t ht => ⟨⟨t, ht⟩, (Path.extend_apply γ ht).symm⟩)
    | @trans a b c γ₁ γ₂ _ _ ih₁ ih₂ =>
      intro hf
      rw [Path.trans_range] at hf
      exact (ih₁ (hf.mono Set.subset_union_left)).trans (ih₂ (hf.mono Set.subset_union_right))
  rw [CurveIntegrable, hEq] at hCI
  exact hCI

/-- The complex line integral of a finite sum is the sum of the integrals. -/
theorem complexLineIntegral_finset_sum {X ι : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseC1)
    (S : Finset ι) (f : ι → ℂ → X) (hf : ∀ i ∈ S, ContinuousOn (f i) (Set.range γ)) :
    complexLineIntegral γ (fun z => ∑ i ∈ S, f i z) = ∑ i ∈ S, complexLineIntegral γ (f i) := by
  simp only [complexLineIntegral_eq_interval, Finset.smul_sum]
  exact intervalIntegral.integral_finsetSum
    (fun i hi => complexLineIntegral_intervalIntegrable hγ (hf i hi))

/-- A constant vector can be taken outside a scalar-valued complex line integral. -/
theorem complexLineIntegral_smul_const {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {a b : ℂ} (γ : Path a b) (f : ℂ → ℂ) (v : X) :
    complexLineIntegral γ (fun z => f z • v) = complexLineIntegral γ f • v := by
  simp only [complexLineIntegral_eq_interval, smul_smul,
    intervalIntegral.integral_smul_const, smul_eq_mul]

/-- The complex line integral depends only on the integrand along the path. -/
theorem complexLineIntegral_congr_on_path {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {a b : ℂ} (γ : Path a b) {f g : ℂ → X}
    (h : Set.EqOn f g (Set.range γ)) : complexLineIntegral γ f = complexLineIntegral γ g := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  exact congrArg (derivWithin γ.extend unitInterval t • ·)
    (h ⟨⟨t, ht⟩, (Path.extend_apply γ ht).symm⟩)

/-- A constant scalar can be taken outside a complex line integral. -/
theorem complexLineIntegral_scalar_mul {a b : ℂ} (γ : Path a b) (c : ℂ)
    (f : ℂ → ℂ) :
    complexLineIntegral γ (fun z => c * f z) = c * complexLineIntegral γ f := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval]
  simp only [smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  rw [intervalIntegral.integral_const_mul]

/-- The line integral of a difference equals the difference of the integrals. -/
theorem complexLineIntegral_sub_of_continuousOn {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsPiecewiseC1) {f g : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ))
    (hg : ContinuousOn g (Set.range γ)) :
    complexLineIntegral γ (fun z => f z - g z) =
      complexLineIntegral γ f - complexLineIntegral γ g := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval,
    complexLineIntegral_eq_interval]
  simp_rw [smul_sub]
  exact intervalIntegral.integral_sub (complexLineIntegral_intervalIntegrable hγ hf)
    (complexLineIntegral_intervalIntegrable hγ hg)

/-- The complex line integral of a derivative is the difference of endpoint values. -/
theorem complexLineIntegral_derivative {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsPiecewiseC1) {f F : ℂ → ℂ}
    (hF : ∀ z ∈ Set.range γ, HasDerivAt F (f z) z)
    (hf : ContinuousOn f (Set.range γ)) :
    complexLineIntegral γ f = F b - F a := by
  induction hγ with
  | single γ hγ =>
    rw [complexLineIntegral_eq_interval]
    have hm (t : ℝ) (ht : t ∈ unitInterval) : γ.extend t ∈ Set.range γ :=
      ⟨⟨t, ht⟩, (Path.extend_apply γ ht).symm⟩
    have hFc : ContinuousOn F (Set.range γ) :=
      fun z hz => (hF z hz).continuousAt.continuousWithinAt
    have hc : ContinuousOn (F ∘ γ.extend) unitInterval := hFc.comp hγ.continuousOn hm
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc
      (fun t ht => by
        have hn : unitInterval ∈ nhds t := Icc_mem_nhds ht.1 ht.2
        have ht' : t ∈ unitInterval := Ioo_subset_Icc_self ht
        have hcurve := ((hγ.differentiableOn (by norm_num) t ht').differentiableAt hn).hasDerivAt
        have h := (hF (γ.extend t) (hm t ht')).scomp t hcurve
        simpa only [derivWithin_of_mem_nhds hn] using h)
      (complexLineIntegral_intervalIntegrable (Path.IsPiecewiseC1.single γ hγ) hf)
    simpa only [Function.comp_apply, Path.extend_one, Path.extend_zero] using hh
  | @trans a b c γ₁ γ₂ hγ₁ hγ₂ ih₁ ih₂ =>
    rw [Path.trans_range] at hF hf
    let ω (z : ℂ) := (ContinuousLinearMap.id ℂ ℂ).smulRight (f z)
    have hint {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseC1)
        (hf : ContinuousOn f (Set.range γ)) : CurveIntegrable ω γ := by
      have he : curveIntegralFun ω γ =
          fun t => derivWithin γ.extend unitInterval t • f (γ.extend t) := by
        funext t
        rw [curveIntegralFun_def]
        rfl
      rw [CurveIntegrable, he]
      exact complexLineIntegral_intervalIntegrable hγ hf
    have hf₁ := hf.mono Set.subset_union_left
    have hf₂ := hf.mono Set.subset_union_right
    have he : complexLineIntegral (γ₁.trans γ₂) f =
        complexLineIntegral γ₁ f + complexLineIntegral γ₂ f :=
      curveIntegral_trans (hint hγ₁ hf₁) (hint hγ₂ hf₂)
    rw [he, ih₁ (fun z hz => hF z (Or.inl hz)) hf₁,
      ih₂ (fun z hz => hF z (Or.inr hz)) hf₂]
    abel

/-- The line integral of a sum equals the sum of the integrals. -/
theorem complexLineIntegral_add_of_continuousOn {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsPiecewiseC1) {f g : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ))
    (hg : ContinuousOn g (Set.range γ)) :
    complexLineIntegral γ (fun z => f z + g z) =
      complexLineIntegral γ f + complexLineIntegral γ g := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval,
    complexLineIntegral_eq_interval]
  simp_rw [smul_add]
  exact intervalIntegral.integral_add (complexLineIntegral_intervalIntegrable hγ hf)
    (complexLineIntegral_intervalIntegrable hγ hg)

/-- A holomorphic function on an open convex set integrates to zero
along any piecewise $C^1$ loop in that set. -/
theorem complexLineIntegral_zero_of_differentiableOn_convex {a : ℂ} {γ : Path a a}
    (hγ : γ.IsPiecewiseC1) {S : Set ℂ} (hOpen : IsOpen S) (hConvex : Convex ℝ S)
    (hRange : Set.range γ ⊆ S) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    complexLineIntegral γ f = 0 := by
  obtain ⟨F, hF⟩ := hConvex.exists_forall_hasDerivWithinAt hf
  rw [complexLineIntegral_derivative hγ
    (fun z hz => (hF z (hRange hz)).hasDerivAt (hOpen.mem_nhds (hRange hz)))
    (hf.continuousOn.mono hRange), sub_self]

/-- A continuous linear map commutes with complex line integration. -/
theorem complexLineIntegral_map {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℂ X] [NormedSpace ℂ Y]
    [CompleteSpace X] [CompleteSpace Y]
    {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseC1) {f : ℂ → X}
    (hf : ContinuousOn f (Set.range γ)) (L : X →L[ℂ] Y) :
    complexLineIntegral γ (fun z => L (f z)) = L (complexLineIntegral γ f) := by
  rw [complexLineIntegral_eq_interval, complexLineIntegral_eq_interval]
  simp_rw [← map_smul]
  exact L.intervalIntegral_comp_comm (complexLineIntegral_intervalIntegrable hγ hf)

private theorem intervalIntegrable_inversePole_of_contDiffOn {a b w : ℂ} {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend unitInterval) (hw : ∀ t ∈ unitInterval, γ.extend t ≠ w)
    (j : ℕ) (u : V) :
    IntervalIntegrable
      (fun t => (derivWithin γ.extend unitInterval t * ((γ.extend t - w) ^ j)⁻¹) • u)
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  refine ((hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).mul ?_).smul
    continuousOn_const
  exact (((hγ.continuousOn.sub continuousOn_const).pow j).inv₀ fun t ht =>
    pow_ne_zero j (sub_ne_zero.mpr (hw t ht)))

private theorem avoid_of_avoid_trans {a b c w : ℂ} {γ₁ : Path a b} {γ₂ : Path b c}
    (h : ∀ t : unitInterval, (γ₁.trans γ₂) t ≠ w) :
    (∀ t : unitInterval, γ₁ t ≠ w) ∧ ∀ t : unitInterval, γ₂ t ≠ w := by
  have h' : w ∉ Set.range (γ₁.trans γ₂) := fun ⟨t, ht⟩ => h t ht
  rw [Path.trans_range] at h'
  exact ⟨fun t ht => h' (Or.inl ⟨t, ht⟩), fun t ht => h' (Or.inr ⟨t, ht⟩)⟩

private theorem curveIntegrable_inversePole {a b w : ℂ} {γ : Path a b}
    (hγ : γ.IsPiecewiseC1) (hw : ∀ t : unitInterval, γ t ≠ w)
    (j : ℕ) (u : V) :
    CurveIntegrable (complexForm fun z => ((z - w) ^ j)⁻¹ • u) γ := by
  induction hγ with
  | single γ hγ =>
    have havoid : ∀ t ∈ unitInterval, γ.extend t ≠ w := by
      intro t ht
      rw [Path.extend_apply γ ht]
      exact hw _
    rw [CurveIntegrable, curveIntegralFun_complexForm]
    simpa only [smul_smul] using intervalIntegrable_inversePole_of_contDiffOn hγ havoid j u
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ (avoid_of_avoid_trans hw).1).trans (ih₂ (avoid_of_avoid_trans hw).2)

private noncomputable def inversePolePrimitive (w : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  ((-(j : ℤ)) : ℂ)⁻¹ * (z - w) ^ (-(j : ℤ))

private theorem complexLineIntegral_inversePole_succ_of_contDiffOn {a b w : ℂ} {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend unitInterval) (hw : ∀ t ∈ unitInterval, γ.extend t ≠ w)
    {j : ℕ} (hj : 0 < j) :
    complexLineIntegral γ (fun z => ((z - w) ^ (j + 1))⁻¹) =
      inversePolePrimitive w j b - inversePolePrimitive w j a := by
  let m : ℤ := -(j : ℤ)
  let F : ℂ → ℂ := fun z => (m : ℂ)⁻¹ * (z - w) ^ m
  have hm : (m : ℂ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have hd (z : ℂ) (hz : z ≠ w) :
      HasDerivAt F (((z - w) ^ (j + 1))⁻¹) z := by
    have h := ((hasDerivAt_zpow m (z - w) (Or.inl (sub_ne_zero.mpr hz))).comp z
        ((hasDerivAt_id z).sub_const w)).const_mul ((m : ℂ)⁻¹)
    change HasDerivAt F ((m : ℂ)⁻¹ * (((m : ℂ) * (z - w) ^ (m - 1)) * 1)) z at h
    have he : m - 1 = -((j + 1 : ℕ) : ℤ) := by omega
    rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hm, one_mul, he, zpow_neg, zpow_natCast] at h
  rw [complexLineIntegral_eq_interval]
  have hFc : ContinuousOn F {w}ᶜ :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (F ∘ γ.extend) unitInterval :=
    hFc.comp hγ.continuousOn fun t ht => hw t ht
  have hi := intervalIntegrable_inversePole_of_contDiffOn hγ hw (j + 1) (1 : ℂ)
  simp only [smul_eq_mul, mul_one] at hi
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun t ht => by
      have hnhds : unitInterval ∈ nhds t := Icc_mem_nhds ht.1 ht.2
      have ht' : t ∈ unitInterval := Ioo_subset_Icc_self ht
      have hg := ((hγ.differentiableOn (by norm_num) t ht').differentiableAt hnhds).hasDerivAt
      have hg' := (hd (γ.extend t) (hw t ht')).scomp t hg
      simpa only [derivWithin_of_mem_nhds hnhds, smul_eq_mul] using hg')
    hi
  simpa only [smul_eq_mul, Function.comp_apply, Path.extend_one, Path.extend_zero,
    F, m, inversePolePrimitive, Int.cast_neg] using hF

private theorem complexLineIntegral_inversePole_succ {a b w : ℂ} {γ : Path a b}
    (hγ : γ.IsPiecewiseC1) (hw : ∀ t : unitInterval, γ t ≠ w) {j : ℕ} (hj : 0 < j) :
    complexLineIntegral γ (fun z => ((z - w) ^ (j + 1))⁻¹) =
      inversePolePrimitive w j b - inversePolePrimitive w j a := by
  induction hγ with
  | single γ hγ =>
    apply complexLineIntegral_inversePole_succ_of_contDiffOn hγ _ hj
    intro t ht
    rw [Path.extend_apply γ ht]
    exact hw _
  | @trans a b c γ₁ γ₂ h₁ h₂ ih₁ ih₂ =>
    have ⟨hw₁, hw₂⟩ := avoid_of_avoid_trans hw
    have hint₁ := curveIntegrable_inversePole h₁ hw₁ (j + 1) (1 : ℂ)
    have hint₂ := curveIntegrable_inversePole h₂ hw₂ (j + 1) (1 : ℂ)
    simp only [smul_eq_mul, mul_one] at hint₁ hint₂
    rw [complexLineIntegral, curveIntegral_trans hint₁ hint₂]
    change complexLineIntegral γ₁ _ + complexLineIntegral γ₂ _ = _
    rw [ih₁ hw₁, ih₂ hw₂]
    abel

/-- A pole of order at least two has zero integral along a closed path avoiding its pole. -/
theorem complexLineIntegral_inversePole_succ_eq_zero {a w : ℂ} (γ : Path a a)
    (hγ : γ.IsPiecewiseC1) (hw : w ∉ Set.range γ) {j : ℕ} (hj : 0 < j) :
    complexLineIntegral γ (fun z => ((z - w) ^ (j + 1))⁻¹) = 0 := by
  rw [complexLineIntegral_inversePole_succ hγ (fun t ht => hw ⟨t, ht⟩) hj, sub_self]

private theorem iterate_dslope_eq_taylorJet {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (j : ℕ) :
    (Function.swap dslope w)^[j] f w = Hermite.taylorJet f w j := by
  obtain ⟨p, hp⟩ := hf
  have hds := hp.has_fpower_series_iterate_dslope_fslope j
  obtain ⟨r, hr⟩ := hp
  obtain ⟨q, hq, hcoeff⟩ := hr.exists_hasFPowerSeriesOnBall_iteratedDeriv j
  have hq₀ : q.coeff 0 = iteratedDeriv j f w := hq.coeff_zero 1
  rw [hcoeff, Nat.zero_add, Nat.descFactorial_self] at hq₀
  rw [← hds.coeff_zero 1, ← FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.coeff_iterate_fslope, Nat.zero_add, Hermite.taylorJet, ← hq₀]
  rw [mul_comm, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr j.factorial_ne_zero)]

private theorem continuousOn_inversePole {a b w : ℂ} {γ : Path a b}
    (hAvoid : w ∉ Set.range γ) (j : ℕ) :
    ContinuousOn (fun z => ((z - w) ^ j)⁻¹) (Set.range γ) :=
  ((continuousOn_id.sub continuousOn_const).pow j).inv₀ fun z hz =>
    pow_ne_zero j (sub_ne_zero.mpr (fun (he : z = w) => hAvoid (he ▸ hz)))

private theorem complexLineIntegral_dslope {a w : ℂ} (γ : Path a a)
    (hγ : γ.IsPiecewiseC1) (hAvoid : w ∉ Set.range γ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range γ)) (j : ℕ) :
    complexLineIntegral γ (fun z => f z / (z - w) ^ (j + 2)) =
      complexLineIntegral γ (fun z => dslope f w z / (z - w) ^ (j + 1)) := by
  have hDecompose : Set.EqOn (fun z => f z / (z - w) ^ (j + 2))
      (fun z => dslope f w z / (z - w) ^ (j + 1) + f w * ((z - w) ^ (j + 2))⁻¹)
      (Set.range γ) := by
    intro z hz
    have hne : z ≠ w := fun he => hAvoid (he ▸ hz)
    have hsub : z - w ≠ 0 := sub_ne_zero.mpr hne
    simp only [dslope_of_ne _ hne, slope_def_field, pow_succ _ (j + 1)]
    field_simp
    ring
  have hInv := continuousOn_inversePole hAvoid (j + 2)
  have hD : ContinuousOn (dslope f w) (Set.range γ) := by
    intro z hz
    exact (continuousWithinAt_dslope_of_ne (fun (he : z = w) => hAvoid (he ▸ hz))).mpr (hf z hz)
  have hLeft : ContinuousOn (fun z => dslope f w z / (z - w) ^ (j + 1)) (Set.range γ) := by
    simp only [div_eq_mul_inv]
    exact hD.mul (continuousOn_inversePole hAvoid (j + 1))
  have hRight : ContinuousOn (fun z => f w * ((z - w) ^ (j + 2))⁻¹) (Set.range γ) :=
    continuousOn_const.mul hInv
  rw [complexLineIntegral_congr_on_path γ hDecompose,
    complexLineIntegral_add_of_continuousOn hγ hLeft hRight,
    complexLineIntegral_scalar_mul,
    complexLineIntegral_inversePole_succ_eq_zero γ hγ hAvoid (Nat.succ_pos j), mul_zero, add_zero]

private theorem complexLineIntegral_eq_iterate_dslope {a w : ℂ} (γ : Path a a)
    (hγ : γ.IsPiecewiseC1) (hAvoid : w ∉ Set.range γ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range γ)) (j : ℕ) :
    complexLineIntegral γ (fun z => f z / (z - w) ^ (j + 1)) =
      complexLineIntegral γ (fun z => ((Function.swap dslope w)^[j] f) z / (z - w)) := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    rw [complexLineIntegral_dslope γ hγ hAvoid hf, ih, Function.iterate_succ_apply]
    intro z hz
    exact (continuousWithinAt_dslope_of_ne (fun (he : z = w) => hAvoid (he ▸ hz))).mpr (hf z hz)

private theorem complexLineIntegral_simplePole_of_differentiableOn_convex
    {a w : ℂ} {S : Set ℂ} (γ : Path a a) (hγ : γ.IsPiecewiseC1)
    (hOpen : IsOpen S) (hConvex : Convex ℝ S) (hRange : Set.range γ ⊆ S) (hAvoid : w ∉ Set.range γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    complexLineIntegral γ (fun z => f z / (z - w)) =
      f w * complexLineIntegral γ (fun z => (z - w)⁻¹) := by
  have hDiff : DifferentiableOn ℂ (dslope f w) S := by
    intro z hz
    exact ((hf.analyticAt (hOpen.mem_nhds hz)).dslope w
      ).differentiableAt.differentiableWithinAt
  have hEq : Set.EqOn (fun z => f z / (z - w))
      (fun z => dslope f w z + f w * (z - w)⁻¹) (Set.range γ) := by
    intro z hz
    have hne : z ≠ w := fun he => hAvoid (he ▸ hz)
    simp only [dslope_of_ne f hne, slope_def_field]
    ring
  have hPole : ContinuousOn (fun z => f w * (z - w)⁻¹) (Set.range γ) := by
    have hInv : ContinuousOn (fun z => (z - w)⁻¹) (Set.range γ) := by
      simpa only [pow_one] using continuousOn_inversePole hAvoid 1
    exact continuousOn_const.mul hInv
  rw [complexLineIntegral_congr_on_path γ hEq,
    complexLineIntegral_add_of_continuousOn hγ (hDiff.continuousOn.mono hRange) hPole,
    complexLineIntegral_zero_of_differentiableOn_convex hγ hOpen hConvex hRange hDiff, zero_add,
    complexLineIntegral_scalar_mul]

private theorem differentiableOn_iterate_dslope {S : Set ℂ} (hOpen : IsOpen S) (w : ℂ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) (j : ℕ) :
    DifferentiableOn ℂ ((Function.swap dslope w)^[j] f) S := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    intro z hz
    exact ((ih.analyticAt (hOpen.mem_nhds hz)).dslope w
      ).differentiableAt.differentiableWithinAt

/-- Cauchy's formula for derivatives along any piecewise $C^1$ loop contained in
an open convex set of holomorphy. The normalized integral at a point off the loop is its winding number times the
corresponding Taylor coefficient. Points outside the set contribute zero. -/
theorem normalized_complexLineIntegral_div_sub_pow {a w : ℂ} {S : Set ℂ} (γ : Path a a)
    (hγ : γ.IsPiecewiseC1)
    (hOpen : IsOpen S) (hConvex : Convex ℝ S) (hRange : Set.range γ ⊆ S)
    (hAvoid : w ∉ Set.range γ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S)
    (j : ℕ) :
    (2 * π * I)⁻¹ * complexLineIntegral γ (fun z => f z / (z - w) ^ (j + 1)) =
      complexPathIndex γ w * Hermite.taylorJet f w j := by
  by_cases hw : w ∈ S
  · rw [complexLineIntegral_eq_iterate_dslope γ hγ hAvoid (hf.continuousOn.mono hRange),
      complexLineIntegral_simplePole_of_differentiableOn_convex γ hγ hOpen hConvex hRange hAvoid
        (differentiableOn_iterate_dslope hOpen w hf j),
      iterate_dslope_eq_taylorJet (hf.analyticAt (hOpen.mem_nhds hw)) j,
      complexPathIndex]
    ring
  · have hne (z : ℂ) (hz : z ∈ S) : z - w ≠ 0 :=
      sub_ne_zero.mpr (fun he => hw (he ▸ hz))
    have hsub : DifferentiableOn ℂ (fun z => z - w) S :=
      differentiableOn_id.sub_const w
    have hfDiv : DifferentiableOn ℂ (fun z => f z / (z - w) ^ (j + 1)) S :=
      hf.div (hsub.pow (j + 1)) (fun z hz => pow_ne_zero _ (hne z hz))
    have hInv : DifferentiableOn ℂ (fun z => (z - w)⁻¹) S := hsub.inv hne
    rw [complexLineIntegral_zero_of_differentiableOn_convex hγ hOpen hConvex hRange hfDiv,
      complexPathIndex,
      complexLineIntegral_zero_of_differentiableOn_convex hγ hOpen hConvex hRange hInv]
    simp

/-- Cauchy's formula for the simple pole on a piecewise $C^1$ loop in a disk of holomorphy. -/
theorem normalized_complexLineIntegral_cauchy_disk {a w c : ℂ} (γ : Path a a)
    (hγ : γ.IsPiecewiseC1) {R : ℝ} (hDisk : Set.range γ ⊆ Metric.ball c R)
    (hAvoid : w ∉ Set.range γ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball c R)) :
    (2 * π * I)⁻¹ * complexLineIntegral γ (fun z => (z - w)⁻¹ * f z) =
      complexPathIndex γ w * f w := by
  simpa only [zero_add, pow_one, Hermite.taylorJet_zero, div_eq_inv_mul] using
    normalized_complexLineIntegral_div_sub_pow γ hγ Metric.isOpen_ball
      (convex_ball _ _) hDisk hAvoid hf 0

section Resolvent

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- The normalized complex line integral of a resolvent around a piecewise $C^1$ loop avoiding the
spectrum is the sum of the spectral idempotents multiplied by the winding integrals
of their spectral points. The resolvent uses the ring inverse, and the operator is assumed
integral over $\mathbb C$. -/
theorem complexLineIntegral_resolvent {a : B} (ha : IsIntegral ℂ a) {z₀ : ℂ}
    (γ : Path z₀ z₀) (hγ : γ.IsPiecewiseC1)
    (havoid : ∀ t ∈ unitInterval, γ.extend t ∉ (minpoly ℂ a).roots) :
    (2 * π * I)⁻¹ • complexLineIntegral γ (fun z => Ring.inverse (algebraMap ℂ B z - a)) =
      ∑ w ∈ (minpoly ℂ a).roots.toFinset, complexPathIndex γ w • spectralIdempotent a w := by
  classical
  let R := (minpoly ℂ a).roots.toFinset
  let X := fun w : ℂ => fun j : ℕ => (a - algebraMap ℂ B w) ^ j * spectralIdempotent a w
  let F := fun w j t => derivWithin γ.extend unitInterval t * ((γ.extend t - w) ^ (j + 1))⁻¹
  have hs := IsAlgClosed.splits (minpoly ℂ a)
  have hw : ∀ w ∈ R, ∀ t ∈ unitInterval, γ.extend t ≠ w := by
    intro w hw t ht h
    exact havoid t ht (h.symm ▸ Multiset.mem_toFinset.1 hw)
  have havPath : ∀ w ∈ R, ∀ t : unitInterval, γ t ≠ w := by
    intro w h t
    have ht := hw w h t.1 t.2
    rwa [Path.extend_apply γ t.2] at ht
  have hdecomp :
      (∫ t in (0 : ℝ)..1, derivWithin γ.extend unitInterval t • Ring.inverse
        (algebraMap ℂ B (γ.extend t) - a)) =
        ∫ t in (0 : ℝ)..1, ∑ w ∈ R, ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w),
          F w j t • X w j := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    dsimp only
    rw [inverse_sub_eq_sum_spectralIdempotent ha hs (havoid t ht)]
    simp only [Finset.smul_sum, smul_smul, F, X, R]
  have hint (w : ℂ) (hw' : w ∈ R) (j : ℕ) :
      IntervalIntegrable (fun t => F w j t • X w j) MeasureTheory.volume 0 1 := by
    have h := curveIntegrable_inversePole hγ (havPath w hw') (j + 1) (X w j)
    simpa only [CurveIntegrable, curveIntegralFun_complexForm, smul_smul, F] using h
  let G := fun w t => ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w), F w j t • X w j
  have hG (w : ℂ) (hw' : w ∈ R) : IntervalIntegrable (G w) MeasureTheory.volume 0 1 := by
    have heq : G w = ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w),
        fun t => F w j t • X w j := by
      funext t
      simp only [G, Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum _ (fun j _ => hint w hw' j)
  rw [complexLineIntegral_eq_interval, hdecomp]
  change (2 * π * I)⁻¹ • (∫ t in (0 : ℝ)..1, ∑ w ∈ R, G w t) = _
  rw [intervalIntegral.integral_finsetSum hG, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w hw' => ?_
  dsimp only [G]
  rw [intervalIntegral.integral_finsetSum (fun j _ => hint w hw' j)]
  simp only [intervalIntegral.integral_smul_const]
  rw [Finset.sum_eq_single 0]
  · simp only [F, X, zero_add, pow_one, pow_zero, one_mul, smul_smul]
    rw [complexPathIndex, complexLineIntegral_eq_interval]
    rfl
  · intro j _ hj
    have hz := complexLineIntegral_inversePole_succ hγ (havPath w hw') (Nat.pos_of_ne_zero hj)
    rw [sub_self] at hz
    rw [complexLineIntegral_eq_interval] at hz
    change (∫ t in (0 : ℝ)..1, F w j t) = 0 at hz
    rw [hz, zero_smul]
  · intro h0
    have hm := Multiset.mem_toFinset.mp hw'
    exact (h0 (Finset.mem_range.mpr
      ((rootMultiplicity_pos (ne_zero_of_mem_roots hm)).mpr (isRoot_of_mem_roots hm)))).elim

/-- The normalized weighted resolvent integral on a piecewise $C^1$ loop in an open convex set of
holomorphy has a primary expansion. The coefficient at each spectral value is its Taylor
coefficient multiplied by its winding number. -/
theorem complexLineIntegral_smul_resolvent {a : B} (ha : IsIntegral ℂ a) {p : ℂ} {S : Set ℂ}
    (γ : Path p p) (hγ : γ.IsPiecewiseC1)
    (hOpen : IsOpen S) (hConvex : Convex ℝ S) (hRange : Set.range γ ⊆ S)
    (hAvoid : ∀ w ∈ (minpoly ℂ a).roots.toFinset, w ∉ Set.range γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f S) :
    (2 * π * I)⁻¹ • complexLineIntegral γ (fun z =>
      f z • Ring.inverse (algebraMap ℂ B z - a)) =
      ∑ w ∈ (minpoly ℂ a).roots.toFinset, ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w),
        (complexPathIndex γ w * Hermite.taylorJet f w j) •
          ((a - algebraMap ℂ B w) ^ j * spectralIdempotent a w) := by
  let X (w : ℂ) (j : ℕ) := (a - algebraMap ℂ B w) ^ j * spectralIdempotent a w
  let F (w : ℂ) (j : ℕ) (z : ℂ) := f z / (z - w) ^ (j + 1)
  let terms (w : ℂ) (z : ℂ) :=
    ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity w), F w j z • X w j
  have hc (w : ℂ) (hw : w ∈ (minpoly ℂ a).roots.toFinset) (j : ℕ) :
      ContinuousOn (F w j) (Set.range γ) := by
    simp only [F, div_eq_mul_inv]
    exact (hf.continuousOn.mono hRange).mul (continuousOn_inversePole (hAvoid w hw) (j + 1))
  have hEq : Set.EqOn (fun z => f z • Ring.inverse (algebraMap ℂ B z - a))
      (fun z => ∑ w ∈ (minpoly ℂ a).roots.toFinset, terms w z) (Set.range γ) := by
    intro z hz
    have hroot : z ∉ (minpoly ℂ a).roots := fun h => hAvoid z (Multiset.mem_toFinset.mpr h) hz
    simp only [inverse_sub_eq_sum_spectralIdempotent ha (IsAlgClosed.splits _) hroot,
      Finset.smul_sum, smul_smul, F, X, terms, div_eq_mul_inv]
  have hTerms (w : ℂ) (hw : w ∈ (minpoly ℂ a).roots.toFinset) :
      ContinuousOn (terms w) (Set.range γ) :=
    continuousOn_finsetSum _ fun j _ => (hc w hw j).smul continuousOn_const
  rw [complexLineIntegral_congr_on_path γ hEq,
    complexLineIntegral_finset_sum hγ _ terms hTerms, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  unfold terms
  rw [complexLineIntegral_finset_sum hγ _ (fun j z => F w j z • X w j)
    (fun j _ => (hc w hw j).smul continuousOn_const), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [complexLineIntegral_smul_const, smul_smul]
  exact congrArg (· • X w j)
    (normalized_complexLineIntegral_div_sub_pow γ hγ hOpen hConvex hRange (hAvoid w hw) hf j)

/-- A finite family of piecewise $C^1$ loops recovers the primary functional calculus when each
loop lies in an open convex set of holomorphy. The total winding number is one
at every spectral value. -/
theorem pfc_eq_sum_complexLineIntegral {a : B} (ha : IsIntegral ℂ a) {ι : Type*} [Fintype ι]
    {p : ι → ℂ} (γ : (i : ι) → Path (p i) (p i)) (hγ : ∀ i, (γ i).IsPiecewiseC1)
    (S : ι → Set ℂ) (hOpen : ∀ i, IsOpen (S i)) (hConvex : ∀ i, Convex ℝ (S i))
    (hRange : ∀ i, Set.range (γ i) ⊆ S i)
    (hAvoid : ∀ i w, w ∈ (minpoly ℂ a).roots.toFinset → w ∉ Set.range (γ i))
    {f : ℂ → ℂ} (hf : ∀ i, DifferentiableOn ℂ f (S i))
    (hIndex : ∀ w ∈ (minpoly ℂ a).roots.toFinset, ∑ i, complexPathIndex (γ i) w = 1) :
    pfc f a = ∑ i, (2 * π * I)⁻¹ • complexLineIntegral (γ i) (fun z =>
      f z • Ring.inverse (algebraMap ℂ B z - a)) := by
  rw [pfc_eq_sum_spectralIdempotent ha (IsAlgClosed.splits _) f]
  simp_rw [complexLineIntegral_smul_resolvent ha (γ _) (hγ _)
    (hOpen _) (hConvex _) (hRange _) (hAvoid _) (hf _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← Finset.sum_mul, hIndex w hw, one_mul]

end Resolvent
