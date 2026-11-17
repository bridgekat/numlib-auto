/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Cauchy

/-!
# Resolvent integrals along complex paths

The integral of the resolvent around a closed curve is a sum of the spectral idempotents
weighted by the winding numbers. The proof integrates the partial fractions of the
resolvent. Each pole of order at least two has an elementary antiderivative on the
complement of the pole.

## Main definitions

* `Path.IsPiecewiseC1` describes concatenations of continuously differentiable paths.
* `complexLineIntegral` is the complex integral along a path of a Banach-space-valued function.
* `complexPathIndex` is the integral of the simple pole divided by $2\pi i$.

## Main results

* `complexLineIntegral_resolvent` evaluates the normalized resolvent integral for a piecewise
  $C^1$ loop.
-/

open Complex Polynomial Set
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
    complexLineIntegral γ f = ∫ t in 0..1, derivWithin γ.extend unitInterval t • f (γ.extend t) := by
  rw [complexLineIntegral, curveIntegral_def, curveIntegralFun_complexForm]

private theorem intervalIntegrable_inversePole_of_contDiffOn {a b w : ℂ} {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend unitInterval) (hw : ∀ t ∈ unitInterval, γ.extend t ≠ w)
    (j : ℕ) (u : V) :
    IntervalIntegrable (fun t => (derivWithin γ.extend unitInterval t * ((γ.extend t - w) ^ j)⁻¹) • u)
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

end Resolvent
