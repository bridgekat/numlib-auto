import Numlib.Optimization.FlatJetChain
import Numlib.Optimization.FiniteChain
import Numlib.Optimization.CubicSharpTrace
import Numlib.Analysis.Calculus.EuclideanOneHigherDeriv

/-!
# Sharp cubic regularization traces driven by gradients

Uniform Hermite interpolation gives globally bounded C² objectives with zero Hessian
at their knots. Exact cubic model minimizers make every step successful, while the
objective gradients remain above the requested tolerance for order ε⁻³ᐟ² steps.
-/
noncomputable section
open scoped NNReal InnerProductSpace Nat
namespace Optimization.CubicGradientSharpness
open CubicRegularization RegularizedTaylorModel

/-- A zero Hessian makes the second-order Taylor model affine. -/
theorem taylorModel_of_zero_hessian {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hH : ∀ u, fderiv ℝ (fderiv ℝ f) x u u = 0) (s : E) :
    taylorModel f 2 x s = f x + fderiv ℝ f x s := by
  have hh := cubicModel_of_scalar_hessian (a := 0) (σ := 0) (by simpa using hH) s
  simpa only [cubicModel_eq, zero_div, zero_mul, add_zero] using hh

/-- With zero Hessian, gradient `-2 ‖v‖ • v` makes `v` a global minimizer of the
cubic model with parameter four. -/
theorem isMinOn_cubicModel_of_gradient {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x v : E}
    (hg : gradient f x = -(2 * ‖v‖) • v) (hd : DifferentiableAt ℝ f x)
    (hH : ∀ u, fderiv ℝ (fderiv ℝ f) x u u = 0) :
    IsMinOn (cubicModel f x 4) Set.univ v := by
  intro y _
  change cubicModel f x 4 v ≤ cubicModel f x 4 y
  rw [cubicModel_eq, cubicModel_eq, taylorModel_of_zero_hessian hH,
    taylorModel_of_zero_hessian hH, hd.hasGradientAt.hasFDerivAt.fderiv, hg]
  change f x + inner ℝ (-(2 * ‖v‖) • v) v + 4 / 6 * ‖v‖ ^ 3 ≤
    f x + inner ℝ (-(2 * ‖v‖) • v) y + 4 / 6 * ‖y‖ ^ 3
  simp only [inner_smul_left, real_inner_self_eq_norm_sq, conj_trivial]
  have hi := real_inner_le_norm v y
  have hp := mul_nonneg (sq_nonneg (‖y‖ - ‖v‖))
    (show 0 ≤ 2 * ‖y‖ + 4 * ‖v‖ by positivity)
  have him := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * ‖v‖ by positivity)
  nlinarith

/-- Uniform scalar flat chains at the cubic-gradient scale. -/
theorem exists_scalar_chain :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (ψ : ℝ → ℝ) (N : ℕ), ContDiff ℝ 2 ψ ∧
        LipschitzWith L (iteratedDeriv 2 ψ) ∧
        (∀ k ≤ N, ∀ j ≤ 2, iteratedDeriv j ψ ((k : ℝ) * Real.sqrt ε) =
          LowerBound.flatJet N (2 * ε) (Real.sqrt ε) k j) ∧
        (∀ t, |ψ t| ≤ B) ∧ 1 / ε ^ (3 / 2 : ℝ) ≤ (N : ℝ) := by
  obtain ⟨L, B, hc⟩ := LowerBound.exists_flatJet_chain 2 (by omega) 8 (by norm_num)
  refine ⟨L, B, ?_⟩
  intro ε he he1
  let h := Real.sqrt ε
  have hh : 0 < h := Real.sqrt_pos.mpr he
  have hh2 : h ^ 2 = ε := Real.sq_sqrt he.le
  have hh1 : h ≤ 1 := by nlinarith
  have hpower : h ^ 3 = ε ^ (3 / 2 : ℝ) := by
    rw [show h = ε ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow ε,
      ← Real.rpow_mul_natCast he.le]
    congr 1
    norm_num
  let N : ℕ := ⌈1 / h ^ 3⌉₊
  have hNpos : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hNlower : 1 / h ^ 3 ≤ (N : ℝ) := Nat.le_ceil _
  have hNupper : (N : ℝ) < 1 / h ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdrop : (N : ℝ) * (2 * ε) * h ≤ 8 := by
    have hm := mul_le_mul_of_nonneg_right hNupper.le (pow_nonneg hh.le 3)
    have hcanc : (1 / h ^ 3 + 1) * h ^ 3 = 1 + h ^ 3 := by field_simp
    rw [hcanc] at hm
    have hp : h ^ 3 ≤ 1 := pow_le_one₀ hh.le hh1
    nlinarith
  obtain ⟨ψ, hψ, hLip, hjet, hb⟩ := hc N hNpos (2 * ε) h (by positivity) hh
    (by nlinarith) hdrop (by linarith) (by linarith)
  refine ⟨ψ, N, hψ, hLip, hjet, ?_, ?_⟩
  · intro t
    simpa using hb 0 (by omega) t
  · rwa [hpower] at hNlower

/-- Uniform AR2 hard instances with zero Hessians, an exact stationary endpoint, and at
least `ε⁻³ᐟ²` successful iterations before their first small-gradient test. -/
theorem exists_hard_family :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)),
        ContDiff ℝ 2 f ∧ LipschitzWith L (iteratedFDeriv ℝ 2 f) ∧
        (∀ y, |f y| ≤ B) ∧ f (x 0) = 0 ∧ x 0 = 0 ∧
        SecondOrderRun sharpParameters 1 1 f x s (fun _ => 4) ∧
        (∀ k < N, ε < ‖fderiv ℝ f (x k)‖) ∧ ‖fderiv ℝ f (x N)‖ ≤ ε ∧
        (∀ k u, fderiv ℝ (fderiv ℝ f) (x k) u u = 0) ∧
        ParameterUpdates.successCount
          (fun k => sharpParameters.eta1 ≤ ratio f (x k) (s k) 4) N = N ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ (N : ℝ) := by
  obtain ⟨L, B, hc⟩ := exists_scalar_chain
  refine ⟨L, B, ?_⟩
  intro ε he he1
  obtain ⟨ψ, N, hψ, hLip, hjet, hb, hN⟩ := hc ε he he1
  let h := Real.sqrt ε
  have hh : 0 < h := Real.sqrt_pos.mpr he
  have hh2 : h ^ 2 = ε := Real.sq_sqrt he.le
  let f := EuclideanOne.lift ψ
  let v := EuclideanOne.coord.symm h
  let x := FiniteChain.point N v
  let s := FiniteChain.step N v
  have hvnorm : ‖v‖ = h := by
    change ‖EuclideanOne.coord.symm h‖ = _
    rw [EuclideanOne.coord.symm.norm_map, Real.norm_eq_abs, abs_of_pos hh]
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvnorm]; exact hh.ne')
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv ψ) := by
    simpa only [iteratedDeriv_one] using hψ.differentiable_iteratedDeriv 1 (by norm_num)
  have hvalues (k : ℕ) (hk : k ≤ N) :
      f ((k : ℝ) • v) = -(k : ℝ) * (2 * ε) * h := by
    simpa [f, v, EuclideanOne.lift, Function.comp_def, LowerBound.flatJet]
      using hjet k hk 0 (by norm_num)
  have hscalar (k : ℕ) (hk : k ≤ N) :
      deriv ψ ((k : ℝ) * h) = if k < N then -(2 * ε) else 0 := by
    simpa [LowerBound.flatJet] using hjet k hk 1 (by norm_num)
  have hgrad (k : ℕ) (hk : k ≤ N) :
      gradient f ((k : ℝ) • v) = if k < N then -(2 * ‖v‖) • v else 0 := by
    rw [EuclideanOne.gradient_eq_deriv hd]
    simp only [v, map_smul, EuclideanOne.coord.apply_symm_apply, smul_eq_mul]
    rw [hscalar k hk]
    by_cases hkn : k < N
    · simp only [hkn, ↓reduceIte]
      apply EuclideanOne.coord.injective
      simp only [EuclideanOne.coord.apply_symm_apply, map_smul, smul_eq_mul]
      change -(2 * ε) = -(2 * ‖v‖) * h
      rw [hvnorm]
      nlinarith
    · simp [hkn]
  have hHknots (k : ℕ) (hk : k ≤ N) (u : EuclideanSpace ℝ (Fin 1)) :
      fderiv ℝ (fderiv ℝ f) ((k : ℝ) • v) u u = 0 := by
    have hj : deriv (deriv ψ) ((k : ℝ) * h) = 0 := by
      simpa [iteratedDeriv_succ, iteratedDeriv_zero, LowerBound.flatJet]
        using hjet k hk 2 (by norm_num)
    have ht := EuclideanOne.fderiv_fderiv_apply hd
      (x := (k : ℝ) • v) (d₂ := 0)
      (by simpa [v, hj] using (hd' ((k : ℝ) * h)).hasDerivAt) u u
    simpa using ht
  have hH (k : ℕ) (u : EuclideanSpace ℝ (Fin 1)) :
      fderiv ℝ (fderiv ℝ f) (x k) u u = 0 :=
    hHknots (min k N) (Nat.min_le_right _ _) u
  have hga (k : ℕ) (hk : k < N) : gradient f (x k) = -(2 * ‖v‖) • v := by
    simpa [x, FiniteChain.point_of_le v hk.le, hk] using hgrad k hk.le
  have hgt (k : ℕ) (hk : N ≤ k) : gradient f (x k) = 0 := by
    simpa [x, FiniteChain.point_of_ge v hk] using hgrad N le_rfl
  have hfd : Differentiable ℝ f := (EuclideanOne.contDiff hψ).differentiable (by norm_num)
  have hmin (k : ℕ) : IsMinOn (cubicModel f (x k) 4) Set.univ (s k) := by
    by_cases hk : k < N
    · simpa [s, FiniteChain.step, hk] using
        isMinOn_cubicModel_of_gradient (hga k hk) (hfd (x k)) (hH k)
    · have hg0 : gradient f (x k) = -(2 * ‖(0 : EuclideanSpace ℝ (Fin 1))‖) • 0 := by
        simpa using hgt k (Nat.le_of_not_gt hk)
      simpa [s, FiniteChain.step, hk] using
        isMinOn_cubicModel_of_gradient hg0 (hfd (x k)) (hH k)
  have htaylor (k : ℕ) (hk : k < N) :
      taylorModel f 2 (x k) (s k) = f (x k) - 2 * ε * h := by
    rw [taylorModel_of_zero_hessian (hH k), EuclideanOne.fderiv_eq hd]
    simp [s, FiniteChain.step, hk, x, FiniteChain.point_of_le v hk.le,
      v, hscalar k hk.le]
    ring
  have hratio (k : ℕ) : ratio f (x k) (s k) 4 = 1 := by
    by_cases hk : k < N
    · have hsne : s k ≠ 0 := by simpa [s, FiniteChain.step, hk] using hv
      rw [ratio, ite_eq_right hsne]
      have hx : x k + s k = x (k + 1) := (FiniteChain.point_add_step N v k).symm
      rw [hx, taylorModel_zero, htaylor k hk]
      have hfk : f (x k) = -(k : ℝ) * (2 * ε) * h := by
        simpa [x, FiniteChain.point_of_le v hk.le] using hvalues k hk.le
      have hfk1 : f (x (k + 1)) = -(k + 1 : ℕ) * (2 * ε) * h := by
        simpa [x, FiniteChain.point_of_le v hk] using hvalues (k + 1) hk
      rw [hfk, hfk1]
      have heq : -(k : ℝ) * (2 * ε) * h - (-(k + 1 : ℕ) * (2 * ε) * h) =
          2 * ε * h := by push_cast; ring
      have heq' : -(k : ℝ) * (2 * ε) * h - (-(k : ℝ) * (2 * ε) * h - 2 * ε * h) =
          2 * ε * h := by ring
      rw [heq, heq', div_self (by positivity : 2 * ε * h ≠ 0)]
    · simp [ratio, s, FiniteChain.step, hk]
  have hrun : SecondOrderRun sharpParameters 1 1 f x s (fun _ => 4) :=
    secondOrderRun_of_global_minimizers sharpParameters (by norm_num) (by norm_num)
      (by norm_num [sharpParameters]) (EuclideanOne.contDiff hψ) hmin
      (fun k => by rw [hratio]; norm_num [sharpParameters]) (FiniteChain.point_add_step N v)
  have hcount : ParameterUpdates.successCount
      (fun k => sharpParameters.eta1 ≤ ratio f (x k) (s k) 4) N = N := by
    classical
    norm_num [ParameterUpdates.successCount, hratio, sharpParameters]
  refine ⟨f, N, x, s, EuclideanOne.contDiff hψ,
    EuclideanOne.iteratedFDeriv_lipschitz hψ hLip, ?_, ?_, ?_, hrun, ?_, ?_, hH, hcount, hN⟩
  · intro y
    exact hb _
  · simpa [x, FiniteChain.point] using hvalues 0 (Nat.zero_le N)
  · simp [x]
  · intro k hk
    rw [← toDual_gradient, (InnerProductSpace.toDual ℝ _).norm_map, hga k hk,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity), hvnorm]
    nlinarith
  · rw [← toDual_gradient, (InnerProductSpace.toDual ℝ _).norm_map, hgt N le_rfl, norm_zero]
    exact he.le

end Optimization.CubicGradientSharpness
