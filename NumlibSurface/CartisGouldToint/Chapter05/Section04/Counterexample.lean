import NumlibSurface.CartisGouldToint.Chapter05.Section04
import Numlib.Analysis.Calculus.EuclideanOne
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Quadratic tests of the local convergence bounds

The source's step estimate (5.4.8) replaces the norm-dependent cubic shift by a positive
constant. An actual legal cubic step for a positive quadratic tests the resulting threshold.
A second complete exact-minimization run tests the successful-iteration bound with an
integer-valued double logarithm, so integer rounding does not repair that count.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section04
open Optimization CubicRegularization RegularizedTaylorModel EuclideanOne Set
open scoped InnerProductSpace

private def phi (t : ℝ) : ℝ := t ^ 2 / 2
private def f : EuclideanSpace ℝ (Fin 1) → ℝ := lift phi
private def v (t : ℝ) : EuclideanSpace ℝ (Fin 1) := coord.symm t
private theorem cv (t : ℝ) : coord (v t) = t := coord.apply_symm_apply t
private theorem nv (t : ℝ) : ‖v t‖ = |t| := by
  exact (coord.symm.norm_map t).trans (Real.norm_eq_abs t)
private theorem dphi (t : ℝ) : HasDerivAt phi t t := by
  unfold phi
  convert ((hasDerivAt_id t).pow 2).div_const 2 using 1 <;>
    norm_num
private theorem deriv_phi : deriv phi = id := funext (fun t => (dphi t).deriv)
private theorem smooth : ContDiff ℝ 2 f := by
  apply EuclideanOne.contDiff
  unfold phi
  fun_prop
private theorem grad (x : EuclideanSpace ℝ (Fin 1)) : gradient f x = x := by
  exact (EuclideanOne.gradient_eq (dphi (coord x))).trans (coord.symm_apply_apply x)
private theorem df (x u : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ f x u = coord x * coord u := by
  change fderiv ℝ (lift phi) x u = _
  rw [(EuclideanOne.hasFDerivAt (dphi (coord x))).fderiv]
  rfl
private theorem hess (x u w : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ (fderiv ℝ f) x u w = coord u * coord w := by
  have hd : HasDerivAt (deriv phi) 1 (coord x) := by
    rw [deriv_phi]
    exact hasDerivAt_id _
  simpa only [f, one_mul] using
    EuclideanOne.fderiv_fderiv_apply (fun x => (dphi x).differentiableAt) hd u w
private theorem hess_norm (x : EuclideanSpace ℝ (Fin 1)) :
    ∀ u, fderiv ℝ (fderiv ℝ f) x u u = 1 * ‖u‖ ^ 2 := by
  intro u
  rw [hess, ← coord.norm_map u, Real.norm_eq_abs, sq_abs]
  ring
private theorem curvature (x : EuclideanSpace ℝ (Fin 1)) :
    leastCurvature (fderiv ℝ (fderiv ℝ f) x) = 1 :=
  leastCurvature_eq_of_scalar _ (hess_norm x)
private theorem lipschitz : Chapter03.Section01.hessianLipschitz f 1 := by
  refine ⟨⟨smooth, by norm_num, ?_⟩, le_rfl⟩
  intro x y
  rw [norm_iteratedFDeriv_sub_eq_fderiv_sub, norm_iteratedFDeriv_sub_eq_fderiv_sub,
    norm_iteratedFDeriv_zero_sub]
  have he : fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ f) y := by
    ext u w
    rw [hess, hess]
  rw [he, sub_self, norm_zero]
  positivity
private theorem taylor (x s : EuclideanSpace ℝ (Fin 1)) :
    taylorModel f 2 x s = phi (coord x + coord s) := by
  rw [show 2 = 1 + 1 from rfl, taylorModel_succ, taylorModel_one,
    iteratedFDeriv_two_apply, hess, df]
  simp only [f, lift_apply, phi, smul_eq_mul]
  norm_num
  ring
private theorem model (x : EuclideanSpace ℝ (Fin 1)) (sigma : ℝ) :
    CubicRegularization.cubicModel f x sigma =
      lift (fun t => phi (coord x + t) + sigma / 6 * |t| ^ 3) := by
  funext s
  rw [CubicRegularization.cubicModel_eq, taylor]
  simp only [lift_apply, ← coord.norm_map s, Real.norm_eq_abs]
private theorem initial_residual :
    fderiv ℝ (CubicRegularization.cubicModel f (v (17 / 16384)) 128) (v (-1 / 1024)) = 0 := by
  rw [model]
  have hd := (dphi (17 / 16384 + (-1 / 1024))).comp (-1 / 1024)
    ((hasDerivAt_id (-1 / 1024 : ℝ)).const_add (17 / 16384))
  have ha :=
    ((hasDerivAt_abs_neg (by norm_num : (-1 / 1024 : ℝ) < 0)).pow 3).const_mul (128 / 6 : ℝ)
  have hh := hd.add ha
  have hh' : HasDerivAt (fun t : ℝ => phi (coord (v (17 / 16384)) + t) + 128 / 6 * |t| ^ 3)
      0 (coord (v (-1 / 1024))) := by
    convert hh using 1
    · rfl
    · norm_num
    · exact cv _
  rw [(EuclideanOne.hasFDerivAt hh').fderiv]
  simp
private theorem initial_decrease :
    CubicRegularization.cubicModel f (v (17 / 16384)) 128 (v (-1 / 1024)) < f (v (17 / 16384)) := by
  rw [model]
  norm_num [lift_apply, cv, f, phi]
private theorem initial_ratio :
    CubicRegularization.ratio f (v (17 / 16384)) (v (-1 / 1024)) 128 = 1 := by
  have hs : v (-1 / 1024) ≠ 0 := by
    intro h
    have hh := congrArg coord h
    norm_num [cv] at hh
  rw [CubicRegularization.ratio, ite_eq_right hs, taylorModel_zero, taylor]
  norm_num [f, lift_apply, phi, cv, map_add]

private def params : ParameterUpdates.RegularizationParameters where
  eta1 := 1 / 2
  eta2 := 3 / 4
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 128
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num
private def X : ℕ → EuclideanSpace ℝ (Fin 1)
  | 0 => v (17 / 16384)
  | k + 1 => (exactStates params f (v (1 / 16384)) 128 k).1
private def S : ℕ → EuclideanSpace ℝ (Fin 1)
  | 0 => v (-1 / 1024)
  | k + 1 => exactSteps params f (v (1 / 16384)) 128 k
private def Sigma : ℕ → ℝ
  | 0 => 128
  | k + 1 => (exactStates params f (v (1 / 16384)) 128 k).2
private theorem tailRun : IsRun params 1 f
    (fun k => (exactStates params f (v (1 / 16384)) 128 k).1)
    (exactSteps params f (v (1 / 16384)) 128)
    (fun k => (exactStates params f (v (1 / 16384)) 128 k).2) :=
  exactStates_isRun params smooth _ (by norm_num [params]) (by norm_num)
private theorem lawful : IsRun params 1 f X S Sigma where
  initial_lower := by norm_num [params, Sigma]
  update k := by
    cases k with
    | zero =>
      simp only [Sigma, X, S, initial_ratio, exactStates_zero]
      norm_num [params]
    | succ k => exact tailRun.update k
  iterate k := by
    cases k with
    | zero =>
      simp only [X, S, Sigma, initial_ratio, params]
      norm_num
      apply coord.injective
      norm_num [cv, map_add]
    | succ k => exact tailRun.iterate k
  decrease k := by
    cases k with
    | zero => exact Or.inl initial_decrease
    | succ k => exact tailRun.decrease k
  residual k := by
    cases k with
    | zero => rw [X, S, Sigma, initial_residual, norm_zero]; positivity
    | succ k => exact tailRun.residual k
private theorem strengthened (k : ℕ) :
    ‖fderiv ℝ (CubicRegularization.cubicModel f (X k) (Sigma k)) (S k)‖ ≤
      min ‖gradient f (X k)‖ (‖S k‖ ^ 2 / 2) := by
  have hz : fderiv ℝ (CubicRegularization.cubicModel f (X k) (Sigma k)) (S k) = 0 := by
    cases k with
    | zero => exact initial_residual
    | succ k =>
      exact fderiv_eq_zero_of_isMinOn_cubicModel
        (exactSteps_isMinOn params f _ (by norm_num [params]) k)
  rw [hz, norm_zero]
  exact le_min (norm_nonneg _) (by positivity)
private theorem reference_min : IsLocalMin f (v 0) := by
  apply IsMinOn.isLocalMin (s := univ) _ (by simp)
  intro y _
  norm_num [f, lift_apply, phi, cv]
  positivity
private theorem threshold : phaseGradientThreshold 1 1 1 128 128 (3 / 4) = 1 / 16 := by
  norm_num [phaseGradientThreshold, phaseBaseThreshold, phaseCurvatureScale]
private theorem initial_region : X 0 ∈ quadraticConvergenceRegion f (v 0) 1 1 128 128 (3 / 4) := by
  rw [mem_quadraticConvergenceRegion]
  constructor
  · rw [mem_localConvexityRegion]
    simp only [X, v, map_zero, sub_zero]
    norm_num [localConvexityRadius, curvature, ← nv]
  · rw [grad, curvature, threshold]
    norm_num [X, nv]
private theorem failed_bound :
    ‖gradient f (X 0)‖ ^ 2 / phaseGradientThreshold 1 1 1 128 128 (3 / 4) <
      ‖gradient f (X 1)‖ := by
  rw [grad, grad, threshold]
  norm_num [X, nv]

/-- The printed phase threshold fails for an actual fully lawful, exact-residual AR2 run.
The objective is a globally bounded-below positive quadratic on Euclidean one-space;
the initial point is in Q_*^1, the first step is very successful, and yet (5.4.4) fails.
Every later step is an actual global cubic-model minimizer with a legal parameter update. -/
theorem literal_phase_quadratic_counterexample :
    ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (p : ParameterUpdates.RegularizationParameters)
      (xstar : EuclideanSpace ℝ (Fin 1))
      (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (sigma : ℕ → ℝ),
      Chapter03.Section01.hessianLipschitz f 1 ∧ IsLocalMin f xstar ∧
      (∀ y, 0 ≤ f y) ∧ leastCurvature (fderiv ℝ (fderiv ℝ f) xstar) = 1 ∧
      p.sigmaMin = 128 ∧ p.eta2 = 3 / 4 ∧ sigma 0 = 128 ∧
      Chapter03.Section03.sigmaMax p 1 (sigma 0) = 128 ∧
      Chapter03.Section03.firstOrderRun p 1 f x s sigma ∧
      (∀ k, ‖fderiv ℝ (Chapter03.Section03.cubicModel f (x k) (sigma k)) (s k)‖ ≤
        min ‖gradient f (x k)‖ (‖s k‖ ^ 2 / 2)) ∧
      x 0 ∈ quadraticConvergenceRegion f xstar 1 1 p.sigmaMin
        (Chapter03.Section03.sigmaMax p 1 (sigma 0)) p.eta2 ∧
      p.eta2 ≤ CubicRegularization.ratio f (x 0) (s 0) (sigma 0) ∧
      ‖gradient f (x 0)‖ ^ 2 / phaseGradientThreshold
        (leastCurvature (fderiv ℝ (fderiv ℝ f) xstar)) 1 1 p.sigmaMin
        (Chapter03.Section03.sigmaMax p 1 (sigma 0)) p.eta2 < ‖gradient f (x 1)‖ := by
  have hmax : Chapter03.Section03.sigmaMax params 1 (Sigma 0) = 128 := by
    norm_num [Chapter03.Section03.sigmaMax, params, Sigma]
  refine ⟨f, params, v 0, X, S, Sigma, lipschitz, reference_min, ?_, curvature _,
    rfl, rfl, rfl, hmax, lawful, ?_, ?_, ?_, ?_⟩
  · intro y
    exact div_nonneg (sq_nonneg _) (by norm_num)
  · intro k
    rw [Chapter03.Section03.cubicModel_eq]
    exact strengthened k
  · rw [hmax]
    exact initial_region
  · simp only [X, S, Sigma, initial_ratio]
    norm_num [params]
  · rw [curvature, hmax]
    exact failed_bound

private def countParams : ParameterUpdates.RegularizationParameters :=
  { params with sigmaMin := 256, sigmaMin_pos := by norm_num }
private def countX (k : ℕ) : EuclideanSpace ℝ (Fin 1) :=
  (exactStates countParams f (v (1 / 64)) 256 k).1
private def countS : ℕ → EuclideanSpace ℝ (Fin 1) :=
  exactSteps countParams f (v (1 / 64)) 256
private def countSigma (k : ℕ) : ℝ :=
  (exactStates countParams f (v (1 / 64)) 256 k).2
private theorem countRun : IsRun countParams 1 f countX countS countSigma :=
  exactStates_isRun countParams smooth _ (by norm_num [countParams]) (by norm_num)
private theorem countMin (k : ℕ) :
    IsMinOn (CubicRegularization.cubicModel f (countX k) (countSigma k)) univ (countS k) :=
  exactSteps_isMinOn countParams f _ (by norm_num [countParams]) k

private theorem min_properties {x s : EuclideanSpace ℝ (Fin 1)}
    (hx : 0 < coord x)
    (hs : IsMinOn (CubicRegularization.cubicModel f x 256) univ s) :
    coord s < 0 ∧ coord (x + s) = 128 * coord s ^ 2 ∧
      0 < coord (x + s) ∧ CubicRegularization.ratio f x s 256 = 1 := by
  have hg : fderiv ℝ f x ≠ 0 := by
    intro hh
    have h := congrArg (fun F => F (v 1)) hh
    rw [df, cv] at h
    simp only [zero_apply, mul_one] at h
    linarith
  have hd := strict_decrease_of_isMinOn_cubicModel smooth.contDiffAt
    (by norm_num : (0 : ℝ) < 256) (Or.inl hg) hs
  have hneg : coord s < 0 := by
    by_contra hn
    have hn' : 0 ≤ coord s := le_of_not_gt hn
    rw [model] at hd
    simp only [lift_apply, f, phi] at hd
    have : 0 ≤ (256 / 6 : ℝ) * |coord s| ^ 3 := by positivity
    nlinarith [mul_nonneg hx.le hn']
  have hd1 := (dphi (coord x + coord s)).comp (coord s)
    ((hasDerivAt_id (coord s)).const_add (coord x))
  have hd2 := ((hasDerivAt_abs_neg hneg).pow 3).const_mul (256 / 6 : ℝ)
  have hd3 := EuclideanOne.hasFDerivAt (hd1.add hd2)
  have hz := fderiv_eq_zero_of_isMinOn_cubicModel hs
  rw [model] at hz
  have heq := congrArg (fun F => F (v 1)) (hd3.fderiv.symm.trans hz)
  change ((coord x + coord s) * 1 + (256 / 6 : ℝ) *
    (3 * |coord s| ^ (3 - 1 : ℕ) * -1)) * coord (v 1) = 0 at heq
  norm_num only [cv, mul_one, Nat.reduceSub] at heq
  have heq' : coord x + coord s = 128 * coord s ^ 2 := by
    rw [abs_of_neg hneg] at heq
    nlinarith [heq]
  have hp : 0 < coord (x + s) := by
    rw [map_add, heq']
    exact mul_pos (by norm_num) (sq_pos_of_neg hneg)
  have hr : CubicRegularization.ratio f x s 256 = 1 := by
    have hs0 : s ≠ 0 := by
      intro hh
      simp only [hh, map_zero] at hneg
      exact (lt_irrefl 0 hneg)
    have hden : f x - taylorModel f 2 x s ≠ 0 := by
      rw [CubicRegularization.cubicModel_eq] at hd
      have hreg : 0 ≤ (256 / 6 : ℝ) * ‖s‖ ^ 3 := by positivity
      linarith
    rw [CubicRegularization.ratio, ite_eq_right hs0, taylorModel_zero]
    have ht : taylorModel f 2 x s = f (x + s) := by
      rw [taylor]
      simp only [f, lift_apply, map_add]
    rw [ht] at hden ⊢
    exact div_self hden
  exact ⟨hneg, by simpa only [map_add] using heq', hp, hr⟩

private theorem count_invariants (k : ℕ) :
    0 < coord (countX k) ∧ countSigma k = 256 := by
  induction k with
  | zero => norm_num [countX, countSigma, cv]
  | succ k ih =>
    have hm := countMin k
    rw [ih.2] at hm
    obtain ⟨_, _, hp, hr⟩ := min_properties ih.1 hm
    have hs : countX (k + 1) = countX k + countS k := by
      have hi := countRun.iterate k
      rw [ih.2, hr] at hi
      simpa only [countParams, params, show (1 / 2 : ℝ) ≤ 1 by norm_num,
        ↓reduceIte] using hi
    constructor
    · rwa [hs]
    · change FirstOrderRegularization.nextSigma countParams
        (CubicRegularization.ratio f (countX k) (countS k) (countSigma k))
        (countSigma k) = 256
      rw [ih.2, hr]
      norm_num [FirstOrderRegularization.nextSigma, countParams, params]

private theorem count_ratio (k : ℕ) :
    CubicRegularization.ratio f (countX k) (countS k) (countSigma k) = 1 := by
  have hm := countMin k
  rw [(count_invariants k).2] at hm ⊢
  exact (min_properties (count_invariants k).1 hm).2.2.2
private theorem count_iterate (k : ℕ) : countX (k + 1) = countX k + countS k := by
  have hi := countRun.iterate k
  rw [count_ratio] at hi
  simpa only [countParams, params, show (1 / 2 : ℝ) ≤ 1 by norm_num, ↓reduceIte] using hi
private theorem count_count (j : ℕ) :
    ParameterUpdates.successCount
      (fun k => countParams.eta1 ≤
        CubicRegularization.ratio f (countX k) (countS k) (countSigma k)) j = j := by
  norm_num [ParameterUpdates.successCount, count_ratio, countParams, params]
private theorem count_first : coord (countX 1) = 1 / 128 := by
  have hm := countMin 0
  rw [(count_invariants 0).2] at hm
  obtain ⟨hs, heq, _, _⟩ := min_properties (count_invariants 0).1 hm
  rw [count_iterate]
  have hx0 : coord (countX 0) = 1 / 64 := by norm_num [countX, cv]
  rw [map_add, hx0] at heq ⊢
  have hf : (coord (countS 0) + 1 / 128) * (128 * coord (countS 0) - 2) = 0 := by
    nlinarith [heq]
  rcases mul_eq_zero.mp hf with h | h
  · linarith
  · linarith
private theorem count_second : (1 / 1024 : ℝ) < coord (countX 2) := by
  have hm := countMin 1
  rw [(count_invariants 1).2] at hm
  obtain ⟨_, heq, _, _⟩ := min_properties (count_invariants 1).1 hm
  have hi := congrArg coord (count_iterate 1)
  rw [map_add, count_first] at hi
  rw [← count_iterate] at heq
  by_contra hn
  have hh : coord (countX 2) ≤ 1 / 1024 := le_of_not_gt hn
  have hs : coord (countS 1) ≤ -7 / 1024 := by linarith
  nlinarith [sq_nonneg (coord (countS 1) + 7 / 1024)]
private theorem count_no_quality (j : ℕ) (hj : j ≤ 2) :
    (1 / 1024 : ℝ) < ‖gradient f (countX j)‖ := by
  rw [grad, ← coord.norm_map, Real.norm_eq_abs, abs_of_pos (count_invariants j).1]
  interval_cases j
  · norm_num [countX, cv]
  · rw [count_first]; norm_num
  · exact count_second
private theorem count_log :
    Real.logb 2 (Real.logb 2 ((1 / 64 : ℝ) / (1 / 1024))) = 2 := by
  have h16 : Real.logb 2 16 = 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  norm_num only [show ((1 / 64 : ℝ) / (1 / 1024)) = 16 by norm_num, h16, h4]

/-- Lemma 5.4.3's successful-iteration bound fails for an actual exact-minimization AR2
run, even when the displayed double logarithm is the integer two. The globally nonnegative
quadratic has unit reference curvature, normalized Hessian Lipschitz constant one, and
initial gradient `zeta = 1/64 ≤ zeta_*/2 = 1/32` inside the source ball. Every model is
minimized globally, every residual is zero, and every iteration is very successful.
Nevertheless all states reachable with at most two successful steps have gradient greater
than `epsilon = 1/1024`. Taking a ceiling or adding a zero-iteration branch cannot repair
this instance. This statement makes no claim about the additional global term in Theorem 5.4.4. -/
theorem literal_phase_count_counterexample :
    ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (p : ParameterUpdates.RegularizationParameters)
      (xstar : EuclideanSpace ℝ (Fin 1))
      (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (sigma : ℕ → ℝ),
      Chapter03.Section01.hessianLipschitz f 1 ∧ IsLocalMin f xstar ∧
      (∀ y, 0 ≤ f y) ∧ leastCurvature (fderiv ℝ (fderiv ℝ f) xstar) = 1 ∧
      p.sigmaMin = 256 ∧ p.eta2 = 3 / 4 ∧ (∀ k, sigma k = 256) ∧
      Chapter03.Section03.sigmaMax p 1 (sigma 0) = 256 ∧
      Chapter03.Section03.firstOrderRun p 1 f x s sigma ∧
      (∀ k, IsMinOn (Chapter03.Section03.cubicModel f (x k) (sigma k)) univ (s k)) ∧
      (∀ k, ‖fderiv ℝ (Chapter03.Section03.cubicModel f (x k) (sigma k)) (s k)‖ ≤
        min ‖gradient f (x k)‖ (‖s k‖ ^ 2 / 2)) ∧
      x 0 ∈ localConvexityRegion f xstar 1 ∧
      ‖gradient f (x 0)‖ = 1 / 64 ∧
      (1 / 64 : ℝ) ≤ phaseGradientThreshold
        (leastCurvature (fderiv ℝ (fderiv ℝ f) xstar)) 1 1 p.sigmaMin
        (Chapter03.Section03.sigmaMax p 1 (sigma 0)) p.eta2 / 2 ∧
      (∀ k, CubicRegularization.ratio f (x k) (s k) (sigma k) = 1) ∧
      Real.logb 2 (Real.logb 2 ((1 / 64 : ℝ) / (1 / 1024))) = 2 ∧
      ⌈Real.logb 2 (Real.logb 2 ((1 / 64 : ℝ) / (1 / 1024)))⌉₊ = 2 ∧
      ∀ j, (ParameterUpdates.successCount
        (fun k => p.eta1 ≤ CubicRegularization.ratio f (x k) (s k) (sigma k)) j : ℝ) ≤
          Real.logb 2 (Real.logb 2 ((1 / 64 : ℝ) / (1 / 1024))) →
        (1 / 1024 : ℝ) < ‖gradient f (x j)‖ := by
  have hmax : Chapter03.Section03.sigmaMax countParams 1 (countSigma 0) = 256 := by
    norm_num [Chapter03.Section03.sigmaMax, countParams, params, countSigma]
  refine ⟨f, countParams, v 0, countX, countS, countSigma, lipschitz, reference_min,
    ?_, curvature _, rfl, rfl, fun k => (count_invariants k).2, hmax, countRun,
    ?_, ?_, ?_, ?_, ?_, count_ratio, count_log, ?_, ?_⟩
  · intro y
    exact div_nonneg (sq_nonneg _) (by norm_num)
  · intro k
    rw [Chapter03.Section03.cubicModel_eq]
    exact countMin k
  · intro k
    rw [Chapter03.Section03.cubicModel_eq,
      fderiv_eq_zero_of_isMinOn_cubicModel (countMin k), norm_zero]
    exact le_min (norm_nonneg _) (by positivity)
  · rw [mem_localConvexityRegion]
    simp only [countX, exactStates_zero, v, map_zero, sub_zero]
    norm_num [localConvexityRadius, curvature, ← nv]
  · rw [grad]
    norm_num [countX, nv]
  · rw [curvature, hmax]
    norm_num [phaseGradientThreshold, phaseBaseThreshold, phaseCurvatureScale, countParams, params]
  · rw [count_log]
    norm_num
  · intro j hj
    rw [count_count, count_log] at hj
    exact count_no_quality j (by exact_mod_cast hj)

end CartisGouldToint.Chapter05.Section04
