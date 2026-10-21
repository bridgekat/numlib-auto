import Numlib.Analysis.Calculus.BoundedAffineExtension
import Numlib.Optimization.TrustRegionSecondOrder
import Numlib.Optimization.TrustRegionSharpness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# First-order sharpness for trust regions with the true Hessian

A bounded extension of a linear segment plus a small periodic perturbation prescribes
positive unit Hessians at all iterates. Exact quadratic minimizers are accepted with ratio
two, while the objective and Hessian bounds stay independent of the accuracy.
-/
noncomputable section
open scoped NNReal InnerProductSpace
namespace Optimization.TrustRegionHessianSharpness

/-- A periodic perturbation keeps the gradient fixed and prescribes unit Hessian at grid points. -/
def wavy (c : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  -2 * ε * c x + ε ^ 2 / Real.pi ^ 2 * (1 - Real.cos (Real.pi * x / ε))

/-- The perturbed bounded extension is C². -/
theorem wavy_contDiff {c : ℝ → ℝ} (hc : ContDiff ℝ 2 c) (ε : ℝ) :
    ContDiff ℝ 2 (wavy c ε) := by fun_prop [wavy]

/-- First derivative of the periodic perturbation. -/
theorem deriv_wavy {c : ℝ → ℝ} (hc : ContDiff ℝ 2 c) {ε : ℝ} (hε : ε ≠ 0)
    (x : ℝ) : deriv (wavy c ε) x =
      -2 * ε * deriv c x + ε / Real.pi * Real.sin (Real.pi * x / ε) := by
  have hd := (hc.differentiable (by norm_num) x).hasDerivAt
  have hh := (hd.const_mul (-2 * ε)).add
    (((((hasDerivAt_id x).const_mul Real.pi).div_const ε).cos.const_sub 1).const_mul
      (ε ^ 2 / Real.pi ^ 2))
  convert hh.deriv using 1 <;> first | rfl | (simp only [id_eq]; field_simp)

/-- Second derivative of the periodic perturbation. -/
theorem deriv_deriv_wavy {c : ℝ → ℝ} (hc : ContDiff ℝ 2 c) {ε : ℝ} (hε : ε ≠ 0)
    (x : ℝ) : deriv (deriv (wavy c ε)) x =
      -2 * ε * deriv (deriv c) x + Real.cos (Real.pi * x / ε) := by
  have hd : Differentiable ℝ (deriv c) := by
    simpa only [iteratedDeriv_one] using hc.differentiable_iteratedDeriv 1 (by norm_num)
  rw [show deriv (wavy c ε) = fun x =>
    -2 * ε * deriv c x + ε / Real.pi * Real.sin (Real.pi * x / ε) from
      funext (deriv_wavy hc hε)]
  have hh := ((hd x).hasDerivAt.const_mul (-2 * ε)).add
    (((((hasDerivAt_id x).const_mul Real.pi).div_const ε).sin).const_mul (ε / Real.pi))
  convert hh.deriv using 1 <;> first | rfl | (simp only [id_eq]; field_simp)

/-- Uniform bounded C² scalar objectives have a long constant-gradient chain with unit
Hessians at all knots and zero terminal gradient. -/
theorem exists_scalar_chain : ∃ B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ (φ : ℝ → ℝ) (N : ℕ), ContDiff ℝ 2 φ ∧
      (∀ t, |φ t| ≤ B) ∧ (∀ t, |deriv (deriv φ) t| ≤ B) ∧
      (∀ k ≤ N, φ ((k : ℝ) * (2 * ε)) = -(k : ℝ) * (2 * ε) ^ 2 ∧
        deriv φ ((k : ℝ) * (2 * ε)) = (if k < N then -(2 * ε) else 0) ∧
        deriv (deriv φ) ((k : ℝ) * (2 * ε)) = 1) ∧
      ⌈1 / ε ^ 2⌉₊ < N := by
  obtain ⟨B, hbase⟩ := BoundedAffineExtension.exists_extension
  let M : ℝ≥0 := ⟨14 + 4 * B + 2 / Real.pi ^ 2, by positivity⟩
  refine ⟨M, ?_⟩
  intro ε hε hεone
  let N := ⌈1 / ε ^ 2⌉₊ + 1
  let l : ℝ := ((N - 1 : ℕ) : ℝ) * (2 * ε)
  have hN : 0 < N := by dsimp [N]; omega
  have hl : 0 ≤ l := by dsimp [l]; positivity
  obtain ⟨c, hc, hmid, hend, hdend, hddend, hb, hdd⟩ :=
    hbase (2 * ε) l (by positivity) hl
  let φ := wavy c ε
  have he : ε ≠ 0 := hε.ne'
  have hpow : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcount : (N : ℝ) * ε ^ 2 ≤ 3 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 1 / ε ^ 2 by positivity)
    have hm := mul_lt_mul_of_pos_right hh hpow
    have hi : (1 / ε ^ 2 + 1) * ε ^ 2 = 1 + ε ^ 2 := by field_simp
    rw [hi] at hm
    dsimp [N]
    push_cast
    nlinarith [sq_nonneg (ε - 1)]
  have hlend : l + 2 * ε = (N : ℝ) * (2 * ε) := by
    dsimp [l]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    push_cast
    ring
  refine ⟨φ, N, wavy_contDiff hc ε, ?_, ?_, ?_, by dsimp [N]; omega⟩
  · intro t
    dsimp [φ, wavy]
    have hcos : |1 - Real.cos (Real.pi * t / ε)| ≤ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      linarith [Real.neg_one_le_cos (Real.pi * t / ε)]
    have hh0 := mul_le_mul_of_nonneg_left (hb t) (show 0 ≤ 2 * ε by positivity)
    have hh1 := mul_le_mul_of_nonneg_left hcos
      (show 0 ≤ ε ^ 2 / Real.pi ^ 2 by positivity)
    have hsq : ε ^ 2 ≤ 1 := by nlinarith
    have hb0 := mul_le_mul_of_nonneg_right hsq B.coe_nonneg
    have hp0 := mul_le_mul_of_nonneg_right (show ε ^ 2 ≤ 1 by nlinarith)
      (show 0 ≤ 2 / Real.pi ^ 2 by positivity)
    have hlen : 2 * ε * l ≤ 4 * (N : ℝ) * ε ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left
        (show l ≤ (N : ℝ) * (2 * ε) by linarith) (show 0 ≤ 2 * ε by positivity)
      nlinarith only [hm]
    have hA : |-2 * ε * c t| ≤ 2 * ε * (l + 2 * ε * B) := by
      simpa only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos hε] using hh0
    have hD : |ε ^ 2 / Real.pi ^ 2 * (1 - Real.cos (Real.pi * t / ε))| ≤
        ε ^ 2 * (2 / Real.pi ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 2 / Real.pi ^ 2)]
      convert hh1 using 1; ring
    apply (abs_add_le _ _).trans
    change _ ≤ 14 + 4 * (B : ℝ) + 2 / Real.pi ^ 2
    nlinarith only [hA, hD, hlen, hcount, hb0, hp0]
  · intro t
    rw [deriv_deriv_wavy hc he]
    apply (abs_add_le _ _).trans
    have hh := mul_le_mul_of_nonneg_left (hdd t) (show 0 ≤ 2 * ε by positivity)
    have hid : 2 * ε * ((B : ℝ) / (2 * ε)) = B := by field_simp
    rw [hid] at hh
    simp only [abs_mul, abs_neg, abs_of_pos hε, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hcos := Real.abs_cos_le_one (Real.pi * t / ε)
    change _ ≤ 14 + 4 * (B : ℝ) + 2 / Real.pi ^ 2
    linarith [show 0 ≤ 2 / Real.pi ^ 2 by positivity]
  · intro k hk
    have hangle : Real.pi * ((k : ℝ) * (2 * ε)) / ε = (k : ℝ) * (2 * Real.pi) := by
      field_simp
    have hs : Real.sin (Real.pi * ((k : ℝ) * (2 * ε)) / ε) = 0 := by
      rw [hangle]
      simpa [mul_assoc, mul_comm, mul_left_comm] using Real.sin_nat_mul_pi (2 * k)
    have hcos : Real.cos (Real.pi * ((k : ℝ) * (2 * ε)) / ε) = 1 := by
      rw [hangle, Real.cos_nat_mul_two_pi]
    have hj : c ((k : ℝ) * (2 * ε)) = (k : ℝ) * (2 * ε) ∧
        deriv c ((k : ℝ) * (2 * ε)) = (if k < N then 1 else 0) ∧
        deriv (deriv c) ((k : ℝ) * (2 * ε)) = 0 := by
      by_cases hk' : k < N
      · have hkl : (k : ℝ) * (2 * ε) ≤ l := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (show k ≤ N - 1 by omega)
        simpa [hk'] using hmid ((k : ℝ) * (2 * ε)) ⟨by positivity, hkl⟩
      · have heq : k = N := by omega
        subst k
        rw [← hlend]
        simpa using (show c (l + 2 * ε) = l + 2 * ε ∧
          deriv c (l + 2 * ε) = 0 ∧ deriv (deriv c) (l + 2 * ε) = 0 from
          ⟨hend, hdend, hddend⟩)
    refine ⟨?_, ?_, ?_⟩
    · dsimp [φ, wavy]
      rw [hj.1, hcos]
      ring
    · rw [deriv_wavy hc he, hj.2.1, hs]
      split_ifs <;> ring
    · rw [deriv_deriv_wavy hc he, hj.2.2, hcos]
      ring

/-- Trust-region traces using the actual, uniformly bounded Hessian require strictly more
than the ceiling of ε⁻² iterations to reach first-order accuracy. The radius starts at two,
and the true Hessian is positive at every iterate. -/
theorem exists_sharp_firstOrder_family : ∃ B : ℝ≥0,
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (delta : ℕ → ℝ),
        ContDiff ℝ 2 f ∧ (∀ y, |f y| ≤ B) ∧
        (∀ y, ‖TrustRegionSecondOrder.hessianOperator f y‖ ≤ B) ∧
        f (x 0) = 0 ∧ x 0 = 0 ∧ delta 0 = 2 ∧
        TrustRegionSecondOrder.IsRun TrustRegion.sharpParameters true f x s delta ∧
        (∀ k < N, ε < ‖gradient f (x k)‖) ∧ gradient f (x N) = 0 ∧
        (∀ k, TrustRegionSecondOrder.curvature f (x k) = 1) ∧
        ParameterUpdates.successCount (fun k => TrustRegion.sharpParameters.eta1 ≤
          TrustRegion.ratio f (gradient f (x k))
            (TrustRegionSecondOrder.hessianOperator f (x k)) (x k) (s k)) N = N ∧
        ⌈1 / ε ^ 2⌉₊ < N := by
  obtain ⟨B, hfamily⟩ := exists_scalar_chain
  refine ⟨B, ?_⟩
  intro ε hε hεone
  obtain ⟨φ, N, hφ, hb, hHbound, hjet, hN⟩ := hfamily ε hε hεone
  let f := EuclideanOne.lift φ
  let v := EuclideanOne.coord.symm (2 * ε)
  let x := FiniteChain.point N v
  let s := FiniteChain.step N v
  have hvnorm : ‖v‖ = 2 * ε := by
    change ‖EuclideanOne.coord.symm (2 * ε)‖ = _
    rw [EuclideanOne.coord.symm.norm_map, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvnorm]; positivity)
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hvalues (k : ℕ) (hk : k ≤ N) :
      f ((k : ℝ) • v) = -(k : ℝ) * ‖v‖ ^ 2 := by
    simpa [f, v, EuclideanOne.lift, Function.comp_def, hvnorm] using (hjet k hk).1
  have hgrads (k : ℕ) (hk : k ≤ N) :
      gradient f ((k : ℝ) • v) = if k < N then -v else 0 := by
    rw [EuclideanOne.gradient_eq_deriv hd]
    have hh := (hjet k hk).2.1
    simp only [map_smul, smul_eq_mul]
    change EuclideanOne.coord.symm (deriv φ ((k : ℝ) * (2 * ε))) = _
    rw [hh]
    split_ifs <;> simp [v]
  have hH (k : ℕ) (hk : k ≤ N) :
      TrustRegionSecondOrder.hessianOperator f ((k : ℝ) • v) =
        ContinuousLinearMap.id ℝ _ := by
    rw [TrustRegionSecondOrder.hessianOperator,
      EuclideanOne.continuousLinearMapOfBilin_fderiv_fderiv hφ]
    simpa [v] using congrArg (fun a : ℝ => a •
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) (hjet k hk).2.2
  have hHall (k : ℕ) : TrustRegionSecondOrder.hessianOperator f (x k) =
      ContinuousLinearMap.id ℝ _ := hH (min k N) (Nat.min_le_right k N)
  have hcurv (k : ℕ) : TrustRegionSecondOrder.curvature f (x k) = 1 := by
    apply leastCurvature_eq_of_scalar
    intro u
    have hh := InnerProductSpace.continuousLinearMapOfBilin_apply
      (fderiv ℝ (fderiv ℝ f) (x k)) u u
    change inner ℝ (TrustRegionSecondOrder.hessianOperator f (x k) u) u = _ at hh
    rw [hHall] at hh
    simpa [real_inner_self_eq_norm_sq] using hh.symm
  have htr := TrustRegion.isRun_sharpChain_with_radius (by norm_num : (0 : ℝ) < 2)
    hv (by rw [hvnorm]; linarith) hvalues hgrads
  have hrun : TrustRegionSecondOrder.IsRun TrustRegion.sharpParameters true f x s
      (TrustRegion.sharpRadiusWith 2 N) := by
    constructor
    · simpa only [hHall] using htr
    · intro _ k hk
      rw [hcurv] at hk
      norm_num at hk
  have hcount : ParameterUpdates.successCount (fun k => TrustRegion.sharpParameters.eta1 ≤
      TrustRegion.ratio f (gradient f (x k))
        (TrustRegionSecondOrder.hessianOperator f (x k)) (x k) (s k)) N = N := by
    classical
    unfold ParameterUpdates.successCount
    rw [Finset.filter_eq_self.mpr (fun k hk => ?_), Finset.card_range]
    rw [hHall, TrustRegion.sharp_ratio_active hv (Finset.mem_range.mp hk) hvalues]
    · norm_num [TrustRegion.sharpParameters]
    · intro i hi
      simpa [hi] using hgrads i hi.le
  refine ⟨f, N, x, s, TrustRegion.sharpRadiusWith 2 N, EuclideanOne.contDiff hφ,
    fun y => hb _, ?_, ?_, ?_, ?_, hrun, ?_, ?_, hcurv, hcount, hN⟩
  · intro y
    rw [TrustRegionSecondOrder.hessianOperator,
      EuclideanOne.continuousLinearMapOfBilin_fderiv_fderiv hφ,
      norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
    exact hHbound _
  · simpa [x, FiniteChain.point] using hvalues 0 (Nat.zero_le N)
  · simp [x]
  · simp [TrustRegion.sharpRadiusWith, TrustRegion.sharpRadius]
  · intro k hk
    rw [show x k = (k : ℝ) • v from FiniteChain.point_of_le v hk.le, hgrads k hk.le]
    simp only [hk, ↓reduceIte, norm_neg, hvnorm]
    linarith
  · rw [show x N = (N : ℝ) • v from FiniteChain.point_of_le v le_rfl, hgrads N le_rfl]
    simp

end Optimization.TrustRegionHessianSharpness
