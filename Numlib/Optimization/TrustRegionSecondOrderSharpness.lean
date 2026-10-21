import Numlib.Optimization.TrustRegionSecondOrder

import Numlib.Optimization.CubicCurvatureSharpness
import Numlib.Optimization.TrustRegionSharpness

/-!
# Trust-region traces driven by negative curvature

Uniform scalar Hermite interpolation realizes true objective derivatives. The active steps
minimize the true quadratic model on a ball, and actual model agreement makes every active
iteration very successful. The initial radius is explicitly the requested accuracy.
-/

noncomputable section
open scoped InnerProductSpace NNReal
open InnerProductSpace


namespace Optimization.TrustRegionSecondOrderSharpness
open QuadraticSubproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radius stays equal to ε during the finite chain and contracts afterwards. -/
def radius (ε : ℝ) (N k : ℕ) : ℝ := ε * (1 / 2 : ℝ) ^ (k - N)

/-- A uniformly bounded smooth family requires at least ε⁻³ successful trust-region steps
before its true negative curvature meets the tolerance. The initial radius equals ε, as in
the construction, while all objective and Hessian bounds are independent of ε. -/
theorem exists_sharp_secondOrder_family :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (delta : ℕ → ℝ),
        ContDiff ℝ 2 f ∧ LipschitzWith L (iteratedFDeriv ℝ 2 f) ∧
        (∀ y, |f y| ≤ B) ∧
        (∀ y, ‖TrustRegionSecondOrder.hessianOperator f y‖ ≤ B) ∧
        f (x 0) = 0 ∧ x 0 = 0 ∧ delta 0 = ε ∧
        TrustRegionSecondOrder.IsRun TrustRegion.sharpParameters true f x s delta ∧
        (∀ k, gradient f (x k) = 0) ∧
        (∀ k < N, TrustRegionSecondOrder.curvature f (x k) = -2 * ε) ∧
        TrustRegionSecondOrder.curvature f (x N) = 0 ∧
        ParameterUpdates.successCount (fun k => TrustRegion.sharpParameters.eta1 ≤
          TrustRegion.ratio f (gradient f (x k))
            (TrustRegionSecondOrder.hessianOperator f (x k)) (x k) (s k)) N = N ∧
        1 / ε ^ 3 ≤ (N : ℝ) := by
  obtain ⟨L, B, hfamily⟩ := CubicCurvatureSharpness.exists_scalar_chain
  refine ⟨L, B, ?_⟩
  intro ε hε hεone
  obtain ⟨ψ, N, hψ, hLip, hjet, hbound, hNlower⟩ := hfamily ε hε hεone
  let f := EuclideanOne.lift ψ
  let v := EuclideanOne.coord.symm ε
  let x := FiniteChain.point N v
  let s := FiniteChain.step N v
  let delta := radius ε N
  have hvnorm : ‖v‖ = ε := by
    change ‖EuclideanOne.coord.symm ε‖ = _
    rw [EuclideanOne.coord.symm.norm_map, Real.norm_eq_abs, abs_of_pos hε]
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv ψ) := by
    simpa only [iteratedDeriv_one] using hψ.differentiable_iteratedDeriv 1 (by norm_num)
  have hvalues (k : ℕ) (hk : k ≤ N) : f ((k : ℝ) • v) = -(k : ℝ) * ε ^ 3 := by
    simpa [f, v, EuclideanOne.lift, Function.comp_def, CubicCurvatureSharpness.curvatureJet]
      using hjet k hk 0 (by norm_num)
  have hgrad (k : ℕ) (hk : k ≤ N) : gradient f ((k : ℝ) • v) = 0 := by
    have hj : deriv ψ ((k : ℝ) * ε) = 0 := by
      simpa [CubicCurvatureSharpness.curvatureJet] using hjet k hk 1 (by norm_num)
    rw [EuclideanOne.gradient_eq_deriv hd]
    simp [v, hj]
  have hessian (k : ℕ) (hk : k ≤ N) :
      TrustRegionSecondOrder.hessianOperator f ((k : ℝ) • v) =
        (if k < N then -2 * ε else 0) • ContinuousLinearMap.id ℝ _ := by
    have hj : deriv (deriv ψ) ((k : ℝ) * ε) = if k < N then -2 * ε else 0 := by
      simpa [iteratedDeriv_succ, iteratedDeriv_zero, CubicCurvatureSharpness.curvatureJet]
        using hjet k hk 2 (by norm_num)
    rw [TrustRegionSecondOrder.hessianOperator,
      EuclideanOne.continuousLinearMapOfBilin_fderiv_fderiv hψ]
    simp [v, hj]
  have hgall (k : ℕ) : gradient f (x k) = 0 :=
    hgrad (min k N) (Nat.min_le_right k N)
  have hHactive (k : ℕ) (hk : k < N) :
      TrustRegionSecondOrder.hessianOperator f (x k) =
        (-2 * ε) • ContinuousLinearMap.id ℝ _ := by
    simpa [x, FiniteChain.point_of_le v hk.le, hk] using hessian k hk.le
  have hHterminal (k : ℕ) (hk : N ≤ k) :
      TrustRegionSecondOrder.hessianOperator f (x k) = 0 := by
    simpa [x, FiniteChain.point_of_ge v hk] using hessian N le_rfl
  have hδactive (k : ℕ) (hk : k ≤ N) : delta k = ε := by
    simp [delta, radius, Nat.sub_eq_zero_of_le hk]
  have hδpos (k : ℕ) : 0 < delta k := by dsimp [delta, radius]; positivity
  have hmin (k : ℕ) (y : EuclideanSpace ℝ (Fin 1)) (hy : ‖y‖ ≤ delta k) :
      quadratic (gradient f (x k)) (TrustRegionSecondOrder.hessianOperator f (x k)) (s k) ≤
        quadratic (gradient f (x k)) (TrustRegionSecondOrder.hessianOperator f (x k)) y := by
    rw [hgall]
    by_cases hk : k < N
    · rw [hHactive k hk]
      apply quadratic_zero_negative_scalar_min (by linarith) (δ := ε)
      · simpa [s, FiniteChain.step, hk] using hvnorm
      · simpa [hδactive k hk.le] using hy
    · simp [s, FiniteChain.step, hk, hHterminal k (Nat.le_of_not_gt hk), quadratic]
  have hratio (k : ℕ) (hk : k < N) :
      TrustRegion.ratio f (gradient f (x k))
        (TrustRegionSecondOrder.hessianOperator f (x k)) (x k) (s k) = 1 := by
    rw [TrustRegion.ratio, hgall, hHactive k hk]
    have hx : x k + s k = x (k + 1) := (FiniteChain.point_add_step N v k).symm
    rw [hx]
    have hfk : f (x k) = -(k : ℝ) * ε ^ 3 := by
      simpa [x, FiniteChain.point_of_le v hk.le] using hvalues k hk.le
    have hfk1 : f (x (k + 1)) = -(k + 1 : ℕ) * ε ^ 3 := by
      simpa [x, FiniteChain.point_of_le v hk] using hvalues (k + 1) hk
    rw [hfk, hfk1]
    simp only [s, FiniteChain.step, hk, ↓reduceIte, quadratic, inner_zero_left,
      inner_zero_right, zero_add, smul_apply,
      ContinuousLinearMap.id_apply, real_inner_smul_right, real_inner_self_eq_norm_sq,
      mul_zero, hvnorm]
    have hdif : -(k : ℝ) * ε ^ 3 - -(k + 1 : ℕ) * ε ^ 3 = ε ^ 3 := by push_cast; ring
    rw [hdif]
    have hden : 0 - 1 / 2 * (-2 * ε * ε ^ 2) = ε ^ 3 := by ring
    rw [hden, div_self (pow_ne_zero 3 hε.ne')]
  have hratio_terminal (k : ℕ) (hk : N ≤ k) :
      TrustRegion.ratio f (gradient f (x k))
        (TrustRegionSecondOrder.hessianOperator f (x k)) (x k) (s k) = 0 := by
    simp [TrustRegion.ratio, s, FiniteChain.step, Nat.not_lt.mpr hk, quadratic]
  have hrun : TrustRegionSecondOrder.IsRun TrustRegion.sharpParameters true f x s delta := by
    constructor
    · constructor
      · exact hδpos 0
      · intro k
        by_cases hk : k < N
        · simp [s, FiniteChain.step, hk, hvnorm, hδactive k hk.le]
        · simp [s, FiniteChain.step, hk, (hδpos k).le]
      · intro k t _ ht
        apply hmin k
        simpa [hgall] using (hδpos k).le
      · intro k
        by_cases hk : k < N
        · rw [hratio k hk]
          norm_num [TrustRegion.sharpParameters]
          exact FiniteChain.point_add_step N v k
        · rw [hratio_terminal k (Nat.le_of_not_gt hk)]
          norm_num [TrustRegion.sharpParameters]
          simp [x, FiniteChain.point_of_ge v (Nat.le_of_not_gt hk),
            FiniteChain.point_of_ge v ((Nat.le_of_not_gt hk).trans (Nat.le_succ k))]
      · intro k
        by_cases hk : k < N
        · rw [hratio k hk]
          norm_num [TrustRegion.sharpParameters, hδactive k hk.le, hδactive (k + 1) hk]
          linarith
        · rw [hratio_terminal k (Nat.le_of_not_gt hk)]
          norm_num [TrustRegion.sharpParameters]
          have hsub : k + 1 - N = k - N + 1 := by omega
          simp [delta, radius, hsub, pow_succ, mul_comm, mul_left_comm]
    · intro _ k _
      obtain ⟨u, hu, hB, hgu⟩ := TrustRegionSecondOrder.exists_signed_unit
        ((EuclideanOne.contDiff hψ).contDiffAt (x := x k))
      refine ⟨u, hu, hB, hgu, hmin k _ ?_⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hδpos k), hu, mul_one]
  have hcurv (k : ℕ) (hk : k ≤ N) :
      TrustRegionSecondOrder.curvature f ((k : ℝ) • v) = if k < N then -2 * ε else 0 := by
    apply leastCurvature_eq_of_scalar
    intro u
    have hh := continuousLinearMapOfBilin_apply
      (fderiv ℝ (fderiv ℝ f) ((k : ℝ) • v)) u u
    change inner ℝ (TrustRegionSecondOrder.hessianOperator f ((k : ℝ) • v) u) u = _ at hh
    rw [hessian k hk] at hh
    simpa only [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
      real_inner_self_eq_norm_sq] using hh.symm
  have hcount : ParameterUpdates.successCount (fun k => TrustRegion.sharpParameters.eta1 ≤
      TrustRegion.ratio f (gradient f (x k))
        (TrustRegionSecondOrder.hessianOperator f (x k)) (x k) (s k)) N = N := by
    classical
    unfold ParameterUpdates.successCount
    rw [Finset.filter_eq_self.mpr (fun k hk => ?_), Finset.card_range]
    rw [hratio k (Finset.mem_range.mp hk)]
    norm_num [TrustRegion.sharpParameters]
  refine ⟨f, N, x, s, delta, EuclideanOne.contDiff hψ,
    EuclideanOne.iteratedFDeriv_lipschitz hψ hLip, ?_, ?_, ?_, ?_, hδactive 0 (Nat.zero_le N),
    hrun, hgall, ?_, ?_, hcount, hNlower⟩
  · intro y
    simpa [f, EuclideanOne.lift] using hbound 0 (by omega) (EuclideanOne.coord y)
  · intro y
    rw [TrustRegionSecondOrder.hessianOperator,
      EuclideanOne.continuousLinearMapOfBilin_fderiv_fderiv hψ]
    rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
      hbound 2 le_rfl (EuclideanOne.coord y)
  · simpa [x, FiniteChain.point] using hvalues 0 (Nat.zero_le N)
  · simp [x]
  · intro k hk
    simpa [x, FiniteChain.point_of_le v hk.le, hk] using hcurv k hk.le
  · simpa [x, FiniteChain.point_of_le v le_rfl] using hcurv N le_rfl

end Optimization.TrustRegionSecondOrderSharpness
