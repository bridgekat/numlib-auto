import NumlibSurface.ConnGouldToint.Chapter14.Section02
import Mathlib.Analysis.Calculus.Deriv.Pow
import Numlib.Optimization.Subproblem.Secular

/-! # Quadratic penalty convergence -/

open Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter14

variable {G F : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Theorem 14.3.1(i)–(ii). A convergent subsequence of approximate
minimizers of the fixed-multiplier penalty has a feasible, stationary limit.
The bounds apply to the reindexed subsequence. -/
theorem theorem_14_3_1 [FiniteDimensional ℝ F] {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) {xstar : G}
    (hA : Function.Surjective (fderiv ℝ c xstar)) {x : ℕ → G}
    (hx : Tendsto x atTop (𝓝 xstar)) (y : F) {μ ω : ℕ → ℝ}
    (hμ : ∀ k, 0 < μ k) (hμlim : Tendsto μ atTop (𝓝 0))
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c y (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0)) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let ystar := ls xstar
    IsEqualityKKT f c xstar ystar ∧
      Tendsto (fun k ↦ firstOrderMultiplier c y (μ k) (x k)) atTop (𝓝 ystar) ∧
      Tendsto (ls ∘ x) atTop (𝓝 ystar) ∧
      ∃ K₁ > 0, ∃ K₂ > 0, ∀ᶠ k in atTop,
        ‖firstOrderMultiplier c y (μ k) (x k) - ystar‖ ≤ K₁ * ω k + K₂ * ‖x k - xstar‖ ∧
        ‖ls (x k) - ystar‖ ≤ K₂ * ‖x k - xstar‖ ∧
        ‖c (x k)‖ ≤ μ k * (K₁ * ω k + ‖y - ystar‖ + K₂ * ‖x k - xstar‖) := by
  let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
  have hu := multiplierGram_isUnit_of_surjective hA
  obtain ⟨K₁, hK₁, K₂, hK₂, hb⟩ := lemma_14_2_2_i (y := fun _ ↦ y) hf hc hu hx hμ hres
  obtain ⟨hy, hls, hkkt⟩ := lemma_14_2_2_ii (y := fun _ ↦ y) hf hc hu hx hμ hres hω
  have hxnorm := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hmajor : Tendsto (fun k ↦ μ k * (K₁ * ω k + ‖y - ystar‖ + K₂ * ‖x k - xstar‖))
      atTop (𝓝 0) := by
    have hsum := ((hω.const_mul K₁).add_const ‖y - ystar‖).add (hxnorm.const_mul K₂)
    simpa only [zero_mul] using hμlim.mul hsum
  have hzero : Tendsto (c ∘ x) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_apply, sub_zero] using squeeze_zero'
      (Eventually.of_forall fun k ↦ norm_nonneg (c (x k))) (hb.mono fun _ h ↦ h.2.2) hmajor
  exact ⟨hkkt (tendsto_nhds_unique (hc.continuous.continuousAt.tendsto.comp hx) hzero),
    hy, hls, K₁, hK₁, K₂, hK₂, hb⟩

/-- Theorem 14.3.1(iii). With an invertible limiting KKT Jacobian the
primal and both multiplier errors are bounded by the inner tolerance and
penalty parameter, while feasibility has an additional penalty factor. -/
theorem theorem_14_3_1_iii [FiniteDimensional ℝ F] {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) {xstar : G}
    (hA : Function.Surjective (fderiv ℝ c xstar)) {x : ℕ → G}
    (hx : Tendsto x atTop (𝓝 xstar)) (y : F) {μ ω : ℕ → ℝ}
    (hμ : ∀ k, 0 < μ k) (hμlim : Tendsto μ atTop (𝓝 0))
    (hres : ∀ k, ‖fderiv ℝ (augmentedLagrangian f c y (μ k)) (x k)‖ ≤ ω k)
    (hω : Tendsto ω atTop (𝓝 0))
    (hK : IsUnit (penaltyKKTJacobian f c
      (xstar, leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)))) :
    let ls := fun z ↦ leastSquaresMultiplier (fderiv ℝ c z) (gradient f z)
    let ystar := ls xstar
    ∃ K₃ > 0, ∃ K₄ > 0, ∃ K₅ > 0, ∃ K₆ > 0, ∃ K₇ > 0, ∀ᶠ k in atTop,
      ‖x k - xstar‖ ≤ K₃ * ω k + K₄ * μ k ∧
      ‖firstOrderMultiplier c y (μ k) (x k) - ystar‖ ≤ K₅ * ω k + K₆ * μ k ∧
      ‖ls (x k) - ystar‖ ≤ K₇ * ω k + K₆ * μ k ∧
      ‖c (x k)‖ ≤ K₅ * μ k * ω k + K₆ * μ k ^ 2 + μ k * ‖y - ystar‖ := by
  let ystar := leastSquaresMultiplier (fderiv ℝ c xstar) (gradient f xstar)
  have hfeas := (theorem_14_3_1 hf hc hA hx y hμ hμlim hres hω).1.1
  obtain ⟨μmax, hmax, K₃, h₃, K₄, h₄, K₅, h₅, K₆, h₆, K₇, h₇, hb⟩ :=
    lemma_14_2_2_iii (y := fun _ ↦ y) hf hc hfeas hx hμ hres hω hK
  let D := ‖y - ystar‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K₃, h₃, K₄ * D, mul_pos h₄ hD, K₅, h₅, K₆ * D, mul_pos h₆ hD, K₇, h₇, ?_⟩
  filter_upwards [hb, hμlim.eventually (gt_mem_nhds hmax)] with k hk hkμ
  obtain ⟨hxk, hyk, hlsk, hck⟩ := hk hkμ.le
  have hD' : ‖y - ystar‖ ≤ D := le_add_of_nonneg_right zero_le_one
  have hfour := mul_le_mul_of_nonneg_left hD' (mul_nonneg h₄.le (hμ k).le)
  have hsix := mul_le_mul_of_nonneg_left hD' (mul_nonneg h₆.le (hμ k).le)
  have hsq := mul_le_mul_of_nonneg_left hD' (mul_nonneg h₆.le (sq_nonneg (μ k)))
  refine ⟨hxk.trans ?_, hyk.trans ?_, hlsk.trans ?_, hck.trans ?_⟩ <;>
    nlinarith only [hfour, hsix, hsq]

open scoped InnerProduct

private theorem gradient_augmentedLagrangian_eq {f : G → ℝ} {c : G → F} {x : G}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (y : F) (μ : ℝ) :
    gradient (augmentedLagrangian f c y μ) x =
      gradient f x - (fderiv ℝ c x).adjoint (firstOrderMultiplier c y μ x) := by
  rw [gradient, fderiv_augmentedLagrangian_eq hf hc]
  exact gradient_lagrangian_eq hf hc _

/-- The augmented Hessian (14.3.9). The Lagrangian Hessian is evaluated
with the first-order multiplier estimate held fixed. -/
theorem fderiv_gradient_augmentedLagrangian_eq {f : G → ℝ} {c : G → F}
    (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c) (x : G) (y : F) (μ : ℝ) :
    fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x =
      fderiv ℝ (gradient (lagrangian f c (firstOrderMultiplier c y μ x))) x +
        μ⁻¹ • (fderiv ℝ c x).adjoint.comp (fderiv ℝ c x) := by
  let A := fderiv ℝ c
  let Adj : (G →L[ℝ] F) →L[ℝ] (F →L[ℝ] G) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  let yF := firstOrderMultiplier c y μ
  have hA : ContDiff ℝ 1 A := hc.fderiv_right (by norm_num)
  have hAdj : ContDiff ℝ 1 (fun z ↦ (A z).adjoint) := Adj.contDiff.comp hA
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  have hA' := (hAdj.differentiable one_ne_zero x).hasFDerivAt
  have hg' := (hg.differentiable one_ne_zero x).hasFDerivAt
  have hyF : HasFDerivAt yF (0 - μ⁻¹ • A x) x :=
    (hasFDerivAt_const y x).sub ((hc.differentiable (by norm_num) x).hasFDerivAt.const_smul μ⁻¹)
  have hp := (hg'.sub (hA'.clm_apply hyF)).congr_of_eventuallyEq
    (f₁ := gradient (augmentedLagrangian f c y μ)) (Eventually.of_forall fun z ↦
      gradient_augmentedLagrangian_eq (hf.differentiable (by norm_num) z)
        (hc.differentiable (by norm_num) z) y μ)
  have hL := (hg'.sub (hA'.clm_apply (hasFDerivAt_const (yF x) x))).congr_of_eventuallyEq
    (f₁ := gradient (lagrangian f c (yF x))) (Eventually.of_forall fun z ↦
      gradient_lagrangian_eq (hf.differentiable (by norm_num) z)
        (hc.differentiable (by norm_num) z) (yF x))
  rw [hp.fderiv, hL.fderiv]
  ext d
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, smul_apply, zero_sub, neg_apply, map_neg,
    map_zero, zero_add, map_smul, A]
  abel

/-- At an infeasible point the augmented Hessian can have an additional
term of order inverse penalty. For the scalar constraint in this example,
the scaled Hessian is three and the constraint Gram value is one.
Thus Lemma 14.3.2(ii)–(iii) needs a bounded Lagrangian-Hessian term. -/
theorem lemma_14_3_2_infeasible_counterexample {μ : ℝ} (hμ : 0 < μ) :
    let c : ℝ → ℝ := fun x ↦ 1 + x + x ^ 2
    μ * deriv (deriv (quadraticPenalty (fun _ ↦ 0) c μ)) 0 = 3 ∧
      (deriv c 0) ^ 2 = 1 := by
  let c : ℝ → ℝ := fun x ↦ 1 + x + x ^ 2
  have hc (x : ℝ) : HasDerivAt c (1 + 2 * x) x := by
    have h := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).add
      ((hasDerivAt_id x).pow 2)
    convert h using 1
    · rfl
    · simp [id]
  have hfirst : deriv (quadraticPenalty (fun _ ↦ 0) c μ) =
      fun x ↦ μ⁻¹ * (c x * (1 + 2 * x)) := by
    funext x
    have h := ((hc x).pow 2).const_mul ((2 * μ)⁻¹)
    have h' : HasDerivAt (quadraticPenalty (fun _ ↦ 0) c μ)
        (μ⁻¹ * (c x * (1 + 2 * x))) x := by
      convert h using 1
      · funext t
        simp [quadraticPenalty, Real.norm_eq_abs, sq_abs]
      · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_inv_rev]
        ring
    exact h'.deriv
  have hd : HasDerivAt (fun x : ℝ ↦ 1 + 2 * x) 2 0 := by
    simpa [id] using ((hasDerivAt_id (0 : ℝ)).const_mul 2).const_add 1
  have hsecond := ((hc 0).mul hd).const_mul μ⁻¹
  change μ * deriv (deriv (quadraticPenalty (fun _ ↦ 0) c μ)) 0 = 3 ∧
    (deriv c 0) ^ 2 = 1
  change HasDerivAt (fun x ↦ μ⁻¹ * (c x * (1 + 2 * x))) _ 0 at hsecond
  rw [hfirst, hsecond.deriv, (hc 0).deriv]
  simp [c]
  field_simp [hμ.ne']; norm_num

/-- Elimination of the auxiliary variable in (14.3.13)–(14.3.14).
The lower block fixes the auxiliary variable uniquely when the penalty
parameter is nonzero. -/
theorem penalty_system_iff (M : G →L[ℝ] G) (A : G →L[ℝ] F)
    (b s : G) (c : F) {μ : ℝ} (hμ : μ ≠ 0) :
    M s + μ⁻¹ • A.adjoint (A s) = b + μ⁻¹ • A.adjoint c ↔
      ∃ t : F, M s + A.adjoint t = b ∧ A s - μ • t = c := by
  have hsolve (t : F) (ht : A s - μ • t = c) : t = μ⁻¹ • (A s - c) := by
    have he : μ • t = A s - c := by rw [← ht, sub_sub_cancel]
    rw [← he, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hc : A s - μ • (μ⁻¹ • (A s - c)) = c := by
    rw [smul_smul, mul_inv_cancel₀ hμ, one_smul, sub_sub_cancel]
  constructor
  · intro h
    refine ⟨μ⁻¹ • (A s - c), ?_, hc⟩
    rw [map_smul, map_sub, smul_sub, ← add_sub_assoc, h, add_sub_cancel_right]
  · rintro ⟨t, h, ht⟩
    rw [hsolve t ht, map_smul, map_sub, smul_sub, ← add_sub_assoc] at h
    exact sub_eq_iff_eq_add.mp h

/-- Corrected (14.3.15). Changing only the penalty parameter changes the
gradient by the signed factor new inverse minus old inverse, multiplied
by the constraint contribution. -/
theorem gradient_augmentedLagrangian_change_parameter
    {f : G → ℝ} {c : G → F} {x : G} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (y : F) {μ ν : ℝ} (hμ : μ ≠ 0) :
    gradient (augmentedLagrangian f c y ν) x =
      gradient (augmentedLagrangian f c y μ) x +
        (μ / ν - 1) • (fderiv ℝ c x).adjoint (y - firstOrderMultiplier c y μ x) := by
  rw [gradient_augmentedLagrangian_eq hf hc, gradient_augmentedLagrangian_eq hf hc]
  have hscalar : (μ / ν - 1) * μ⁻¹ = ν⁻¹ - μ⁻¹ := by
    calc
      _ = (μ * μ⁻¹) * ν⁻¹ - μ⁻¹ := by rw [div_eq_mul_inv]; ring
      _ = _ := by rw [mul_inv_cancel₀ hμ, one_mul]
  simp only [firstOrderMultiplier, sub_sub_cancel, map_sub, map_smul, smul_smul]
  rw [hscalar, sub_smul]
  abel

open Subproblem in
omit [CompleteSpace G] in
/-- Corrected scaled eigenvalue estimates for Lemma 14.3.2(ii)–(iii).
A uniformly bounded Lagrangian Hessian gives a uniform error of order
the penalty parameter in the scaled extreme eigenvalues. -/
theorem lemma_14_3_2_scaled_extremes [FiniteDimensional ℝ G] [Nontrivial G]
    {P B H : G →L[ℝ] G} (hP : P.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {μ : ℝ} (hμ : 0 < μ) (hmodel : P = H + μ⁻¹ • B) :
    |μ * leftmost hP - leftmost hB| ≤ μ * ‖H‖ ∧
      |μ * rightmost hP - rightmost hB| ≤ μ * ‖H‖ := by
  have hunit (v : G) (hv : ‖v‖ = 1) : |μ * ⟪v, P v⟫ - ⟪v, B v⟫| ≤ μ * ‖H‖ := by
    have hb : |⟪v, H v⟫| ≤ ‖H‖ := by
      have h₁ := abs_real_inner_le_norm v (H v)
      have h₂ := H.le_opNorm v
      rw [hv, one_mul] at h₁
      rw [hv, mul_one] at h₂
      exact h₁.trans h₂
    have hmul : μ * (μ⁻¹ * ⟪v, B v⟫) = ⟪v, B v⟫ := by
      rw [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]
    have he : μ * ⟪v, P v⟫ - ⟪v, B v⟫ = μ * ⟪v, H v⟫ := by
      rw [hmodel, add_apply, smul_apply, inner_add_right, real_inner_smul_right]
      linarith only [hmul, mul_add μ ⟪v, H v⟫ (μ⁻¹ * ⟪v, B v⟫)]
    rw [he, abs_mul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left hb hμ.le
  have hleft (T : G →L[ℝ] G) (hT : T.toLinearMap.IsSymmetric) :
      ∃ v : G, ‖v‖ = 1 ∧ ⟪v, T v⟫ = leftmost hT := by
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hT)
    refine ⟨hT.eigenvectorBasis rfl i, (hT.eigenvectorBasis rfl).norm_eq_one i, ?_⟩
    rw [apply_eigenvectorBasis' (hH := hT), hi, real_inner_smul_right,
      real_inner_self_eq_norm_sq, (hT.eigenvectorBasis rfl).norm_eq_one, one_pow, mul_one]
  have hright (T : G →L[ℝ] G) (hT : T.toLinearMap.IsSymmetric) :
      ∃ v : G, ‖v‖ = 1 ∧ ⟪v, T v⟫ = rightmost hT := by
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_rightmost (hH := hT)
    refine ⟨hT.eigenvectorBasis rfl i, (hT.eigenvectorBasis rfl).norm_eq_one i, ?_⟩
    rw [apply_eigenvectorBasis' (hH := hT), hi, real_inner_smul_right,
      real_inner_self_eq_norm_sq, (hT.eigenvectorBasis rfl).norm_eq_one, one_pow, mul_one]
  obtain ⟨p, hp, hpl⟩ := hleft P hP
  obtain ⟨b, hb, hbl⟩ := hleft B hB
  obtain ⟨p', hp', hpr⟩ := hright P hP
  obtain ⟨b', hb', hbr⟩ := hright B hB
  constructor <;> apply abs_le.mpr
  · have h₁ := (abs_le.mp (hunit p hp)).1
    have h₂ := (abs_le.mp (hunit b hb)).2
    have hpB : leftmost hB ≤ ⟪p, B p⟫ := by
      simpa only [hp, one_pow, mul_one] using leftmost_mul_norm_sq_le (hH := hB) p
    have hbP : leftmost hP ≤ ⟪b, P b⟫ := by
      simpa only [hb, one_pow, mul_one] using leftmost_mul_norm_sq_le (hH := hP) b
    rw [hpl] at h₁
    rw [hbl] at h₂
    exact ⟨by linarith only [h₁, hpB],
      by linarith only [h₂, mul_le_mul_of_nonneg_left hbP hμ.le]⟩
  · have h₁ := (abs_le.mp (hunit b' hb')).1
    have h₂ := (abs_le.mp (hunit p' hp')).2
    have hbP : ⟪b', P b'⟫ ≤ rightmost hP := by
      simpa only [hb', one_pow, mul_one] using inner_le_rightmost_mul_norm_sq (hH := hP) b'
    have hpB : ⟪p', B p'⟫ ≤ rightmost hB := by
      simpa only [hp', one_pow, mul_one] using inner_le_rightmost_mul_norm_sq (hH := hB) p'
    rw [hbr] at h₁
    rw [hpr] at h₂
    exact ⟨by linarith only [h₁, mul_le_mul_of_nonneg_left hbP hμ.le],
      by linarith only [h₂, hpB]⟩

end ConnGouldToint.Chapter14
