/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter14.Section02
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Numlib.Optimization.Subproblem.Secular

/-! # Quadratic penalty convergence -/

open Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter14

variable {G F : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A run of Algorithm 14.3.1. The starting points of the inner solves,
and the choices of iterates and tolerances, are supplied by the run. -/
structure QuadraticPenaltyRun (f : G → ℝ) (c : G → F) (y : F) where
  start : ℕ → G
  iterate : ℕ → G
  parameter : ℕ → ℝ
  tolerance : ℕ → ℝ
  parameter_pos : ∀ k, 0 < parameter k
  parameter_tendsto : Tendsto parameter atTop (𝓝 0)
  tolerance_tendsto : Tendsto tolerance atTop (𝓝 0)
  residual_le : ∀ k,
    ‖fderiv ℝ (augmentedLagrangian f c y (parameter k)) (iterate k)‖ ≤ tolerance k

/-- The multiplier estimate reported after each inner solve of Algorithm 14.3.1. -/
noncomputable def QuadraticPenaltyRun.multiplier {f : G → ℝ} {c : G → F} {y : F}
    (run : QuadraticPenaltyRun f c y) (k : ℕ) : F :=
  firstOrderMultiplier c y (run.parameter k) (run.iterate k)

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

open Subproblem in
omit [CompleteSpace G] in
/-- Limit form of the corrected Lemma 14.3.2(ii)–(iii). Multiplying the
error in either eigenvalue by the penalty parameter makes it tend to zero. -/
theorem lemma_14_3_2_scaled_limits [FiniteDimensional ℝ G] [Nontrivial G]
    {ι : Type*} {l : Filter ι} {μ : ι → ℝ} {P H : ι → G →L[ℝ] G}
    {B : G →L[ℝ] G} (hP : ∀ i, (P i).toLinearMap.IsSymmetric)
    (hB : B.toLinearMap.IsSymmetric) (hμ : Tendsto μ l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < μ i) (C : ℝ) (hbound : ∀ᶠ i in l, ‖H i‖ ≤ C)
    (hmodel : ∀ᶠ i in l, P i = H i + (μ i)⁻¹ • B) :
    Tendsto (fun i ↦ μ i * leftmost (hP i)) l (𝓝 (leftmost hB)) ∧
      Tendsto (fun i ↦ μ i * rightmost (hP i)) l (𝓝 (rightmost hB)) := by
  have hb := hμ.mul_const C
  rw [zero_mul] at hb
  have he := hpos.and (hbound.and hmodel)
  constructor
  · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall
      fun _ ↦ norm_nonneg _) ?_ hb)
    filter_upwards [he] with i hi
    rw [Real.norm_eq_abs]
    exact (lemma_14_3_2_scaled_extremes (hP i) hB hi.1 hi.2.2).1.trans
      (mul_le_mul_of_nonneg_left hi.2.1 hi.1.le)
  · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall
      fun _ ↦ norm_nonneg _) ?_ hb)
    filter_upwards [he] with i hi
    rw [Real.norm_eq_abs]
    exact (lemma_14_3_2_scaled_extremes (hP i) hB hi.1 hi.2.2).2.trans
      (mul_le_mul_of_nonneg_left hi.2.1 hi.1.le)

omit [CompleteSpace F] in
/-- Lemma 14.3.2(iv). With a zero-dimensional constraint space the penalty
Hessian is exactly the objective Hessian. -/
theorem lemma_14_3_2_iv [Subsingleton F] (f : G → ℝ) (c : G → F)
    (x : G) (y : F) (μ : ℝ) :
    fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x = fderiv ℝ (gradient f) x := by
  congr 2
  funext z
  simp [augmentedLagrangian, lagrangian, Subsingleton.elim (c z) 0]

section ReducedHessian

variable [FiniteDimensional ℝ G] (A : G →L[ℝ] F)

/-- The restriction of the Hessian quadratic form to the constraint nullspace,
represented by its symmetric compression to the kernel subspace. -/
noncomputable def reducedPenaltyHessian (H : G →L[ℝ] G) :
    A.toLinearMap.ker →L[ℝ] A.toLinearMap.ker :=
  let N := A.toLinearMap.ker.subtypeL
  N.adjoint.comp (H.comp N)

omit [CompleteSpace F] [FiniteDimensional ℝ G] in
/-- Compressing a symmetric Hessian to the constraint kernel preserves symmetry. -/
theorem reducedPenaltyHessian_symmetric {H : G →L[ℝ] G} (hH : H.toLinearMap.IsSymmetric) :
    (reducedPenaltyHessian A H).toLinearMap.IsSymmetric := by
  intro v w
  change ⟪(A.toLinearMap.ker.subtypeL.adjoint) (H v), w⟫ =
    ⟪v, (A.toLinearMap.ker.subtypeL.adjoint) (H w)⟫
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact hH v w

open Subproblem in
/-- Corrected Lemma 14.3.2(i) for a fixed Lagrangian Hessian. A positive
penalty forces the minimum-Rayleigh directions into the constraint kernel
in the limit. The compression uses the entire kernel. -/
theorem lemma_14_3_2_i [Nontrivial G] [Nontrivial A.toLinearMap.ker]
    {H : G →L[ℝ] G} (hH : H.toLinearMap.IsSymmetric)
    (hP : ∀ μ : ℝ, (H + μ⁻¹ • A.adjoint.comp A).toLinearMap.IsSymmetric) :
    Tendsto (fun μ ↦ leftmost (hP μ)) (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (leftmost (reducedPenaltyHessian_symmetric A hH))) := by
  let R := reducedPenaltyHessian A H
  let hR := reducedPenaltyHessian_symmetric A hH
  let lamMin := leftmost hR
  let q : G → ℝ := fun v ↦ ⟪v, H v⟫
  have hq : Continuous q := continuous_id.inner H.continuous
  have hkernel (v : A.toLinearMap.ker) : ⟪v, R v⟫ = q v := by
    exact ContinuousLinearMap.adjoint_inner_right A.toLinearMap.ker.subtypeL v (H v)
  have hquad (μ : ℝ) (v : G) :
      ⟪v, (H + μ⁻¹ • A.adjoint.comp A) v⟫ = q v + μ⁻¹ * ‖A v‖ ^ 2 := by
    rw [add_apply, smul_apply, inner_add_right, real_inner_smul_right,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq]
  have hmin (v : G) (hv : A v = 0) (hunit : ‖v‖ = 1) : lamMin ≤ q v := by
    let v' : A.toLinearMap.ker := ⟨v, hv⟩
    have h := leftmost_mul_norm_sq_le (hH := hR) v'
    rw [hkernel, show ‖v'‖ = 1 from hunit, one_pow, mul_one] at h
    exact h
  have hupper (μ : ℝ) : leftmost (hP μ) ≤ lamMin := by
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hR)
    let v := hR.eigenvectorBasis rfl i
    have hv : ‖(v : G)‖ = 1 := (hR.eigenvectorBasis rfl).norm_eq_one i
    have hker : A (v : G) = 0 := v.property
    have hvalue : q v = lamMin := by
      rw [← hkernel, show R v = lamMin • v from (apply_eigenvectorBasis' (hH := hR) i).trans
        (congrArg (fun t : ℝ ↦ t • v) hi), real_inner_smul_right, real_inner_self_eq_norm_sq,
        show ‖v‖ = 1 from hv, one_pow, mul_one]
    have h := leftmost_mul_norm_sq_le (hH := hP μ) (v : G)
    rw [hv, one_pow, mul_one, hquad, hker, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero, hvalue] at h
    exact h
  have hlarge (ε : ℝ) (hε : 0 < ε) :
      ∃ δ > 0, ∀ μ ∈ Set.Ioo 0 δ, lamMin - ε ≤ leftmost (hP μ) := by
    let S := Metric.sphere (0 : G) 1 ∩ {v | q v ≤ lamMin - ε}
    have hS : IsCompact S := (isCompact_sphere _ _).inter_right
      (isClosed_le hq continuous_const)
    have hSunit (v : G) (hv : v ∈ S) : ‖v‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hv.1
    have hbound (μ : ℝ) (hμ : 0 < μ) (v : G) (hv : ‖v‖ = 1)
        (h : v ∉ S) : lamMin - ε ≤ ⟪v, (H + μ⁻¹ • A.adjoint.comp A) v⟫ := by
      have hqv : lamMin - ε ≤ q v := by
        by_contra! hn
        exact h ⟨by simpa [Metric.mem_sphere, dist_zero_right] using hv, hn.le⟩
      rw [hquad]
      exact hqv.trans (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hμ.le) (sq_nonneg _)))
    have hRayleigh (μ : ℝ) (h :
        ∀ v : G, ‖v‖ = 1 → lamMin - ε ≤ ⟪v, (H + μ⁻¹ • A.adjoint.comp A) v⟫) :
        lamMin - ε ≤ leftmost (hP μ) := by
      obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hP μ)
      let v := (hP μ).eigenvectorBasis rfl i
      have hv : ‖v‖ = 1 := ((hP μ).eigenvectorBasis rfl).norm_eq_one i
      have hv' := h v hv
      rw [show (H + μ⁻¹ • A.adjoint.comp A) v = leftmost (hP μ) • v from
        (apply_eigenvectorBasis' (hH := hP μ) i).trans (congrArg (fun t : ℝ ↦ t • v) hi),
        real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one] at hv'
      exact hv'
    by_cases hne : S.Nonempty
    · obtain ⟨w, hw, hwmin⟩ := hS.exists_isMinOn hne
        ((A.continuous.norm.pow 2).continuousOn)
      let d := ‖A w‖ ^ 2
      have hd : 0 < d := by
        have hAw : A w ≠ 0 := fun he ↦ by
          have h₁ := hmin w he (hSunit w hw)
          have h₂ : q w ≤ lamMin - ε := hw.2
          linarith
        exact sq_pos_of_pos (norm_pos_iff.mpr hAw)
      let C := |lamMin - ε| + ‖H‖ + 1
      have hC : 0 < C := by dsimp [C]; positivity
      refine ⟨d / C, div_pos hd hC, fun μ hμ ↦ hRayleigh μ ?_⟩
      intro v hv
      by_cases hvs : v ∈ S
      · have hlow : -‖H‖ ≤ q v := by
          have hi := (abs_le.mp (abs_real_inner_le_norm v (H v))).1
          have hop := H.le_opNorm v
          rw [hv, one_mul] at hi
          rw [hv, mul_one] at hop
          change -‖H‖ ≤ ⟪v, H v⟫
          linarith
        have hprod : C * μ ≤ d := by
          have := (lt_div_iff₀ hC).mp hμ.2
          linarith
        have hdC : C ≤ μ⁻¹ * ‖A v‖ ^ 2 := by
          rw [inv_mul_eq_div, le_div_iff₀ hμ.1]
          exact hprod.trans (hwmin hvs)
        rw [hquad]
        dsimp [C] at hdC
        linarith only [hlow, hdC, le_abs_self (lamMin - ε)]
      · exact hbound μ hμ.1 v hv hvs
    · exact ⟨1, zero_lt_one, fun μ hμ ↦
        hRayleigh μ fun v hv ↦ hbound μ hμ.1 v hv (fun h ↦ hne ⟨v, h⟩)⟩
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδbound⟩ := hlarge (ε / 2) (half_pos hε)
  have hev : ∀ᶠ μ : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0, μ ∈ Set.Ioo 0 δ := by
    have hup := (eventually_lt_nhds hδ).filter_mono
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0)
    filter_upwards [self_mem_nhdsWithin, hup] with μ hlo hhi
    exact ⟨hlo, hhi⟩
  filter_upwards [hev] with μ hμ
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hupper μ, hδbound μ hμ]

end ReducedHessian

private theorem symmetric_fderiv_gradient {f : G → ℝ} (hf : ContDiff ℝ 2 f) (x : G) :
    (fderiv ℝ (gradient f) x).toLinearMap.IsSymmetric := by
  let J := (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ f)).differentiable one_ne_zero x
  have h := J.hasFDerivAt.comp x hd.hasFDerivAt
  change HasFDerivAt (gradient f) _ _ at h
  have hs := hf.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)
  intro v w
  change ⟪fderiv ℝ (gradient f) x v, w⟫ = ⟪v, fderiv ℝ (gradient f) x w⟫
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← real_inner_comm v]
  change ⟪(InnerProductSpace.toDual ℝ G).symm (fderiv ℝ (fderiv ℝ f) x v), w⟫ =
    ⟪(InnerProductSpace.toDual ℝ G).symm (fderiv ℝ (fderiv ℝ f) x w), v⟫
  simpa only [InnerProductSpace.toDual_symm_apply] using hs.eq v w

private theorem symmetric_penalty_gram (A : G →L[ℝ] F) :
    (A.adjoint.comp A).toLinearMap.IsSymmetric := by
  intro v w
  change ⟪A.adjoint (A v), w⟫ = ⟪v, A.adjoint (A w)⟫
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

open Subproblem in
omit [CompleteSpace G] in
private theorem leftmost_congr [FiniteDimensional ℝ G] {P M : G →L[ℝ] G}
    (he : P = M) (hP : P.toLinearMap.IsSymmetric) (hM : M.toLinearMap.IsSymmetric) :
    leftmost hP = leftmost hM := by
  subst M
  rfl

open Subproblem in
/-- At a feasible point the multiplier in the penalty Hessian equals the
fixed multiplier, so the corrected Lemma 14.3.2(i) applies directly. -/
theorem lemma_14_3_2_i_of_feasible [FiniteDimensional ℝ G] [Nontrivial G]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {x : G} (hcx : c x = 0) (y : F) [Nontrivial (fderiv ℝ c x).toLinearMap.ker] :
    let A := fderiv ℝ c x
    let H := fderiv ℝ (gradient (lagrangian f c y)) x
    ∃ (hH : H.toLinearMap.IsSymmetric)
      (hP : ∀ μ : ℝ, (fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x).toLinearMap.IsSymmetric),
      Tendsto (fun μ ↦ leftmost (hP μ)) (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 (leftmost (reducedPenaltyHessian_symmetric A hH))) := by
  let A := fderiv ℝ c x
  let H := fderiv ℝ (gradient (lagrangian f c y)) x
  have hL : ContDiff ℝ 2 (lagrangian f c y) := hf.sub (contDiff_const.inner ℝ hc)
  have hH : H.toLinearMap.IsSymmetric := symmetric_fderiv_gradient hL x
  have hM (μ : ℝ) : (H + μ⁻¹ • A.adjoint.comp A).toLinearMap.IsSymmetric :=
    hH.add ((symmetric_penalty_gram A).smul rfl)
  have he (μ : ℝ) :
      fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x = H + μ⁻¹ • A.adjoint.comp A := by
    simpa [firstOrderMultiplier, hcx, H, A] using
      fderiv_gradient_augmentedLagrangian_eq hf hc x y μ
  have hP (μ : ℝ) :
      (fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x).toLinearMap.IsSymmetric :=
    he μ ▸ hM μ
  refine ⟨hH, hP, ?_⟩
  have hfun : (fun μ ↦ leftmost (hP μ)) = fun μ ↦ leftmost (hM μ) := by
    funext μ
    exact leftmost_congr (he μ) (hP μ) (hM μ)
  rw [hfun]
  exact lemma_14_3_2_i A hH hM

open Subproblem in
/-- The scaled limits of Lemma 14.3.2(ii)–(iii) at a fixed feasible point.
Here the first-order multiplier correction vanishes for every parameter. -/
theorem lemma_14_3_2_scaled_limits_of_feasible [FiniteDimensional ℝ G] [Nontrivial G]
    {f : G → ℝ} {c : G → F} (hf : ContDiff ℝ 2 f) (hc : ContDiff ℝ 2 c)
    {x : G} (hcx : c x = 0) (y : F) :
    let A := fderiv ℝ c x
    ∃ (hB : (A.adjoint.comp A).toLinearMap.IsSymmetric)
      (hP : ∀ μ : ℝ, (fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x).toLinearMap.IsSymmetric),
      Tendsto (fun μ ↦ μ * leftmost (hP μ)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (leftmost hB)) ∧
        Tendsto (fun μ ↦ μ * rightmost (hP μ)) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (rightmost hB)) := by
  let A := fderiv ℝ c x
  let H := fderiv ℝ (gradient (lagrangian f c y)) x
  have hB := symmetric_penalty_gram A
  have hL : ContDiff ℝ 2 (lagrangian f c y) := hf.sub (contDiff_const.inner ℝ hc)
  have hH : H.toLinearMap.IsSymmetric := symmetric_fderiv_gradient hL x
  have he (μ : ℝ) :
      fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x = H + μ⁻¹ • A.adjoint.comp A := by
    simpa [firstOrderMultiplier, hcx, H, A] using
      fderiv_gradient_augmentedLagrangian_eq hf hc x y μ
  have hP (μ : ℝ) :
      (fderiv ℝ (gradient (augmentedLagrangian f c y μ)) x).toLinearMap.IsSymmetric :=
    he μ ▸ hH.add (hB.smul rfl)
  refine ⟨hB, hP, lemma_14_3_2_scaled_limits hP hB (Filter.tendsto_id'.mpr nhdsWithin_le_nhds)
    self_mem_nhdsWithin ‖H‖ (Eventually.of_forall fun _ ↦ le_rfl)
    (Eventually.of_forall he)⟩

end ConnGouldToint.Chapter14
