/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Composite objective functions -/

open Filter Topology ContinuousLinearMap

namespace ConnGouldToint.Chapter08

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The outer objective evaluated on the graph of the inner objective or model. -/
def compositeObjective (f₀ : E × F → ℝ) (u : E → F) (x : E) : ℝ := f₀ (x, u x)

/-- The first derivative of a composite objective. -/
theorem fderiv_compositeObjective {f₀ : E × F → ℝ} {u : E → F} {x : E}
    (hf : DifferentiableAt ℝ f₀ (x, u x)) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (compositeObjective f₀ u) x =
      (fderiv ℝ f₀ (x, u x)).comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ u x)) := by
  change fderiv ℝ (f₀ ∘ fun z => (id z, u z)) x = _
  exact (hf.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hu.hasFDerivAt)).fderiv

/-- The Hessian chain rule in graph coordinates. The two graph tangent
arguments generate the four second-derivative terms of the outer function. -/
theorem second_fderiv_compositeObjective {f₀ : E × F → ℝ} {u : E → F}
    (hf : ContDiff ℝ 2 f₀) (hu : ContDiff ℝ 2 u) (x v w : E) :
    fderiv ℝ (fderiv ℝ (compositeObjective f₀ u)) x v w =
      fderiv ℝ (fderiv ℝ f₀) (x, u x) (v, fderiv ℝ u x v) (w, fderiv ℝ u x w) +
      fderiv ℝ f₀ (x, u x) (0, fderiv ℝ (fderiv ℝ u) x v w) := by
  have hdF := (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
    (by norm_num)
  have hdU := (hu.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
    (by norm_num)
  have hu' := hu.differentiable (by norm_num)
  have hf' := hf.differentiable (by norm_num)
  let c := fun z : E => fderiv ℝ f₀ (z, u z)
  let d := fun z : E => (w, fderiv ℝ u z w)
  have hfun : (fun z => fderiv ℝ (compositeObjective f₀ u) z w) = fun z => c z (d z) := by
    funext z
    rw [fderiv_compositeObjective (hf' _) (hu' _)]
    rfl
  have hc : HasFDerivAt c
      ((fderiv ℝ (fderiv ℝ f₀) (x, u x)).comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ u x))) x :=
    (hdF _).hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk (hu' x).hasFDerivAt)
  have hd : HasFDerivAt d
      ((0 : E →L[ℝ] E).prod
        ((ContinuousLinearMap.apply ℝ F w).comp (fderiv ℝ (fderiv ℝ u) x))) x :=
    (hasFDerivAt_const w x).prodMk ((ContinuousLinearMap.apply ℝ F w).hasFDerivAt.comp x
      (hdU x).hasFDerivAt)
  have hcomp : ContDiff ℝ 2 (compositeObjective f₀ u) :=
    hf.comp (contDiff_id.prodMk hu)
  have hh := ((hcomp.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
    (by norm_num) x).hasFDerivAt
  have hev := ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x hh).fderiv
  have heval := (hc.clm_apply hd).fderiv
  change fderiv ℝ (fun z => fderiv ℝ (compositeObjective f₀ u) z w) x = _ at hev
  rw [hfun, heval] at hev
  have h := DFunLike.congr_fun hev v
  exact (add_comm _ _).trans h |>.symm

/-- The smoothness requirements on the objective and model follow from
twice continuous differentiability of the two constituent functions. -/
theorem theorem_8_5_1_smooth {f₀ : E × F → ℝ} {u : E → F}
    (hf : ContDiff ℝ 2 f₀) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 2 (compositeObjective f₀ u) :=
  hf.comp (contDiff_id.prodMk hu)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- A global lower bound on the outer objective is preserved on every graph. -/
theorem theorem_8_5_1_lower {f₀ : E × F → ℝ} (u : E → F)
    (hf : BddBelow (Set.range f₀)) : BddBelow (Set.range (compositeObjective f₀ u)) :=
  hf.mono (show Set.range (compositeObjective f₀ u) ⊆ Set.range f₀ from
    fun _ ⟨x, hx⟩ => ⟨(x, u x), hx⟩)

/-- Uniform bounds on the outer Hessian, the inner Hessian, the inner
derivative and the outer partial derivative in the inner variable give
a uniform composite Hessian bound. The estimate is pointwise, so the
same constants apply on every trust region. -/
theorem theorem_8_5_1_hessian {f₀ : E × F → ℝ} {u : E → F}
    (hf : ContDiff ℝ 2 f₀) (hu : ContDiff ℝ 2 u) (x : E)
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hff : ‖fderiv ℝ (fderiv ℝ f₀) (x, u x)‖ ≤ A)
    (huu : ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B)
    (hd : ‖fderiv ℝ u x‖ ≤ C)
    (hpartial : ∀ z, |fderiv ℝ f₀ (x, u x) (0, z)| ≤ D * ‖z‖) :
    ‖fderiv ℝ (fderiv ℝ (compositeObjective f₀ u)) x‖ ≤ A * (max 1 C) ^ 2 + D * B := by
  let C' := max 1 C
  have hC' : 0 ≤ C' := zero_le_one.trans (le_max_left _ _)
  have hgraph (v : E) : ‖(v, fderiv ℝ u x v)‖ ≤ C' * ‖v‖ := by
    apply norm_prod_le_iff.mpr
    exact ⟨le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _),
      ((fderiv ℝ u x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hd.trans (le_max_right _ _)) (norm_nonneg _))⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [second_fderiv_compositeObjective hf hu]
  have h₁ : |fderiv ℝ (fderiv ℝ f₀) (x, u x) (v, fderiv ℝ u x v)
      (w, fderiv ℝ u x w)| ≤ A * (C' * ‖v‖) * (C' * ‖w‖) := by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ (fderiv ℝ f₀) (x, u x) (v, fderiv ℝ u x v)).le_opNorm _).trans ?_
    refine mul_le_mul ?_ (hgraph w) (norm_nonneg _) (by positivity)
    exact ((fderiv ℝ (fderiv ℝ f₀) (x, u x)).le_opNorm _).trans
      (mul_le_mul hff (hgraph v) (norm_nonneg _) hA)
  have h₂ : |fderiv ℝ f₀ (x, u x) (0, fderiv ℝ (fderiv ℝ u) x v w)| ≤
      D * (B * ‖v‖ * ‖w‖) := by
    refine (hpartial _).trans (mul_le_mul_of_nonneg_left ?_ hD)
    exact ((fderiv ℝ (fderiv ℝ u) x v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right
        (((fderiv ℝ (fderiv ℝ u) x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right huu (norm_nonneg _))) (norm_nonneg _))
  rw [Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq ?_)
  change _ = (A * C' ^ 2 + D * B) * ‖v‖ * ‖w‖
  ring

/-- Matching the value and first derivative of the inner model at a center
preserves both agreements after outer composition. -/
theorem theorem_8_5_1_agreement {f₀ : E × F → ℝ} {u m : E → F} {x : E}
    (hf : DifferentiableAt ℝ f₀ (x, u x)) (hu : DifferentiableAt ℝ u x)
    (hm : DifferentiableAt ℝ m x) (hval : m x = u x) (hderiv : fderiv ℝ m x = fderiv ℝ u x) :
    compositeObjective f₀ m x = compositeObjective f₀ u x ∧
      fderiv ℝ (compositeObjective f₀ m) x = fderiv ℝ (compositeObjective f₀ u) x := by
  have hfm : DifferentiableAt ℝ f₀ (x, m x) := by simpa only [hval] using hf
  constructor
  · simp only [compositeObjective, hval]
  · rw [fderiv_compositeObjective hfm hm, fderiv_compositeObjective hf hu, hval, hderiv]

/-- Under center value and derivative agreement, the composite Hessian error
comes entirely from the inner Hessian error multiplied by the outer partial
derivative. A uniform bound on that derivative transfers AM.5. -/
theorem theorem_8_5_2_hessian_agreement {f₀ : E × F → ℝ} {u : E → F}
    {m : ℕ → E → F} {x : ℕ → E} {D : ℝ} (hD : 0 ≤ D)
    (hf : ContDiff ℝ 2 f₀) (hu : ContDiff ℝ 2 u) (hm : ∀ k, ContDiff ℝ 2 (m k))
    (hval : ∀ k, m k (x k) = u (x k))
    (hderiv : ∀ k, fderiv ℝ (m k) (x k) = fderiv ℝ u (x k))
    (hpartial : ∀ k z, |fderiv ℝ f₀ (x k, u (x k)) (0, z)| ≤ D * ‖z‖)
    (hinner : Tendsto (fun k => ‖fderiv ℝ (fderiv ℝ u) (x k) -
      fderiv ℝ (fderiv ℝ (m k)) (x k)‖) atTop (𝓝 0)) :
    Tendsto (fun k => ‖fderiv ℝ (fderiv ℝ (compositeObjective f₀ u)) (x k) -
      fderiv ℝ (fderiv ℝ (compositeObjective f₀ (m k))) (x k)‖) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using (tendsto_const_nhds (x := D)).mul hinner)
    (fun _ => norm_nonneg _) ?_
  intro k
  let Q := fderiv ℝ (fderiv ℝ u) (x k) - fderiv ℝ (fderiv ℝ (m k)) (x k)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hD (norm_nonneg Q))
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hD (norm_nonneg Q)) (norm_nonneg _))
  intro w
  simp only [sub_apply, second_fderiv_compositeObjective hf hu,
    second_fderiv_compositeObjective hf (hm k), hval k, hderiv k]
  rw [add_sub_add_left_eq_sub]
  have he : fderiv ℝ f₀ (x k, u (x k)) (0, fderiv ℝ (fderiv ℝ u) (x k) v w) -
      fderiv ℝ f₀ (x k, u (x k)) (0, fderiv ℝ (fderiv ℝ (m k)) (x k) v w) =
      fderiv ℝ f₀ (x k, u (x k)) (0, Q v w) := by
    rw [← map_sub]
    simp [Q]
  rw [he, Real.norm_eq_abs]
  have hQ : ‖Q v w‖ ≤ ‖Q‖ * ‖v‖ * ‖w‖ :=
    ((Q v).le_opNorm w).trans (mul_le_mul_of_nonneg_right (Q.le_opNorm v) (norm_nonneg _))
  calc
    _ ≤ D * ‖Q v w‖ := hpartial k _
    _ ≤ D * (‖Q‖ * ‖v‖ * ‖w‖) := mul_le_mul_of_nonneg_left hQ hD
    _ = _ := by ring

/-- The uniform Lipschitz conclusion in Theorem 8.5.2(ii) fails even for
polynomials. The outer function is independent of the explicit (x) argument.
Both constituent second derivatives are constant, and both first derivatives
are bounded by two on the model graphs. The composite second derivatives have
Lipschitz constants growing at least linearly in the iteration index. -/
theorem theorem_8_5_2_lipschitz_counterexample :
    let f : ℝ → ℝ := fun z => z ^ 2
    let m : ℕ → ℝ → ℝ := fun k x => ((k : ℝ) + 1) * x ^ 2
    let B : ℕ → Set ℝ := fun k => Metric.closedBall 0 (((k : ℝ) + 1)⁻¹)
    (∀ x, deriv (deriv f) x = 2) ∧
    (∀ k x, deriv (deriv (m k)) x = 2 * ((k : ℝ) + 1)) ∧
    (∀ k x, x ∈ B k → |deriv (m k) x| ≤ 2 ∧ |deriv f (m k x)| ≤ 2) ∧
    ¬ ∃ L : ℝ, ∀ k x, x ∈ B k → ∀ y, y ∈ B k →
      |deriv (deriv (f ∘ m k)) x - deriv (deriv (f ∘ m k)) y| ≤ L * |x - y| := by
  dsimp only
  have hquad (a : ℝ) : deriv (fun x => a * x ^ 2) = fun x => 2 * a * x := by
    funext x
    rw [deriv_const_mul_field, deriv_pow_field]
    norm_num
    ring
  have hcomp (a : ℝ) :
      deriv (deriv ((fun z : ℝ => z ^ 2) ∘ fun x => a * x ^ 2)) =
        fun x => 12 * a ^ 2 * x ^ 2 := by
    have he : ((fun z : ℝ => z ^ 2) ∘ fun x => a * x ^ 2) =
        fun x => a ^ 2 * x ^ 4 := by funext x; dsimp; ring
    rw [he]
    have hd : deriv (fun x => a ^ 2 * x ^ 4) = fun x => (4 * a ^ 2) * x ^ 3 := by
      funext x
      rw [deriv_const_mul_field, deriv_pow_field]
      norm_num
      ring
    rw [hd]
    funext x
    rw [deriv_const_mul_field, deriv_pow_field]
    norm_num
    ring
  have hf : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
    simpa only [one_mul, mul_one] using hquad 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [hf, deriv_const_mul_id]
  · intro k x
    rw [hquad, deriv_const_mul_id]
  · intro k x hx
    let a : ℝ := (k : ℝ) + 1
    have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have ha₀ : 0 < a := zero_lt_one.trans_le ha
    have hb : |x| ≤ a⁻¹ := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
    have hx₁ : |x| ≤ 1 := hb.trans (inv_le_one_of_one_le₀ ha)
    constructor
    · rw [hquad, abs_mul, abs_mul, abs_of_nonneg ha₀.le, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h := mul_le_mul_of_nonneg_left hb ha₀.le
      rw [mul_inv_cancel₀ ha₀.ne'] at h
      linarith
    · rw [hf, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (mul_nonneg ha₀.le (sq_nonneg _))]
      have hs : a * x ^ 2 ≤ 1 := calc
        _ = a * (|x| * |x|) := by rw [← pow_two, sq_abs]
        _ ≤ a * |x| := by
          gcongr
          exact mul_le_of_le_one_right (abs_nonneg _) hx₁
        _ ≤ a * a⁻¹ := mul_le_mul_of_nonneg_left hb ha₀.le
        _ = 1 := mul_inv_cancel₀ ha₀.ne'
      linarith
  · rintro ⟨L, hL⟩
    obtain ⟨k, hk⟩ := exists_nat_gt L
    let a : ℝ := (k : ℝ) + 1
    have ha : 0 < a := by dsimp [a]; positivity
    have h0 : (0 : ℝ) ∈ Metric.closedBall 0 a⁻¹ :=
      Metric.mem_closedBall_self (inv_nonneg.mpr ha.le)
    have h1 : a⁻¹ ∈ Metric.closedBall (0 : ℝ) a⁻¹ := by
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero,
        abs_of_nonneg (inv_nonneg.mpr ha.le), le_rfl]
    have h := hL k a⁻¹ h1 0 h0
    rw [hcomp] at h
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at h
    change |12 * a ^ 2 * (a⁻¹) ^ 2| ≤ L * |a⁻¹| at h
    rw [abs_of_nonneg (by positivity : 0 ≤ 12 * a ^ 2 * (a⁻¹) ^ 2),
      abs_of_nonneg (inv_nonneg.mpr ha.le)] at h
    have he : 12 * a ^ 2 * (a⁻¹) ^ 2 = 12 := by field_simp [ha.ne']
    rw [he, ← div_eq_mul_inv] at h
    have := (le_div_iff₀ ha).mp h
    dsimp [a] at this
    linarith [Nat.cast_nonneg (α := ℝ) k]

private theorem norm_apply₂_le {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : X →L[ℝ] Y →L[ℝ] Z) (v : X) (w : Y) :
    ‖A v w‖ ≤ ‖A‖ * ‖v‖ * ‖w‖ :=
  ((A v).le_opNorm w).trans (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _))

/-- Corrected Theorem 8.5.2(ii). Uniform bounds on both constituent Hessians,
in addition to their Lipschitz constants, control the terms in which the
first derivatives vary. The convex set T contains the graph over S. -/
theorem theorem_8_5_2_lipschitz {f₀ : E × F → ℝ} {u : E → F}
    (hf : ContDiff ℝ 2 f₀) (hu : ContDiff ℝ 2 u) {S : Set E} {T : Set (E × F)}
    (hS : Convex ℝ S) (hT : Convex ℝ T) (hmem : ∀ x ∈ S, (x, u x) ∈ T)
    {A B C D Lf Lu : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hLf : 0 ≤ Lf) (hLu : 0 ≤ Lu)
    (hff : ∀ z ∈ T, ‖fderiv ℝ (fderiv ℝ f₀) z‖ ≤ A)
    (huu : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ B)
    (hd : ∀ z ∈ S, ‖fderiv ℝ u z‖ ≤ C)
    (hpartial : ∀ z ∈ T, ∀ a, |fderiv ℝ f₀ z (0, a)| ≤ D * ‖a‖)
    (hflip : ∀ x ∈ T, ∀ y ∈ T, ‖fderiv ℝ (fderiv ℝ f₀) x -
      fderiv ℝ (fderiv ℝ f₀) y‖ ≤ Lf * ‖x - y‖)
    (hulip : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ u) x -
      fderiv ℝ (fderiv ℝ u) y‖ ≤ Lu * ‖x - y‖)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖fderiv ℝ (fderiv ℝ (compositeObjective f₀ u)) x -
      fderiv ℝ (fderiv ℝ (compositeObjective f₀ u)) y‖ ≤
      (Lf * (max 1 C) ^ 3 + 3 * A * B * max 1 C + D * Lu) * ‖x - y‖ := by
  let M := max 1 C
  have hM : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
  let X := (x, u x)
  let Y := (y, u y)
  let d := ‖x - y‖
  let K := Lf * M ^ 3 + 3 * A * B * M + D * Lu
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hnorm (z : E) (hz : z ∈ S) (v : E) : ‖(v, fderiv ℝ u z v)‖ ≤ M * ‖v‖ :=
    norm_prod_le_iff.mpr ⟨le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _),
      ((fderiv ℝ u z).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((hd z hz).trans (le_max_right _ _)) (norm_nonneg _))⟩
  have hU : ‖u x - u y‖ ≤ C * d :=
    hS.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hu.differentiable (by norm_num) z) hd hy hx
  have hXY : ‖X - Y‖ ≤ M * d :=
    norm_prod_le_iff.mpr ⟨le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _),
      hU.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩
  have hdu : ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ B * d :=
    hS.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable
        (by norm_num) z) huu hy hx
  have hdf : ‖fderiv ℝ f₀ X - fderiv ℝ f₀ Y‖ ≤ A * (M * d) :=
    (hT.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable
        (by norm_num) z) hff (hmem y hy) (hmem x hx)).trans (mul_le_mul_of_nonneg_left hXY hA)
  change _ ≤ K * d
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (norm_nonneg _))
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hK (norm_nonneg _)) (norm_nonneg _))
  intro w
  let Vx := (v, fderiv ℝ u x v)
  let Vy := (v, fderiv ℝ u y v)
  let Wx := (w, fderiv ℝ u x w)
  let Wy := (w, fderiv ℝ u y w)
  let Fx := fderiv ℝ (fderiv ℝ f₀) X
  let Fy := fderiv ℝ (fderiv ℝ f₀) Y
  let Ux := fderiv ℝ (fderiv ℝ u) x
  let Uy := fderiv ℝ (fderiv ℝ u) y
  have hgraphdiff (z : E) :
      ‖(z, fderiv ℝ u x z) - (z, fderiv ℝ u y z)‖ ≤ B * d * ‖z‖ := by
    simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _),
      sub_apply] using
        ((fderiv ℝ u x - fderiv ℝ u y).le_opNorm z).trans
          (mul_le_mul_of_nonneg_right hdu (norm_nonneg _))
  have h₁ : ‖(Fx - Fy) Vx Wx‖ ≤ (Lf * (M * d)) * (M * ‖v‖) * (M * ‖w‖) := by
    refine (norm_apply₂_le _ _ _).trans ?_
    have hLip : ‖Fx - Fy‖ ≤ Lf * (M * d) :=
      (hflip X (hmem x hx) Y (hmem y hy)).trans (mul_le_mul_of_nonneg_left hXY hLf)
    have hv : ‖Vx‖ ≤ M * ‖v‖ := hnorm x hx v
    have hw : ‖Wx‖ ≤ M * ‖w‖ := hnorm x hx w
    gcongr
  have h₂ : ‖Fy (Vx - Vy) Wx‖ ≤ A * (B * d * ‖v‖) * (M * ‖w‖) := by
    refine (norm_apply₂_le _ _ _).trans ?_
    have hb : ‖Fy‖ ≤ A := hff Y (hmem y hy)
    have hv : ‖Vx - Vy‖ ≤ B * d * ‖v‖ := hgraphdiff v
    have hw : ‖Wx‖ ≤ M * ‖w‖ := hnorm x hx w
    gcongr
  have h₃ : ‖Fy Vy (Wx - Wy)‖ ≤ A * (M * ‖v‖) * (B * d * ‖w‖) := by
    refine (norm_apply₂_le _ _ _).trans ?_
    have hb : ‖Fy‖ ≤ A := hff Y (hmem y hy)
    have hv : ‖Vy‖ ≤ M * ‖v‖ := hnorm y hy v
    have hw : ‖Wx - Wy‖ ≤ B * d * ‖w‖ := hgraphdiff w
    gcongr
  have h₄ : ‖fderiv ℝ f₀ X (0, (Ux - Uy) v w)‖ ≤ D * (Lu * d * ‖v‖ * ‖w‖) := by
    rw [Real.norm_eq_abs]
    apply (hpartial X (hmem x hx) _).trans
    apply mul_le_mul_of_nonneg_left _ hD
    exact (norm_apply₂_le _ _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hulip x hx y hy) (norm_nonneg _))
        (norm_nonneg _))
  have h₅ : ‖(fderiv ℝ f₀ X - fderiv ℝ f₀ Y) (0, Uy v w)‖ ≤
      (A * (M * d)) * (B * ‖v‖ * ‖w‖) := by
    refine ((fderiv ℝ f₀ X - fderiv ℝ f₀ Y).le_opNorm _).trans ?_
    have hb : ‖Uy v w‖ ≤ B * ‖v‖ * ‖w‖ := (norm_apply₂_le _ _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (huu y hy) (norm_nonneg _))
        (norm_nonneg _))
    simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    exact mul_le_mul hdf hb (norm_nonneg _) (by positivity)
  simp only [sub_apply, second_fderiv_compositeObjective hf hu]
  change ‖(Fx Vx Wx + fderiv ℝ f₀ X (0, Ux v w)) -
    (Fy Vy Wy + fderiv ℝ f₀ Y (0, Uy v w))‖ ≤ (K * d) * ‖v‖ * ‖w‖
  have he : (Fx Vx Wx + fderiv ℝ f₀ X (0, Ux v w)) -
      (Fy Vy Wy + fderiv ℝ f₀ Y (0, Uy v w)) =
      (Fx - Fy) Vx Wx + Fy (Vx - Vy) Wx + Fy Vy (Wx - Wy) +
        fderiv ℝ f₀ X (0, (Ux - Uy) v w) +
        (fderiv ℝ f₀ X - fderiv ℝ f₀ Y) (0, Uy v w) := by
    have hsplit : (0, (Ux - Uy) v w) = ((0 : E), Ux v w) - (0, Uy v w) := by simp
    rw [hsplit]
    simp only [sub_apply, map_sub]
    ring
  rw [he]
  calc
    _ ≤ (Lf * (M * d)) * (M * ‖v‖) * (M * ‖w‖) + A * (B * d * ‖v‖) * (M * ‖w‖) +
        A * (M * ‖v‖) * (B * d * ‖w‖) + D * (Lu * d * ‖v‖ * ‖w‖) +
        (A * (M * d)) * (B * ‖v‖ * ‖w‖) :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃))
          h₄)) h₅)
    _ = _ := by dsimp [K]; ring

end ConnGouldToint.Chapter08
