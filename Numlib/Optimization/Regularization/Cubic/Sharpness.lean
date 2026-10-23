import Numlib.Optimization.Regularization.Cubic.FirstOrder
import Numlib.Optimization.LineSearch.Sharpness
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A twice-smooth plateau for cubic-regularization sharpness

Second differences of cubic positive parts give a nonnegative, twice-smooth
linear plateau. Its middle transition point has half the plateau gradient.
Choosing the transition width proportional to `√ε` keeps the Hessian Lipschitz
constant fixed while cubic-model steps travel a distance proportional to `√ε`.
-/

open Set Filter Topology
open scoped ContDiff

namespace CubicRegularization

/-- The cubic positive part is twice continuously differentiable. -/
noncomputable def cubicHinge (u : ℝ) : ℝ := (max 0 u) ^ 3

/-- Its first derivative is three times the squared positive part. -/
theorem hasDerivAt_cubicHinge (u : ℝ) :
    HasDerivAt cubicHinge (3 * BacktrackingGradient.squaredHinge u) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have heq : cubicHinge =ᶠ[𝓝 u] (fun _ => 0) := by
      filter_upwards [gt_mem_nhds hu] with v hv
      simp [cubicHinge, max_eq_left hv.le]
    simpa [BacktrackingGradient.squaredHinge, max_eq_left hu.le] using
      (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq heq
  · have hl : HasDerivWithinAt cubicHinge 0 (Iic 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
        (fun v hv => by simp [cubicHinge, max_eq_left (show v ≤ 0 from hv)])
        (by simp [cubicHinge])
    have hc : HasDerivAt (fun v : ℝ => v ^ 3) 0 0 := by
      convert (hasDerivAt_id (0 : ℝ)).pow 3 using 1
      · rfl
      · norm_num
    have hr : HasDerivWithinAt cubicHinge 0 (Ici 0) 0 :=
      hc.hasDerivWithinAt.congr
        (fun v hv => by simp [cubicHinge, max_eq_right (show 0 ≤ v from hv)])
        (by simp [cubicHinge])
    simpa [BacktrackingGradient.squaredHinge, Iic_union_Ici] using hl.union hr
  · have heq : cubicHinge =ᶠ[𝓝 u] (fun v => v ^ 3) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      simp [cubicHinge, max_eq_right hv.le]
    simpa [BacktrackingGradient.squaredHinge, max_eq_right hu.le] using
      ((hasDerivAt_id u).pow 3).congr_of_eventuallyEq heq

/-- The second derivative is the continuous piecewise linear function `6 max(0,u)`. -/
theorem hasDerivAt_deriv_cubicHinge (u : ℝ) :
    HasDerivAt (deriv cubicHinge) (6 * max 0 u) u := by
  have heq : deriv cubicHinge = fun v => 3 * BacktrackingGradient.squaredHinge v :=
    funext (fun v => (hasDerivAt_cubicHinge v).deriv)
  rw [heq]
  convert (BacktrackingGradient.hasDerivAt_squaredHinge u).const_mul 3 using 1
  ring

/-- Twice-smoothness holds globally, including the hinge junction. -/
@[fun_prop] theorem contDiff_cubicHinge : ContDiff ℝ 2 cubicHinge := by
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun u => (hasDerivAt_cubicHinge u).differentiableAt, by simp, ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun u => (hasDerivAt_deriv_cubicHinge u).differentiableAt, ?_⟩
  have heq : deriv (deriv cubicHinge) = fun u => 6 * max 0 u :=
    funext (fun u => (hasDerivAt_deriv_cubicHinge u).deriv)
  rw [heq]
  fun_prop

/-- A linear descent plateau with a twice-smooth terminal transition of width `2r`. -/
noncomputable def smoothPlateau (r ε X z : ℝ) : ℝ :=
  ε / (3 * r ^ 2) * (cubicHinge (X + 2 * r - z) -
    2 * cubicHinge (X + r - z) + cubicHinge (X - z))

/-- Its actual first derivative. -/
noncomputable def smoothPlateauGradient (r ε X z : ℝ) : ℝ :=
  ε / r ^ 2 * (-BacktrackingGradient.squaredHinge (X + 2 * r - z) +
    2 * BacktrackingGradient.squaredHinge (X + r - z) -
      BacktrackingGradient.squaredHinge (X - z))

/-- Its actual second derivative. -/
noncomputable def smoothPlateauHessian (r ε X z : ℝ) : ℝ :=
  2 * ε / r ^ 2 * (max 0 (X + 2 * r - z) -
    2 * max 0 (X + r - z) + max 0 (X - z))

/-- Twice continuous differentiability of the actual plateau objective. -/
theorem contDiff_smoothPlateau (r ε X : ℝ) : ContDiff ℝ 2 (smoothPlateau r ε X) := by
  unfold smoothPlateau
  fun_prop (disch := exact contDiff_cubicHinge)

/-- Derivative formula at every point of the smooth plateau. -/
theorem hasDerivAt_smoothPlateau (r ε X z : ℝ) :
    HasDerivAt (smoothPlateau r ε X) (smoothPlateauGradient r ε X z) z := by
  have h (a : ℝ) := (hasDerivAt_cubicHinge (a - z)).comp z
    ((hasDerivAt_const z a).sub (hasDerivAt_id z))
  have hd := (((h (X + 2 * r)).sub ((h (X + r)).const_mul 2)).add (h X)).const_mul
    (ε / (3 * r ^ 2))
  convert hd using 1
  · rfl
  · dsimp [smoothPlateauGradient]
    ring

/-- Second derivative formula at every point, including both junctions. -/
theorem hasDerivAt_smoothPlateauGradient (r ε X z : ℝ) :
    HasDerivAt (smoothPlateauGradient r ε X) (smoothPlateauHessian r ε X z) z := by
  have h (a : ℝ) := (BacktrackingGradient.hasDerivAt_squaredHinge (a - z)).comp z
    ((hasDerivAt_const z a).sub (hasDerivAt_id z))
  have hd := ((((h (X + 2 * r)).neg).add ((h (X + r)).const_mul 2)).sub (h X)).const_mul
    (ε / r ^ 2)
  convert hd using 1
  · rfl
  · dsimp [smoothPlateauHessian]
    ring

/-- Exact linear plateau values and derivatives, including its first junction. -/
theorem smoothPlateau_on_left {r : ℝ} (hr : 0 < r) (ε X z : ℝ) (hz : z ≤ X) :
    smoothPlateau r ε X z = 2 * ε * (X + r - z) ∧
      smoothPlateauGradient r ε X z = -2 * ε ∧ smoothPlateauHessian r ε X z = 0 := by
  have h0 : 0 ≤ X - z := by linarith
  have h1 : 0 ≤ X + r - z := by linarith
  have h2 : 0 ≤ X + 2 * r - z := by linarith
  simp only [smoothPlateau, smoothPlateauGradient, smoothPlateauHessian,
    cubicHinge, BacktrackingGradient.squaredHinge, max_eq_right h0,
    max_eq_right h1, max_eq_right h2]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  · ring

/-- The middle transition point has precisely half the plateau gradient. -/
theorem smoothPlateau_at_middle {r : ℝ} (hr : 0 < r) (ε X : ℝ) :
    smoothPlateau r ε X (X + r) = ε * r / 3 ∧
      smoothPlateauGradient r ε X (X + r) = -ε ∧
        smoothPlateauHessian r ε X (X + r) = 2 * ε / r := by
  have h1 : X + 2 * r - (X + r) = r := by ring
  have h2 : X + r - (X + r) = 0 := by ring
  have h3 : X - (X + r) = -r := by ring
  simp only [smoothPlateau, smoothPlateauGradient, smoothPlateauHessian,
    cubicHinge, BacktrackingGradient.squaredHinge, h1, h2, h3,
    max_eq_right hr.le, max_self, max_eq_left (neg_nonpos.mpr hr.le),
    mul_zero, sub_zero, add_zero]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  · field_simp

/-- The smooth plateau is bounded below by zero everywhere. -/
theorem smoothPlateau_nonneg {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (X z : ℝ) :
    0 ≤ smoothPlateau r ε X z := by
  unfold smoothPlateau
  apply mul_nonneg (div_nonneg hε (by positivity))
  let u := X - z
  rw [show X + 2 * r - z = u + 2 * r by dsimp [u]; ring,
    show X + r - z = u + r by dsimp [u]; ring]
  change 0 ≤ cubicHinge (u + 2 * r) - 2 * cubicHinge (u + r) + cubicHinge u
  by_cases hu : 0 ≤ u
  · have h1 : 0 ≤ u + r := by linarith
    have h2 : 0 ≤ u + 2 * r := by linarith
    simp only [cubicHinge, max_eq_right hu, max_eq_right h1, max_eq_right h2]
    have heq : (u + 2 * r) ^ 3 - 2 * (u + r) ^ 3 + u ^ 3 =
        6 * r ^ 2 * (u + r) := by ring
    rw [heq]
    positivity
  · have hu0 : u ≤ 0 := le_of_not_ge hu
    by_cases h1 : 0 ≤ u + r
    · have h2 : 0 ≤ u + 2 * r := by linarith
      have hc : (u + r) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ h1 (by linarith) 3
      simp only [cubicHinge, max_eq_left hu0, max_eq_right h1,
        max_eq_right h2]
      have heq : (u + 2 * r) ^ 3 - 2 * (u + r) ^ 3 =
          r ^ 3 - (u + r) ^ 3 + 3 * r * (u + r) ^ 2 + 3 * r ^ 2 * (u + r) := by ring
      rw [heq]
      positivity
    · have h10 : u + r ≤ 0 := le_of_not_ge h1
      simp [cubicHinge, max_eq_left hu0, max_eq_left h10]

/-- The actual Hessian values have an explicit global Lipschitz bound. -/
theorem smoothPlateauHessian_lipschitz {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (X z w : ℝ) :
    ‖smoothPlateauHessian r ε X z - smoothPlateauHessian r ε X w‖ ≤
      (8 * ε / r ^ 2) * ‖z - w‖ := by
  have hmax (a : ℝ) : |max 0 (a - z) - max 0 (a - w)| ≤ |z - w| := by
    simpa only [max_comm, show a - z - (a - w) = -(z - w) by ring, abs_neg]
      using abs_max_sub_max_le_abs (a - z) (a - w) 0
  let A := max 0 (X + 2 * r - z) - max 0 (X + 2 * r - w)
  let B := max 0 (X + r - z) - max 0 (X + r - w)
  let C := max 0 (X - z) - max 0 (X - w)
  have hsum : |A - 2 * B + C| ≤ 4 * |z - w| := by
    have ht := (abs_add_le (A - 2 * B) C).trans
      (add_le_add (abs_sub A (2 * B)) le_rfl)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    have hA := hmax (X + 2 * r)
    have hB := hmax (X + r)
    have hC := hmax X
    change |A| ≤ _ at hA
    change |B| ≤ _ at hB
    change |C| ≤ _ at hC
    linarith
  have heq : smoothPlateauHessian r ε X z - smoothPlateauHessian r ε X w =
      (2 * ε / r ^ 2) * (A - 2 * B + C) := by
    dsimp [smoothPlateauHessian, A, B, C]
    ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ε / r ^ 2),
    Real.norm_eq_abs]
  have hs := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * ε / r ^ 2)
  convert hs using 1
  ring

/-- The computed Hessian is the actual second ordinary derivative. -/
theorem iteratedDeriv_two_smoothPlateau (r ε X z : ℝ) :
    iteratedDeriv 2 (smoothPlateau r ε X) z = smoothPlateauHessian r ε X z := by
  have heq : deriv (smoothPlateau r ε X) = smoothPlateauGradient r ε X :=
    funext (fun z => (hasDerivAt_smoothPlateau r ε X z).deriv)
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, heq]
  exact (hasDerivAt_smoothPlateauGradient r ε X z).deriv

/-- The actual second derivative tensors inherit the computed global
Hessian Lipschitz bound. -/
theorem smoothPlateau_tensor_lipschitz {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (X z w : ℝ) :
    ‖iteratedFDeriv ℝ 2 (smoothPlateau r ε X) z -
      iteratedFDeriv ℝ 2 (smoothPlateau r ε X) w‖ ≤ (8 * ε / r ^ 2) * ‖z - w‖ := by
  rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub,
    iteratedDeriv_two_smoothPlateau, iteratedDeriv_two_smoothPlateau]
  exact smoothPlateauHessian_lipschitz hr hε X z w

/-- The actual first derivative is represented by the computed scalar gradient. -/
theorem hasFDerivAt_smoothPlateau (r ε X z : ℝ) :
    HasFDerivAt (smoothPlateau r ε X) (innerSL ℝ (smoothPlateauGradient r ε X z)) z := by
  convert (hasDerivAt_smoothPlateau r ε X z).hasFDerivAt using 1
  ext
  simp [innerSL_apply_apply, mul_comm]

/-- The actual derivative of the gradient is represented by the computed Hessian. -/
theorem hasFDerivAt_smoothPlateauGradient (r ε X z : ℝ) :
    HasFDerivAt (smoothPlateauGradient r ε X) (innerSL ℝ (smoothPlateauHessian r ε X z)) z := by
  convert (hasDerivAt_smoothPlateauGradient r ε X z).hasFDerivAt using 1
  ext
  simp [innerSL_apply_apply, mul_comm]

/-- The actual second derivative vanishes on the linear plateau. -/
theorem secondDerivative_smoothPlateau_eq_zero {r : ℝ} (hr : 0 < r)
    (ε X z : ℝ) (hz : z ≤ X) :
    fderiv ℝ (fderiv ℝ (smoothPlateau r ε X)) z = 0 := by
  have hfun : fderiv ℝ (smoothPlateau r ε X) =
      fun y => innerSL ℝ (smoothPlateauGradient r ε X y) :=
    funext (fun y => (hasFDerivAt_smoothPlateau r ε X y).fderiv)
  rw [hfun]
  have hg := hasFDerivAt_smoothPlateauGradient r ε X z
  rw [(smoothPlateau_on_left hr ε X z hz).2.2, map_zero] at hg
  have hd := (innerSL ℝ).hasFDerivAt.comp z hg
  convert hd.fderiv using 1 <;> simp [Function.comp_def]

/-- The objective-based ratio for a constant scalar trial length. -/
noncomputable def plateauRatio (f : ℝ → ℝ) (x : ℕ → ℝ) (t : ℝ) (i : ℕ) : ℝ :=
  (f (x i) - f (x i + t)) / (TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) t)

/-- The equally spaced orbit is a genuine cubic-regularization execution.
The ratio is computed from the objective, and model stationarity follows from
the actual derivatives and the relation `σ t² = 4ε`. -/
theorem plateau_firstOrderRun {η₁ η₂ γ₁ γ₂ γ₃ θ σ ε t : ℝ} {N : ℕ}
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃)
    (hθ : 0 < θ) (hσ : 0 < σ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ht : 0 < t) (hscale : σ * t ^ 2 = 4 * ε) (_hN : 0 < N) :
    let r := t * (1 - η₂)
    let X := (N : ℝ) * t - r
    let f := smoothPlateau r ε X
    let x := fun i : ℕ => (i : ℝ) * t
    let ρ := plateauRatio f x t
    FirstOrderRun f x (fun _ => t) (fun _ => σ) ρ η₁ η₂ γ₁ γ₂ γ₃ σ θ ε ⊤ N ∧
      (∀ i < N, η₂ ≤ ρ i) ∧ ‖fderiv ℝ f (x N)‖ = ε := by
  let r := t * (1 - η₂)
  let X := (N : ℝ) * t - r
  let f := smoothPlateau r ε X
  let x := fun i : ℕ => (i : ℝ) * t
  let ρ := plateauRatio f x t
  have hη₂0 := hη₁.trans_le hη
  have hr : 0 < r := mul_pos ht (sub_pos.mpr hη₂)
  have hrt : r < t := by dsimp [r]; nlinarith
  have hxleft : ∀ i < N, x i ≤ X := by
    intro i hi
    have hn : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    dsimp [x, X]
    nlinarith
  have hleft (i : ℕ) (hi : i < N) := smoothPlateau_on_left hr ε X (x i) (hxleft i hi)
  have hmid : smoothPlateauGradient r ε X (x N) = -ε := by
    have hxN : x N = X + r := by dsimp [x, X]; ring
    rw [hxN]
    exact (smoothPlateau_at_middle hr ε X).2.1
  have htrial : ∀ i, x i + t = x (i + 1) := by
    intro i
    dsimp [x]
    push_cast
    ring
  have hden (i : ℕ) (hi : i < N) :
      TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) t = 2 * ε * t := by
    rw [TaylorModel.eval_zero, TaylorModel.eval_two_eq,
      (hasFDerivAt_smoothPlateau r ε X (x i)).fderiv,
      secondDerivative_smoothPlateau_eq_zero hr ε X (x i) (hxleft i hi)]
    rw [(hleft i hi).2.1]
    simp [innerSL_apply_apply]
    ring
  have hvery : ∀ i < N, η₂ ≤ ρ i := by
    intro i hi
    change η₂ ≤ (f (x i) - f (x i + t)) /
      (TaylorModel.eval f 2 (x i) 0 - TaylorModel.eval f 2 (x i) t)
    rw [hden i hi]
    apply (le_div_iff₀ (by positivity : 0 < 2 * ε * t)).mpr
    rw [htrial]
    change η₂ * (2 * ε * t) ≤ smoothPlateau r ε X (x i) -
      smoothPlateau r ε X (x (i + 1))
    rw [(hleft i hi).1]
    by_cases hnext : i + 1 < N
    · rw [(hleft (i + 1) hnext).1]
      have hprod : 0 ≤ (1 - η₂) * ε * t := by positivity
      dsimp [x]
      push_cast
      nlinarith
    · have hiN : i + 1 = N := by omega
      have hxN : x N = X + r := by dsimp [x, X]; ring
      rw [hiN, hxN, (smoothPlateau_at_middle hr ε X).1]
      have hiN' : (i : ℝ) + 1 = N := by exact_mod_cast hiN
      dsimp [x, X, r]
      rw [← hiN']
      have hprod : 0 ≤ (1 - η₂) * ε * t := by positivity
      nlinarith
  have hstat : ∀ i < N, fderiv ℝ (model f (x i) σ) t = 0 := by
    intro i hi
    rw [fderiv_model (contDiff_smoothPlateau r ε X).contDiffAt, TaylorModel.quadraticDerivative,
      secondDerivative_smoothPlateau_eq_zero hr ε X (x i) (hxleft i hi),
      zero_apply, add_zero, (hasFDerivAt_smoothPlateau r ε X (x i)).fderiv,
      (hleft i hi).2.1, Real.norm_of_nonneg ht.le]
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, smul_apply, zero_apply, innerSL_apply_apply,
      RCLike.inner_apply, conj_trivial, smul_eq_mul]
    linear_combination (v / 2) * hscale
  have hrun : FirstOrderRun f x (fun _ => t) (fun _ => σ) ρ
      η₁ η₂ γ₁ γ₂ γ₃ σ θ ε ⊤ N := by
    refine ⟨rfl, ⟨?_, ?_, ?_⟩, hθ, hε, hε1, ?_, ?_, ?_⟩
    · refine ⟨hσ, le_rfl, hη₁, hη, hη₂, hγ₁, hγ₁1, hγ₂, hγ₃, ?_⟩
      intro i hi
      rw [ite_eq_left (hvery i hi)]
      exact ⟨max_le le_rfl (by nlinarith), le_rfl⟩
    · intro i hi
      change model f (x i) σ t < model f (x i) σ 0
      have he := hden i hi
      norm_num [model, ModelDecrease.penalized, Real.norm_of_nonneg ht.le]
      rw [TaylorModel.eval_zero] at he
      have hh : σ / 6 * t ^ 3 = 2 * ε * t / 3 := by
        calc _ = (σ * t ^ 2) * t / 6 := by ring
             _ = _ := by rw [hscale]; ring
      rw [hh]
      nlinarith [mul_pos hε ht]
    · intro i hi
      rfl
    · intro i hi
      rw [(hasFDerivAt_smoothPlateau r ε X (x i)).fderiv, innerSL_apply_norm,
        (hleft i hi).2.1, Real.norm_eq_abs, abs_of_neg (by linarith : -2 * ε < 0)]
      linarith
    · intro i hi
      rw [hstat i hi, norm_zero]
      positivity
    · intro i hi
      rw [ite_eq_left (hη.trans (hvery i hi))]
      exact (htrial i).symm
  refine ⟨hrun, hvery, ?_⟩
  rw [(hasFDerivAt_smoothPlateau r ε X (x N)).fderiv, innerSL_apply_norm,
    hmid, norm_neg, Real.norm_of_nonneg hε.le]

/-- Uniformly regular, bounded-gap objectives can force the full `ε⁻³ᐟ²`
number of genuine AR2 iterations. All trials are accepted, so the same lower
bound applies to objective, gradient and Hessian evaluations. -/
theorem exists_slow_firstOrderRun {η₁ η₂ γ₁ γ₂ γ₃ θ σ : ℝ}
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃)
    (hθ : 0 < θ) (hσ : 0 < σ) :
    ∃ L ≥ 1, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : ℝ → ℝ) (x : ℕ → ℝ) (t : ℝ) (ρ : ℕ → ℝ) (N : ℕ),
        ContDiff ℝ 2 f ∧ (∀ z, 0 ≤ f z) ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖) ∧
        f (x 0) ≤ 8 / Real.sqrt σ ∧
        N = ⌈1 / ε ^ (3 / 2 : ℝ)⌉₊ ∧
        FirstOrderRun f x (fun _ => t) (fun _ => σ) ρ η₁ η₂ γ₁ γ₂ γ₃ σ θ ε ⊤ N ∧
        (∀ i < N, η₂ ≤ ρ i) ∧ ‖fderiv ℝ f (x N)‖ = ε ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ N ∧
        1 / ε ^ (3 / 2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ∧
        1 / ε ^ (3 / 2 : ℝ) ≤
          (((EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} N).card + 1 : ℕ) : ℝ) := by
  let a := 1 - η₂
  have ha : 0 < a := sub_pos.mpr hη₂
  refine ⟨1 + 2 * σ / a ^ 2, by
    have hh : 0 ≤ 2 * σ / a ^ 2 := by positivity
    linarith, ?_⟩
  intro ε hε hε1
  let e := Real.sqrt ε
  let b := Real.sqrt σ
  let t := 2 * e / b
  let r := t * a
  let N := ⌈1 / ε ^ (3 / 2 : ℝ)⌉₊
  let X := (N : ℝ) * t - r
  let f := smoothPlateau r ε X
  let x := fun i : ℕ => (i : ℝ) * t
  let ρ := plateauRatio f x t
  have he : 0 < e := Real.sqrt_pos.mpr hε
  have hb : 0 < b := Real.sqrt_pos.mpr hσ
  have he2 : e ^ 2 = ε := Real.sq_sqrt hε.le
  have hb2 : b ^ 2 = σ := Real.sq_sqrt hσ.le
  have ht : 0 < t := by dsimp [t]; positivity
  have hr : 0 < r := mul_pos ht ha
  have hpow : ε ^ (3 / 2 : ℝ) = ε * e := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hε,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hscale : σ * t ^ 2 = 4 * ε := by
    dsimp [t]
    rw [div_pow, mul_pow, hb2, mul_div_cancel₀ _ hσ.ne']
    nlinarith
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hrun := plateau_firstOrderRun hη₁ hη hη₂ hγ₁ hγ₁1 hγ₂ hγ₃ hθ hσ hε hε1
    ht hscale hN
  change FirstOrderRun f x (fun _ => t) (fun _ => σ) ρ
    η₁ η₂ γ₁ γ₂ γ₃ σ θ ε ⊤ N ∧ _ at hrun
  classical
  have hcard : (EvaluationComplexity.successfulIterations {i | η₁ ≤ ρ i} N).card = N := by
    unfold EvaluationComplexity.successfulIterations
    change ((Finset.range N).filter (fun i => η₁ ≤ ρ i)).card = N
    have hall : ∀ i ∈ Finset.range N, η₁ ≤ ρ i :=
      fun i hi => hη.trans (hrun.2.1 i (Finset.mem_range.mp hi))
    rw [Finset.filter_eq_self.mpr hall]
    exact Finset.card_range N
  have hcount : 1 / ε ^ (3 / 2 : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
  refine ⟨f, x, t, ρ, N, contDiff_smoothPlateau r ε X,
    smoothPlateau_nonneg hr hε.le X, ?_, ?_, rfl, hrun.1, hrun.2.1,
    hrun.2.2, hcount, ?_, ?_⟩
  · intro z w
    have hc : 8 * ε / r ^ 2 = 2 * σ / a ^ 2 := by
      apply (div_eq_div_iff (by positivity : r ^ 2 ≠ 0) (by positivity : a ^ 2 ≠ 0)).mpr
      dsimp [r]
      nlinarith [hscale]
    rw [← add_zero (1 + 2 * σ / a ^ 2)]
    calc
      _ ≤ (8 * ε / r ^ 2) * ‖z - w‖ := smoothPlateau_tensor_lipschitz hr hε.le X z w
      _ ≤ _ := by rw [hc]; nlinarith [norm_nonneg (z - w)]
  · have hx0 : x 0 = 0 := by simp [x]
    have hX : 0 ≤ X := by
      have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
      have ha1 : a < 1 := by dsimp [a]; linarith
      dsimp [X, r]
      nlinarith
    rw [hx0]
    change smoothPlateau r ε X 0 ≤ _
    rw [(smoothPlateau_on_left hr ε X 0 hX).1]
    have he1 : e ≤ 1 := by
      dsimp [e]
      exact (Real.sqrt_le_one).mpr hε1
    have hprod : ε * e ≤ 1 := by nlinarith
    have hceil : (N : ℝ) < 1 / (ε * e) + 1 := by
      have hh : (N : ℝ) < 1 / ε ^ (3 / 2 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
      simpa only [hpow] using hh
    have hNprod : (N : ℝ) * (ε * e) ≤ 2 := by
      have hh := (mul_lt_mul_iff_left₀ (mul_pos hε he)).mpr hceil
      rw [add_mul, one_mul, div_mul_cancel₀ _ (mul_pos hε he).ne'] at hh
      nlinarith
    apply (le_div_iff₀ hb).mpr
    have hid : (2 * ε * (X + r - 0)) * b = 4 * (N : ℝ) * (ε * e) := by
      dsimp [X, r, t]
      field_simp
      ring
    rw [hid]
    nlinarith
  · push_cast
    linarith
  · rw [hcard]
    push_cast
    linarith

end CubicRegularization
