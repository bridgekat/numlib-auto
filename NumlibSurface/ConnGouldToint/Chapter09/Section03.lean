import NumlibSurface.ConnGouldToint.Chapter09.Section01
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Second-order conditional models -/

open Filter Topology

namespace ConnGouldToint.Chapter09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second-order validity, as in (9.3.1), in addition to the validity of Section 9.1. -/
def modelSecondOrderValidOnBall (f m : E → ℝ) (x : E) (δ κ₁ κ₂ : ℝ) : Prop :=
  modelValidOnBall f m x δ κ₁ ∧
    ∀ z ∈ Metric.closedBall x δ, |f z - m z| ≤ κ₂ * δ ^ 3

private theorem opNorm_le_of_diagonal {B : E →L[ℝ] E →L[ℝ] ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hsymm : ∀ u v, B u v = B v u)
    (hdiag : ∀ u, |B u u| ≤ K * ‖u‖ ^ 2) : ‖B‖ ≤ 2 * K := by
  have hunit (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : |B u v| ≤ 2 * K := by
    have hadd : ‖u + v‖ ≤ 2 := by
      exact (norm_add_le u v).trans (by rw [hu, hv]; norm_num)
    have hsub : ‖u - v‖ ≤ 2 := by
      exact (norm_sub_le u v).trans (by rw [hu, hv]; norm_num)
    have h₁ := (hdiag (u + v)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hadd 2) hK)
    have h₂ := (hdiag (u - v)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsub 2) hK)
    simp only [map_add, map_sub, add_apply, sub_apply,
      hsymm v u, abs_le] at h₁ h₂ ⊢
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  apply B.opNorm_le_bound (by positivity)
  intro u
  apply (B u).opNorm_le_bound (by positivity)
  intro v
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hun := norm_ne_zero_iff.mpr hu
  have hvn := norm_ne_zero_iff.mpr hv
  have hnorm (z : E) (hz : ‖z‖ ≠ 0) : ‖‖z‖⁻¹ • z‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hz]
  have h := hunit (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) (hnorm u hun) (hnorm v hvn)
  simp only [map_smul, smul_apply, smul_eq_mul,
    abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u‖⁻¹),
    abs_of_nonneg (by positivity : 0 ≤ ‖v‖⁻¹)] at h
  rw [Real.norm_eq_abs]
  convert mul_le_mul_of_nonneg_left h (show 0 ≤ ‖u‖ * ‖v‖ by positivity) using 1
  · field_simp
  · ring

/-- Theorem 9.3.1 under Lipschitz bounds on the two Hessians. The centered difference
eliminates the constant and linear Taylor terms, allowing a positive radius and an
arbitrary center mismatch within the validity bound. -/
theorem theorem_9_3_1_of_hessian_lipschitz {f m : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hm : ContDiff ℝ 2 m) {x : E} {δ κ₁ κ₂ Lf Lm : ℝ} (hδ : 0 < δ)
    (hκ : 0 ≤ κ₂) (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) x‖ ≤ Lf * ‖z - x‖)
    (hM : ∀ z, ‖fderiv ℝ (fderiv ℝ m) z - fderiv ℝ (fderiv ℝ m) x‖ ≤ Lm * ‖z - x‖)
    (hv : modelSecondOrderValidOnBall f m x δ κ₁ κ₂) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ m) x‖ ≤
      2 * (4 * κ₂ + (Lf + Lm) / 3) * δ := by
  let B := fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ m) x
  let K := 4 * κ₂ + (Lf + Lm) / 3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hstep (s : E) (hs : ‖s‖ = δ) : |B s s| ≤ K * δ ^ 3 := by
    have hball (t : E) (ht : ‖t‖ = δ) : x + t ∈ Metric.closedBall x δ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, ht]
    have h₀ := abs_le.mp (hv.2 x (Metric.mem_closedBall_self hδ.le))
    have hn : ‖-s‖ = δ := by simpa using hs
    have h₁ := abs_le.mp (hv.2 (x + s) (hball s hs))
    have h₂ := abs_le.mp (hv.2 (x + -s) (hball (-s) hn))
    have rem {g : E → ℝ} (hg : ContDiff ℝ 2 g) {L : ℝ}
        (hL : ∀ z, ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) x‖ ≤ L * ‖z - x‖)
        (t : E) (ht : ‖t‖ = δ) :
        |g (x + t) - (g x + fderiv ℝ g x t + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ g) x t t)| ≤
          (1 / 6 : ℝ) * L * δ ^ 3 := by
      rw [← ht]
      exact abs_sub_secondOrder_le_of_lipschitzAt_segment isOpen_univ hg.contDiffOn
        (fun _ _ ↦ Set.mem_univ _) (fun z _ ↦ hL z)
    have hf₁ := abs_le.mp (rem hf hF s hs)
    have hf₂ := abs_le.mp (rem hf hF (-s) hn)
    have hm₁ := abs_le.mp (rem hm hM s hs)
    have hm₂ := abs_le.mp (rem hm hM (-s) hn)
    simp only [map_neg, neg_apply, neg_neg] at hf₂ hm₂
    rw [abs_le]
    dsimp [B, K]
    simp only [sub_apply]
    constructor <;>
      linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, hf₁.1, hf₁.2, hf₂.1, hf₂.2,
        hm₁.1, hm₁.2, hm₂.1, hm₂.2]
  rw [mul_assoc]
  apply opNorm_le_of_diagonal (mul_nonneg hK hδ.le)
  · intro u v
    exact congrArg₂ Sub.sub ((hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq u v)
      ((hm.contDiffAt.isSymmSndFDerivAt (by simp)).eq u v)
  · intro u
    by_cases hu : u = 0
    · simp [hu]
    have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let a := δ / ‖u‖
    have ha : 0 < a := by dsimp [a]; positivity
    have hs : ‖a • u‖ = δ := by
      rw [norm_smul, Real.norm_of_nonneg ha.le]
      exact div_mul_cancel₀ _ hnu.ne'
    have h := hstep (a • u) hs
    simp only [map_smul, smul_apply, smul_eq_mul,
      abs_mul, abs_mul, abs_of_pos ha] at h
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos ha)).mp
    calc
      a ^ 2 * |B u u| ≤ K * δ ^ 3 := by nlinarith only [h]
      _ = a ^ 2 * (K * δ * ‖u‖ ^ 2) := by dsimp [a]; field_simp

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 9.3.1 under uniform bounds on third derivatives. The model Hessian
is differentiable and hence continuous, as required for the Taylor estimate. -/
theorem theorem_9_3_1 {f m : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hm : Differentiable ℝ m) (hDm₁ : Differentiable ℝ (fderiv ℝ m))
    (hDm₂ : Differentiable ℝ (fderiv ℝ (fderiv ℝ m)))
    {x : E} {δ κ₁ κ₂ Lf Lm : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ₂)
    (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ Lf)
    (hM : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ m)) z‖ ≤ Lm)
    (hv : modelSecondOrderValidOnBall f m x δ κ₁ κ₂) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ m) x‖ ≤
      2 * (4 * κ₂ + (Lf + Lm) / 3) * δ := by
  have hDf : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hD2f : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hDf.fderiv_right (by norm_num)
  have lip {g : E → E →L[ℝ] E →L[ℝ] ℝ} (hg : Differentiable ℝ g) {L : ℝ}
      (hL : ∀ z, ‖fderiv ℝ g z‖ ≤ L) (z : E) : ‖g z - g x‖ ≤ L * ‖z - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ ↦ hg y) (fun y _ ↦ hL y)
      (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ z)
  have hCm : ContDiff ℝ 2 m := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
    refine ⟨hm, by simp, contDiff_one_iff_fderiv.mpr ⟨hDm₁, hDm₂.continuous⟩⟩
  exact theorem_9_3_1_of_hessian_lipschitz (hf.of_le (by norm_num)) hCm hδ hκ hLf hLm
    (lip (hD2f.differentiable (by norm_num)) hF) (lip hDm₂ hM) hv

/-- Corollary 9.3.2. The modified acceptance test provides eventual second-order
validity on balls of positive radii capped by a multiple of the model gradient. -/
theorem corollary_9_3_2 {f : E → ℝ} (hf : ContDiff ℝ 3 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k))
    (hDm₁ : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    (hDm₂ : ∀ k, Differentiable ℝ (fderiv ℝ (fderiv ℝ (m k))))
    {x : ℕ → E} {δ : ℕ → ℝ} {κ₁ κ₂ Lf Lm μ : ℝ}
    (hκ : 0 ≤ κ₂) (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ Lf)
    (hM : ∀ k z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (m k))) z‖ ≤ Lm)
    (hvalid : ∀ᶠ k in atTop, 0 < δ k ∧ δ k ≤ μ * ‖fderiv ℝ (m k) (x k)‖ ∧
      modelSecondOrderValidOnBall f (m k) (x k) (δ k) κ₁ κ₂)
    (hg : Tendsto (fun k ↦ ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0)) :
    Tendsto (fun k ↦
      ‖fderiv ℝ (fderiv ℝ f) (x k) - fderiv ℝ (fderiv ℝ (m k)) (x k)‖) atTop (𝓝 0) := by
  let C := 2 * (4 * κ₂ + (Lf + Lm) / 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc : Tendsto (fun _ : ℕ ↦ C * μ) atTop (𝓝 (C * μ)) := tendsto_const_nhds
  have hlim : Tendsto (fun k ↦ (C * μ) * ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hc.mul hg
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hvalid] with k hk
  have he := theorem_9_3_1 hf (hm k) (hDm₁ k) (hDm₂ k) hk.1 hκ hLf hLm hF (hM k) hk.2.2
  calc
    _ ≤ C * δ k := he
    _ ≤ C * (μ * ‖fderiv ℝ (m k) (x k)‖) := mul_le_mul_of_nonneg_left hk.2.1 hC
    _ = _ := (mul_assoc C μ _).symm

/-- Theorem 9.3.3 in terms of the bounds supplied by an infinite refinement loop.
The model curvature may stay negative at each finite refinement. Its lower bound
tends to zero, which is what the proof needs in place of the printed (9.3.4). -/
theorem theorem_9_3_3 {f : E → ℝ} (hf : ContDiff ℝ 3 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k))
    (hDm₁ : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    (hDm₂ : ∀ k, Differentiable ℝ (fderiv ℝ (fderiv ℝ (m k))))
    {x : E} {δ τ : ℕ → ℝ} {κ₁ κ₂ Bf Bm Lf Lm μ : ℝ}
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 ≤ κ₂) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hLf : 0 ≤ Lf) (hLm : 0 ≤ Lm)
    (hF₂ : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM₂ : ∀ k z, ‖fderiv ℝ (fderiv ℝ (m k)) z‖ ≤ Bm)
    (hF₃ : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ Lf)
    (hM₃ : ∀ k z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (m k))) z‖ ≤ Lm)
    (hvalid : ∀ᶠ k in atTop, 0 < δ k ∧ δ k ≤ μ * τ k ∧
      modelSecondOrderValidOnBall f (m k) x (δ k) κ₁ κ₂)
    (hgrad : ∀ᶠ k in atTop, ‖fderiv ℝ (m k) x‖ ≤ τ k)
    (hcurv : ∀ v, ∀ᶠ k in atTop, -(τ k) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (m k)) x v v)
    (hτ : Tendsto τ atTop (𝓝 0)) :
    fderiv ℝ f x = 0 ∧ ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let Cg := 2 * κ₁ + (Bf + Bm) / 2
  let Ch := 2 * (4 * κ₂ + (Lf + Lm) / 3)
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCh : 0 ≤ Ch := by dsimp [Ch]; positivity
  constructor
  · apply norm_le_zero_iff.mp
    have hlim : Tendsto (fun k ↦ (1 + Cg * μ) * τ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hτ (f := fun _ ↦ 1 + Cg * μ)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [hvalid, hgrad] with k hv hg
    have he := theorem_9_1_1 (hf.of_le (by norm_num)) (hm k) (hDm₁ k)
      hv.1 hκ₁ hBf hBm hF₂ (hM₂ k) hv.2.2.1
    let a := fderiv ℝ f x
    let b := fderiv ℝ (m k) x
    calc
      ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a - b) b
      _ ≤ Cg * δ k + τ k := add_le_add he hg
      _ ≤ Cg * (μ * τ k) + τ k := add_le_add (mul_le_mul_of_nonneg_left hv.2.1 hCg) le_rfl
      _ = _ := by ring
  · intro v
    have hlim : Tendsto (fun k ↦ -((1 + Ch * μ) * ‖v‖ ^ 2) * τ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        tendsto_const_nhds.mul hτ (f := fun _ ↦ -((1 + Ch * μ) * ‖v‖ ^ 2))
    apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    filter_upwards [hvalid, hcurv v] with k hv hc
    have he := theorem_9_3_1 hf (hm k) (hDm₁ k) (hDm₂ k) hv.1 hκ₂ hLf hLm hF₃ (hM₃ k) hv.2.2
    let A := fderiv ℝ (fderiv ℝ f) x
    let B := fderiv ℝ (fderiv ℝ (m k)) x
    let D := A - B
    have hd : |D v v| ≤ Ch * (μ * τ k) * ‖v‖ ^ 2 := calc
      |D v v| = ‖D v v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖D v‖ * ‖v‖ := (D v).le_opNorm v
      _ ≤ (‖D‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (D.le_opNorm v) (norm_nonneg _)
      _ = ‖D‖ * ‖v‖ ^ 2 := by ring
      _ ≤ Ch * (μ * τ k) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (he.trans (mul_le_mul_of_nonneg_left hv.2.1 hCh)) (sq_nonneg _)
    have hd' := (abs_le.mp hd).1
    change -(Ch * (μ * τ k) * ‖v‖ ^ 2) ≤ A v v - B v v at hd'
    change -(τ k) * ‖v‖ ^ 2 ≤ B v v at hc
    change -((1 + Ch * μ) * ‖v‖ ^ 2) * τ k ≤ A v v
    calc
      _ = -(Ch * (μ * τ k) * ‖v‖ ^ 2) + (-(τ k) * ‖v‖ ^ 2) := by ring
      _ ≤ (A v v - B v v) + B v v := add_le_add hd' hc
      _ = _ := sub_add_cancel _ _

/-- At radius zero, two smooth models can agree in value and have distinct Hessians. -/
theorem second_order_zero_radius_counterexample :
    modelSecondOrderValidOnBall (fun x : ℝ ↦ x ^ 2) (fun _ ↦ 0) 0 0 1 1 ∧
      fderiv ℝ (fderiv ℝ (fun x : ℝ ↦ x ^ 2)) 0 ≠
        fderiv ℝ (fderiv ℝ (fun _ : ℝ ↦ (0 : ℝ))) 0 := by
  constructor
  · constructor <;> intro z hz <;> have hz₀ : z = 0 := by simpa using hz
    all_goals simp [hz₀]
  · let f := fun x : ℝ ↦ x ^ 2
    have hf : ContDiff ℝ 2 f := contDiff_id.pow 2
    have hDf : Differentiable ℝ (fderiv ℝ f) :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have hfirst : (fun x ↦ fderiv ℝ f x 1) = fun x ↦ 2 * x := by
      funext x
      rw [fderiv_apply_one_eq_deriv]
      change deriv (fun y : ℝ ↦ y ^ 2) x = _
      rw [deriv_pow_field]
      norm_num
    have hsecond : deriv (fun x ↦ fderiv ℝ f x 1) 0 = 2 := by
      rw [hfirst]
      simpa only [id_eq, mul_one] using ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).deriv
    change fderiv ℝ (fderiv ℝ f) 0 ≠
      fderiv ℝ (fderiv ℝ (Function.const ℝ (0 : ℝ))) 0
    rw [fderiv_const]
    change fderiv ℝ (fderiv ℝ f) 0 ≠
      fderiv ℝ (Function.const ℝ (0 : ℝ →L[ℝ] ℝ)) 0
    rw [fderiv_const]
    intro h
    rw [deriv_clm_apply (hDf 0) (differentiableAt_const (1 : ℝ)),
      ← fderiv_apply_one_eq_deriv, h] at hsecond
    simp at hsecond

end ConnGouldToint.Chapter09
