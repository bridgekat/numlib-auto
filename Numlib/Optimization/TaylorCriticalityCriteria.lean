import Numlib.Optimization.TaylorOptimality
import Numlib.Optimization.TaylorModelRemainder
import Numlib.Optimization.HigherOrder
import Numlib.Optimization.HessianCurvature
import Numlib.Optimization.RegularizedTaylorCurvature
import Numlib.Analysis.Normed.Multilinear.Diagonal
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Criteria from actual Taylor gaps

Bounds on Taylor gaps imply lower-order derivative conditions. Truncation controls consecutive
model orders; continuity of the highest derivative controls the gap near a local minimum.
-/

noncomputable section
open scoped Nat
open Set Metric Filter Topology
namespace Optimization.TaylorCriticality
open RegularizedTaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The next Taylor term is bounded in the diagonal tensor norm. -/
theorem abs_taylorModel_succ_sub_le_diagonal (f : E → ℝ) (p : ℕ) (x s : E) :
    |taylorModel f (p + 1) x s - taylorModel f p x s| ≤
      (iteratedFDeriv ℝ (p + 1) f x).diagonalNorm / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  rw [taylorModel_succ, add_sub_cancel_left, smul_eq_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ((p + 1)! : ℝ)⁻¹)]
  have h := (iteratedFDeriv ℝ (p + 1) f x).norm_diagonal_le_diagonalNorm_mul
    (by omega) s
  have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ ((p + 1)! : ℝ)⁻¹)
  simpa only [ContinuousMultilinearMap.diagonal, Real.norm_eq_abs, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using h'

/-- On the diagonal, the iterated third Fréchet derivative agrees with the curried third
derivative used by the classical optimality conditions. -/
theorem iteratedFDeriv_three_diagonal (f : E → ℝ) (x d : E) :
    iteratedFDeriv ℝ 3 f x (fun _ => d) =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x d d d := by
  simp only [iteratedFDeriv_succ_apply_right, iteratedFDeriv_zero_apply]
  rfl

/-- A higher-order Taylor gap bounds the preceding one plus the highest homogeneous term. -/
theorem gapOn_taylorDecrement_le_succ [ProperSpace E] (f : E → ℝ) (p : ℕ) (x : E)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    gapOn (taylorDecrement f p x) (closedBall 0 δ) ≤
      gapOn (taylorDecrement f (p + 1) x) (closedBall 0 δ) +
        (iteratedFDeriv ℝ (p + 1) f x).diagonalNorm / ((p + 1)! : ℝ) * δ ^ (p + 1) := by
  apply gapOn_le_gapOn_add (isCompact_closedBall 0 δ) ⟨0, by simpa using hδ⟩
    (continuous_taylorDecrement f (p + 1) x).continuousOn
  intro d hd
  have hn : ‖d‖ ≤ δ := mem_closedBall_zero_iff.mp hd
  have hb := (abs_le.mp (abs_taylorModel_succ_sub_le_diagonal f p x d)).2
  have hp := pow_le_pow_left₀ (norm_nonneg d) hn (p + 1)
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (iteratedFDeriv ℝ (p + 1) f x).diagonalNorm / ((p + 1)! : ℝ) from
      div_nonneg (iteratedFDeriv ℝ (p + 1) f x).diagonalNorm_nonneg (by positivity))
  simp only [taylorDecrement_eq]
  linarith

/-- A sufficiently small highest-order coefficient transfers a gap tolerance to the previous
order. The multiplicative radius assumption also covers a vanishing highest derivative. -/
theorem gapOn_taylorDecrement_pred_le [ProperSpace E] {f : E → ℝ} {p : ℕ} {x : E}
    {δ ε η : ℝ} (hp : 1 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hεη : ε ≤ η)
    (hsmall : 2 * (iteratedFDeriv ℝ (p + 1) f x).diagonalNorm * δ ≤ ((p + 1 : ℕ) : ℝ) * ε)
    (hgap : gapOn (taylorDecrement f (p + 1) x) (closedBall 0 δ) ≤
      ε * δ ^ (p + 1) / ((p + 1)! : ℝ)) :
    gapOn (taylorDecrement f p x) (closedBall 0 δ) ≤ η * δ ^ p / (p ! : ℝ) := by
  have hfac : ((p + 1)! : ℝ) = ((p + 1 : ℕ) : ℝ) * (p ! : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  have hp2 : (2 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ p + 1)
  have hscale : ε * δ + (iteratedFDeriv ℝ (p + 1) f x).diagonalNorm * δ ≤
      ((p + 1 : ℕ) : ℝ) * η := by
    have hεδ : ε * δ ≤ ε := mul_le_of_le_one_right hε hδ1
    have he2 : 2 * ε ≤ ((p + 1 : ℕ) : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hp2 hε
    have heη := mul_le_mul_of_nonneg_left hεη (Nat.cast_nonneg (p + 1))
    nlinarith
  calc
    _ ≤ ε * δ ^ (p + 1) / ((p + 1)! : ℝ) +
        (iteratedFDeriv ℝ (p + 1) f x).diagonalNorm / ((p + 1)! : ℝ) * δ ^ (p + 1) :=
      (gapOn_taylorDecrement_le_succ f p x hδ.le).trans (add_le_add hgap le_rfl)
    _ = (ε * δ + (iteratedFDeriv ℝ (p + 1) f x).diagonalNorm * δ) * δ ^ p /
        (((p + 1 : ℕ) : ℝ) * (p ! : ℝ)) := by rw [hfac, pow_succ]; ring
    _ ≤ (((p + 1 : ℕ) : ℝ) * η) * δ ^ p /
        (((p + 1 : ℕ) : ℝ) * (p ! : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hscale (pow_nonneg hδ.le p))
        (by positivity)
    _ = _ := by field_simp

/-- Local smoothness gives a uniform little-o Taylor estimate on a ball. -/
theorem exists_taylorModel_remainder_le {f : E → ℝ} {p : ℕ} {x : E}
    (hp : 1 ≤ p) (hf : ContDiffAt ℝ p f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : E, ‖s‖ < r →
      |f (x + s) - taylorModel f p x s| ≤ ε * ‖s‖ ^ p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have hc := (hf.iteratedFDeriv_right (i := k + 1) (m := 0) (by simp)).continuousAt
  obtain ⟨r, hr, hbound⟩ := Metric.continuousAt_iff.mp hc
    (ε * ((k + 1)! : ℝ)) (by positivity)
  obtain ⟨R, hR, hsmooth⟩ := Metric.eventually_nhds_iff.mp (hf.eventually (by simp))
  refine ⟨min r R, lt_min hr hR, fun s hs => ?_⟩
  have hsegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖t • s‖ ≤ ‖s‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg s) ht.2
  have hrem := norm_sub_taylorModel_le_holder (n := k) (x := x) (s := s)
    (β := 0) (H := ε * ((k + 1)! : ℝ))
    (by norm_num) (fun t ht => hsmooth (show dist (x + t • s) x < R by
      simpa only [dist_eq_norm, add_sub_cancel_left] using
        (hsegment t ht).trans_lt ((lt_min_iff.mp hs).2))) (fun t ht => ?_)
  · have hprod : (∏ i ∈ Finset.range (k + 1), (((i + 1 : ℕ) : ℝ))) = ((k + 1)! : ℝ) := by
      exact_mod_cast Finset.prod_range_add_one_eq_factorial (k + 1)
    simpa only [add_zero, Real.rpow_zero, mul_one, Real.rpow_natCast,
      hprod,
      mul_div_cancel_right₀ _ (by positivity : ((k + 1)! : ℝ) ≠ 0), Real.norm_eq_abs]
      using hrem
  · have hts : ‖t • s‖ < r :=
      (hsegment t ht).trans_lt ((lt_min_iff.mp hs).1)
    simpa only [Real.rpow_zero, mul_one, dist_eq_norm, add_sub_cancel_left]
      using (hbound (by simpa only [dist_eq_norm, add_sub_cancel_left] using hts)).le

/-- Near a local minimum, a Taylor gap is uniformly smaller than any fixed multiple of the
radius to its order. Smoothness is required only at the expansion point. -/
theorem exists_gapOn_taylorDecrement_le_pow [ProperSpace E] {f : E → ℝ} {p : ℕ} {x : E}
    (hp : 1 ≤ p) (hf : ContDiffAt ℝ p f x) (hmin : IsLocalMin f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ δ : ℝ, 0 ≤ δ → δ < r →
      gapOn (taylorDecrement f p x) (closedBall 0 δ) ≤ ε * δ ^ p := by
  obtain ⟨r, hr, hrem⟩ := exists_taylorModel_remainder_le hp hf hε
  obtain ⟨R, hR, hlocal⟩ := Metric.eventually_nhds_iff.mp hmin
  refine ⟨min r R, lt_min hr hR, fun δ hδ hδr => ?_⟩
  apply gapOn_le ⟨0, by simpa using hδ⟩
  intro d hd
  have hdn : ‖d‖ ≤ δ := mem_closedBall_zero_iff.mp hd
  have hm := hlocal (show dist (x + d) x < R by
    simpa only [dist_eq_norm, add_sub_cancel_left] using
      hdn.trans_lt ((lt_min_iff.mp hδr).2))
  have he := (abs_le.mp (hrem d (hdn.trans_lt ((lt_min_iff.mp hδr).1)))).2
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg d) hdn p) hε.le
  rw [taylorDecrement_eq]
  linarith

/-- At a locally smooth local minimum, the Taylor gap divided by the radius to its order tends
to zero as the radius tends to zero from above. -/
theorem tendsto_gapOn_taylorDecrement_div_pow [ProperSpace E]
    {f : E → ℝ} {p : ℕ} {x : E} (hp : 1 ≤ p) (hf : ContDiffAt ℝ p f x)
    (hmin : IsLocalMin f x) :
    Tendsto (fun δ : ℝ => gapOn (taylorDecrement f p x) (closedBall 0 δ) / δ ^ p)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hg : 0 ≤ gapOn (taylorDecrement f p x) (closedBall 0 δ) :=
      gapOn_nonneg (isCompact_closedBall 0 δ) (continuous_taylorDecrement f p x).continuousOn
        (by simpa using hδ.le) (taylorDecrement_zero f p x)
    exact ha.trans_le (div_nonneg hg (pow_nonneg hδ.le p))
  · intro a ha
    obtain ⟨r, hr, hbound⟩ := exists_gapOn_taylorDecrement_le_pow hp hf hmin
      (show 0 < a / 2 by positivity)
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with δ hδ hδr
    have hb := (div_le_iff₀ (pow_pos hδ p)).mpr (hbound δ hδ.le hδr)
    exact hb.trans_lt (by linarith)

/-- The actual quadratic decrement is the negative linear term minus half the Hessian form. -/
theorem taylorDecrement_two (f : E → ℝ) (x d : E) :
    taylorDecrement f 2 x d = -fderiv ℝ f x d - fderiv ℝ (fderiv ℝ f) x d d / 2 := by
  rw [show 2 = 1 + 1 from rfl, taylorDecrement_succ, taylorDecrement_one,
    iteratedFDeriv_two_apply]
  norm_num
  ring

/-- A zero Taylor gap makes zero displacement a local minimum of the actual Taylor model. -/
theorem isLocalMin_taylorModel_of_gap_eq_zero [ProperSpace E]
    {f : E → ℝ} {p : ℕ} {x : E} {δ : ℝ} (hδ : 0 < δ)
    (hgap : gapOn (taylorDecrement f p x) (closedBall 0 δ) = 0) :
    IsLocalMin (taylorModel f p x) 0 := by
  apply Filter.mem_of_superset (ball_mem_nhds (0 : E) hδ)
  intro d hd
  have h := le_gapOn (isCompact_closedBall 0 δ)
    (continuous_taylorDecrement f p x).continuousOn (mem_closedBall.mpr (mem_ball.mp hd).le)
  rw [hgap, taylorDecrement_eq] at h
  change taylorModel f p x 0 ≤ taylorModel f p x d
  simpa only [taylorModel_zero] using sub_nonpos.mp h

/-- A vanishing quadratic Taylor gap is equivalent to zero derivative and nonnegative Hessian.
The regularity is needed only at the expansion point. -/
theorem gapOn_taylorDecrement_two_eq_zero_iff [ProperSpace E]
    {f : E → ℝ} {x : E} {δ : ℝ} (hf : ContDiffAt ℝ 2 f x) (hδ : 0 < δ) :
    gapOn (taylorDecrement f 2 x) (closedBall 0 δ) = 0 ↔
      fderiv ℝ f x = 0 ∧ ∀ d : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x d d := by
  constructor
  · intro hgap
    have hmin := isLocalMin_taylorModel_of_gap_eq_zero hδ hgap
    have ht : ContDiff ℝ 2 (taylorModel f 2 x) := contDiff_taylorModel _ _ _ _
    have ht' : ContDiff ℝ 1 (fderiv ℝ (taylorModel f 2 x)) :=
      ht.fderiv_right (by norm_num)
    constructor
    · have hD := fderiv_taylorModel_eq_taylorModel_fderiv hf (0 : E)
      simpa only [taylorModel_zero, hmin.fderiv_eq_zero] using hD.symm
    · intro d
      have h := Descent.nonneg_apply_apply_of_isLocalMin hmin
        (Eventually.of_forall fun y => (ht.differentiable (by norm_num) y).hasFDerivAt)
        (ht'.differentiable (by norm_num) 0).hasFDerivAt d
      have he : fderiv ℝ (taylorModel f 2 x) = taylorModel (fderiv ℝ f) 1 x :=
        funext (fderiv_taylorModel_eq_taylorModel_fderiv hf)
      rw [he, fderiv_taylorModel_eq_taylorModel_fderiv (p := 0)
        (hf.fderiv_right (by norm_num)) 0] at h
      simpa using h
  · rintro ⟨hg, hH⟩
    apply (gapOn_eq_zero_iff (isCompact_closedBall 0 δ)
      (continuous_taylorDecrement f 2 x).continuousOn
      (by simpa using hδ.le) (taylorDecrement_zero f 2 x)).mpr
    intro d _
    rw [taylorDecrement_two, hg, zero_apply]
    linarith [hH d]

/-- A quadratic gap tolerance bounds every unit-direction Hessian curvature below, without
positive definiteness or symmetry assumptions. -/
theorem quadratic_curvature_lower_bound [ProperSpace E]
    {f : E → ℝ} {x : E} {δ ε : ℝ} (hδ : 0 < δ)
    (hgap : gapOn (taylorDecrement f 2 x) (closedBall 0 δ) ≤ ε * δ ^ 2 / 2) :
    ∀ d : E, -ε * ‖d‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x d d := by
  have hu : ∀ v : E, ‖v‖ = 1 → -ε ≤ fderiv ℝ (fderiv ℝ f) x v v := by
    intro v hv
    have hpos := (le_gapOn (isCompact_closedBall 0 δ)
      (continuous_taylorDecrement f 2 x).continuousOn
      (show δ • v ∈ closedBall (0 : E) δ by simp [norm_smul, hv, abs_of_pos hδ])).trans hgap
    have hneg := (le_gapOn (isCompact_closedBall 0 δ)
      (continuous_taylorDecrement f 2 x).continuousOn
      (show (-δ) • v ∈ closedBall (0 : E) δ by simp [norm_smul, hv, abs_of_pos hδ])).trans hgap
    simp only [taylorDecrement_two, map_smul, smul_apply, smul_eq_mul] at hpos hneg
    nlinarith [sq_pos_of_pos hδ]
  intro d
  by_cases hd : d = 0
  · simp [hd]
  have hn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have hv : ‖(‖d‖⁻¹ : ℝ) • d‖ = 1 := by simp [norm_smul, hn]
  have hb := hu _ hv
  simp only [map_smul, smul_apply, smul_eq_mul] at hb
  have he : ‖d‖⁻¹ * (‖d‖⁻¹ * fderiv ℝ (fderiv ℝ f) x d d) =
      fderiv ℝ (fderiv ℝ f) x d d / ‖d‖ ^ 2 := by ring
  rw [he] at hb
  exact (le_div_iff₀ (sq_pos_of_ne_zero hn)).mp hb

/-- A quadratic Taylor-gap test bounds the derivative norm with an explicit Hessian-dependent
constant. The same formula applies to zero, semidefinite, and indefinite Hessians. -/
theorem norm_fderiv_le_of_quadratic_gap [ProperSpace E]
    {f : E → ℝ} {x : E} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hgap : gapOn (taylorDecrement f 2 x) (closedBall 0 δ) ≤ ε * δ ^ 2 / 2) :
    ‖fderiv ℝ f x‖ ≤ δ * ((1 + ‖fderiv ℝ (fderiv ℝ f) x‖) / 2) * Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hs1 : Real.sqrt ε ≤ 1 := (Real.sqrt_le_one).mpr hε1
  have hs2 : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
  let t := δ * Real.sqrt ε
  have ht : 0 < t := mul_pos hδ hs
  have htd : t ≤ δ := mul_le_of_le_one_right hδ.le hs1
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hp := (le_gapOn (isCompact_closedBall 0 δ)
    (continuous_taylorDecrement f 2 x).continuousOn
    (show t • v ∈ closedBall (0 : E) δ by
      simpa [norm_smul, hv, abs_of_pos ht] using htd)).trans hgap
  have hm := (le_gapOn (isCompact_closedBall 0 δ)
    (continuous_taylorDecrement f 2 x).continuousOn
    (show (-t) • v ∈ closedBall (0 : E) δ by
      simpa [norm_smul, hv, abs_of_pos ht] using htd)).trans hgap
  simp only [taylorDecrement_two, map_smul, smul_apply, smul_eq_mul] at hp hm
  have hH := (abs_le.mp (ContinuousLinearMap.abs_apply_self_le
    (fderiv ℝ (fderiv ℝ f) x) v)).2
  rw [hv, one_pow, mul_one] at hH
  have ht2 : t ^ 2 = δ ^ 2 * ε := by dsimp [t]; nlinarith [sq_nonneg δ]
  have hc : t * (δ * ((1 + ‖fderiv ℝ (fderiv ℝ f) x‖) / 2) * Real.sqrt ε) =
      ε * δ ^ 2 / 2 + ‖fderiv ℝ (fderiv ℝ f) x‖ * t ^ 2 / 2 := by
    dsimp [t]
    nlinarith [sq_nonneg δ]
  rw [Real.norm_eq_abs]
  apply (mul_le_mul_iff_right₀ ht).mp
  rw [hc]
  have hmul := mul_le_mul_of_nonneg_right hH (sq_nonneg t)
  rcases le_total 0 (fderiv ℝ f x v) with hg | hg
  · rw [abs_of_nonneg hg]
    nlinarith
  · rw [abs_of_nonpos hg]
    nlinarith

/-- A nonnegative symmetric bilinear form has the same diagonal zero set and covector kernel. -/
theorem bilinear_apply_eq_zero_iff {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hsym : ∀ u v, B u v = B v u) (hpos : ∀ u, 0 ≤ B u u) (d : E) :
    B d d = 0 ↔ B d = 0 := by
  constructor
  · intro hd
    ext v
    change B d v = 0
    have hv := hpos v
    have hp := hpos (d + (-(B d v) / (B v v + 1)) • v)
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hd, zero_add,
      hsym v d] at hp
    have hden : B v v + 1 ≠ 0 := by linarith
    have hh := mul_nonneg hp (sq_nonneg (B v v + 1))
    field_simp at hh
    nlinarith [sq_nonneg (B d v), mul_nonneg (sq_nonneg (B d v)) hv]
  · intro hd
    simp [hd]

/-- The common first derivative and Hessian kernels as a bundled linear subspace. -/
def derivativeKernel (f : E → ℝ) (x : E) : Submodule ℝ E :=
  (fderiv ℝ f x).ker ⊓ (fderiv ℝ (fderiv ℝ f) x).ker

/-- Membership is vanishing of the first derivative and of the Hessian covector. -/
@[simp] theorem mem_derivativeKernel {f : E → ℝ} {x d : E} :
    d ∈ derivativeKernel f x ↔ fderiv ℝ f x d = 0 ∧ fderiv ℝ (fderiv ℝ f) x d = 0 :=
  Iff.rfl

/-- At a point with nonnegative Hessian the bundled derivative kernel is exactly the common
first and second diagonal zero set. -/
theorem mem_derivativeKernel_iff {f : E → ℝ} {x d : E}
    (hf : ContDiffAt ℝ 2 f x) (hH : ∀ u, 0 ≤ fderiv ℝ (fderiv ℝ f) x u u) :
    d ∈ derivativeKernel f x ↔
      fderiv ℝ f x d = 0 ∧ fderiv ℝ (fderiv ℝ f) x d d = 0 := by
  rw [mem_derivativeKernel, bilinear_apply_eq_zero_iff (hf.isSymmSndFDerivAt (by norm_num)) hH]

/-- On directions with vanishing first and second terms, the cubic tensor is controlled by
the actual third-order gap. Both signs of the feasible direction are used. -/
theorem abs_cubic_le_gapOn [ProperSpace E] {f : E → ℝ} {x d : E} {δ : ℝ}
    (hδ : 0 < δ) (hd : ‖d‖ ≤ 1) (hg : fderiv ℝ f x d = 0)
    (hH : fderiv ℝ (fderiv ℝ f) x d d = 0) :
    |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤
      6 * gapOn (taylorDecrement f 3 x) (closedBall 0 δ) / δ ^ 3 := by
  have hpos := le_gapOn (isCompact_closedBall 0 δ)
    (continuous_taylorDecrement f 3 x).continuousOn
    (show δ • d ∈ closedBall (0 : E) δ by
      simpa [norm_smul, abs_of_pos hδ] using mul_le_mul_of_nonneg_left hd hδ.le)
  have hneg := le_gapOn (isCompact_closedBall 0 δ)
    (continuous_taylorDecrement f 3 x).continuousOn
    (show (-δ) • d ∈ closedBall (0 : E) δ by
      simpa [norm_smul, abs_of_pos hδ] using mul_le_mul_of_nonneg_left hd hδ.le)
  rw [show 3 = 2 + 1 from rfl, taylorDecrement_succ, taylorDecrement_two] at hpos hneg
  simp only [map_smul, smul_apply, smul_eq_mul, hg, hH, mul_zero, neg_zero, zero_sub,
    ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hpos hneg
  norm_num at hpos hneg
  rw [le_div_iff₀ (pow_pos hδ 3)]
  rcases le_total 0 (iteratedFDeriv ℝ 3 f x (fun _ => d)) with ht | ht
  · rw [abs_of_nonneg ht]
    nlinarith
  · rw [abs_of_nonpos ht]
    nlinarith

end Optimization.TaylorCriticality

namespace Optimization.TaylorCriticality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A quadratic Taylor-gap tolerance bounds the least Hessian Rayleigh curvature below. -/
theorem leastCurvature_lower_bound_of_quadratic_gap [Nontrivial E]
    {f : E → ℝ} {x : E} {δ ε : ℝ} (hδ : 0 < δ)
    (hgap : gapOn (taylorDecrement f 2 x) (closedBall 0 δ) ≤ ε * δ ^ 2 / 2) :
    -ε ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) x) :=
  (le_leastCurvature_iff _ _).mpr (quadratic_curvature_lower_bound hδ hgap)

/-- The actual cubic derivative tensor after the exact orthogonal projection onto the common
first derivative and Hessian kernels. -/
def projectedCubic (f : E → ℝ) (x : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ :=
  (iteratedFDeriv ℝ 3 f x).compContinuousLinearMap
    (fun _ => (derivativeKernel f x).starProjection)

/-- The diagonal norm of the orthogonally projected actual cubic tensor is bounded by the
third-order gap divided by its factorial radius scale. -/
theorem projectedCubic_diagonalNorm_le {f : E → ℝ} {x : E} {δ : ℝ} (hδ : 0 < δ) :
    (projectedCubic f x).diagonalNorm ≤
      6 * gapOn (taylorDecrement f 3 x) (closedBall 0 δ) / δ ^ 3 := by
  have hg : 0 ≤ gapOn (taylorDecrement f 3 x) (closedBall 0 δ) :=
    gapOn_nonneg (isCompact_closedBall 0 δ) (continuous_taylorDecrement f 3 x).continuousOn
      (by simpa using hδ.le) (taylorDecrement_zero f 3 x)
  apply ContinuousMultilinearMap.diagonalNorm_le _ (by positivity)
  intro v hv
  have hm := mem_derivativeKernel.mp ((derivativeKernel f x).starProjection_apply_mem v)
  have hn := (derivativeKernel f x).norm_starProjection_apply_le v
  rw [hv] at hn
  change |iteratedFDeriv ℝ 3 f x
    (fun _ => (derivativeKernel f x).starProjection v)| ≤ _
  exact abs_cubic_le_gapOn hδ hn hm.1 (by simp [hm.2])

/-- If the normalized cubic gap tends to zero then the cubic tensor vanishes on the common
first derivative and Hessian kernel. -/
theorem cubic_eq_zero_of_tendsto_gap_div_cube {f : E → ℝ} {x : E}
    (hlim : Tendsto (fun δ : ℝ => gapOn (taylorDecrement f 3 x) (closedBall 0 δ) / δ ^ 3)
      (𝓝[>] 0) (𝓝 0)) :
    ∀ d ∈ derivativeKernel f x, iteratedFDeriv ℝ 3 f x (fun _ => d) = 0 := by
  have hnorm : (projectedCubic f x).diagonalNorm = 0 := by
    apply le_antisymm _ (ContinuousMultilinearMap.diagonalNorm_nonneg _)
    have ht : Tendsto (fun δ : ℝ =>
        6 * gapOn (taylorDecrement f 3 x) (closedBall 0 δ) / δ ^ 3)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero, mul_div_assoc] using hlim.const_mul 6
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact projectedCubic_diagonalNorm_le hδ
  intro d hd
  have h := (projectedCubic f x).norm_diagonal_le_diagonalNorm_mul (by norm_num) d
  rw [hnorm, zero_mul] at h
  have hz := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  change iteratedFDeriv ℝ 3 f x (fun _ => (derivativeKernel f x).starProjection d) = 0 at hz
  simpa only [(derivativeKernel f x).starProjection_eq_self_iff.mpr hd] using hz

end Optimization.TaylorCriticality
