import Numlib.Optimization.LocalCurvature
import Numlib.Optimization.TrustRegionSecondOrder
import Mathlib.Data.Nat.Log

/-!
# Cubic steps near a nondegenerate critical point

The actual cubic derivative contains the step-dependent shift `sigma * ‖s‖ / 2`.
Positive Hessian curvature and a relative residual bound therefore give a step bound
which does not replace this shift by a positive constant.
-/

noncomputable section
namespace Optimization.CubicRegularization
open RegularizedTaylorModel InnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The cubic derivative evaluated on its step, with the genuine cubic shift. -/
theorem fderiv_cubicModel_apply_self {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (s : E) (sigma : ℝ) :
    fderiv ℝ (cubicModel f x sigma) s s =
      fderiv ℝ f x s + fderiv ℝ (fderiv ℝ f) x s s + sigma / 2 * ‖s‖ ^ 3 := by
  change fderiv ℝ (regularizedModel f 2 x sigma 6 3) s s = _
  rw [fderiv_regularizedModel f 2 x s sigma 6 (by norm_num : (1 : ℝ) < 3),
    fderiv_taylorModel_eq_taylorModel_fderiv (p := 1) hf, taylorModel_one,
    fderiv_norm_rpow s (by norm_num : (1 : ℝ) < 3)]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
    real_inner_self_eq_norm_sq]
  norm_num only [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one]
  ring

/-- Positive Hessian curvature and relative model stationarity bound the step linearly
in the current gradient. No strictly positive constant is extracted from the cubic shift. -/
theorem norm_step_le_of_relative_residual {f : E → ℝ} {x s : E} {sigma theta mu : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hsigma : 0 ≤ sigma) (hmu : 0 < mu)
    (hcurv : mu * ‖s‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x s s)
    (hres : ‖fderiv ℝ (cubicModel f x sigma) s‖ ≤ theta * ‖gradient f x‖) :
    ‖s‖ ≤ (1 + theta) / mu * ‖gradient f x‖ := by
  by_cases hs : s = 0
  · rw [hs, norm_zero]
    have hr : 0 ≤ theta * ‖gradient f x‖ := (norm_nonneg _).trans hres
    rw [div_mul_eq_mul_div]
    exact div_nonneg (by nlinarith [norm_nonneg (gradient f x)]) hmu.le
  have hn := norm_pos_iff.mpr hs
  have hd := fderiv_cubicModel_apply_self hf s sigma
  have hm := (le_abs_self (fderiv ℝ (cubicModel f x sigma) s s)).trans
    ((fderiv ℝ (cubicModel f x sigma) s).le_opNorm s)
  have hg := (neg_abs_le (fderiv ℝ f x s)).trans'
    (neg_le_neg ((fderiv ℝ f x).le_opNorm s))
  have hgn : ‖fderiv ℝ f x‖ = ‖gradient f x‖ := by simp [gradient]
  rw [hgn] at hg
  have hr := mul_le_mul_of_nonneg_right hres hn.le
  have hp : 0 ≤ sigma / 2 * ‖s‖ ^ 3 := by positivity
  have hb : mu * ‖s‖ ≤ (1 + theta) * ‖gradient f x‖ := by
    nlinarith only [hm, hg, hr, hcurv, hd, hp, hn]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hmu).mpr (by nlinarith only [hb])

/-- A Lipschitz Hessian bounds distance to a nondegenerate stationary reference by the
actual gradient, as long as the point lies within the stated Taylor radius. -/
theorem HessianLipschitz.distance_le_gradient {f : E → ℝ} {L mu : ℝ}
    (hf : HessianLipschitz f L) {xstar y : E}
    (hg : fderiv ℝ f xstar = 0) (hmu : 0 < mu)
    (hcurv : mu * ‖y - xstar‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ f) xstar (y - xstar) (y - xstar))
    (hy : L * ‖y - xstar‖ ≤ mu) :
    ‖y - xstar‖ ≤ 2 / mu * ‖gradient f y‖ := by
  by_cases hz : y - xstar = 0
  · simp only [hz, norm_zero]
    positivity
  have hd := norm_pos_iff.mpr hz
  have hr := hf.derivative_remainder xstar (y - xstar)
  rw [fderiv_taylorModel_eq_taylorModel_fderiv (p := 1) hf.smooth.contDiffAt,
    taylorModel_one, hg, zero_add, add_sub_cancel] at hr
  have hn := norm_le_norm_sub_add (fderiv ℝ (fderiv ℝ f) xstar (y - xstar))
    (fderiv ℝ f y)
  rw [norm_sub_rev] at hn
  have he := (le_abs_self (fderiv ℝ (fderiv ℝ f) xstar (y - xstar) (y - xstar))).trans
    ((fderiv ℝ (fderiv ℝ f) xstar (y - xstar)).le_opNorm (y - xstar))
  have hg' : ‖fderiv ℝ f y‖ = ‖gradient f y‖ := by simp [gradient]
  rw [hg'] at hn
  have hprod := mul_le_mul_of_nonneg_right (hn.trans (add_le_add hr le_rfl)) hd.le
  have hrem := mul_le_mul_of_nonneg_right hy (sq_nonneg ‖y - xstar‖)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hmu).mpr
  nlinarith only [he, hcurv, hprod, hrem, hd]

omit [CompleteSpace E] in
/-- Curvature and a sufficiently small step make the actual Taylor ratio very successful.
The model residual is quadratic in the step norm and the objective is evaluated exactly. -/
theorem ratio_ge_of_curvature_residual {f : E → ℝ} {L sigma theta mu eta : ℝ}
    (hf : HessianLipschitz f L) {x s : E} (hsigma : 0 ≤ sigma)
    (hmu : 0 < mu) (heta : eta < 1)
    (hcurv : mu * ‖s‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x s s)
    (hres : ‖fderiv ℝ (cubicModel f x sigma) s‖ ≤ theta / 2 * ‖s‖ ^ 2)
    (hsmall : theta * ‖s‖ ≤ mu / 2)
    (hratio : L * ‖s‖ ≤ 3 / 2 * (1 - eta) * mu) :
    eta ≤ ratio f x s sigma := by
  by_cases hs : s = 0
  · simp only [ratio, hs, ↓reduceIte]
    exact heta.le
  have hn := norm_pos_iff.mpr hs
  have hd := fderiv_cubicModel_apply_self (x := x) hf.smooth.contDiffAt s sigma
  have hm := (le_abs_self (fderiv ℝ (cubicModel f x sigma) s s)).trans
    ((fderiv ℝ (cubicModel f x sigma) s).le_opNorm s)
  have hr := mul_le_mul_of_nonneg_right hres hn.le
  have ht : taylorModel f 2 x s = f x + fderiv ℝ f x s +
      fderiv ℝ (fderiv ℝ f) x s s / 2 := by
    rw [show 2 = 1 + 1 from rfl, taylorModel_succ, taylorModel_one,
      iteratedFDeriv_two_apply]
    norm_num
    ring
  have hsm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖s‖)
  have hc : 0 ≤ sigma / 2 * ‖s‖ ^ 3 := by positivity
  have hp : mu / 4 * ‖s‖ ^ 2 ≤ f x - taylorModel f 2 x s := by
    rw [ht]
    nlinarith only [hd, hm, hr, hcurv, hsm, hc]
  have hp0 : 0 < f x - taylorModel f 2 x s :=
    (mul_pos (by positivity) (sq_pos_of_pos hn)).trans_le hp
  have he := (abs_le.mp (hf.value_remainder x s)).2
  have he' := mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖s‖)
  have hp' := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ 1 - eta)
  rw [ratio, ite_eq_right hs, taylorModel_zero, le_div_iff₀ hp0]
  nlinarith only [he, he', hp']

/-- The valid curvature-to-gradient step factor on a half-curvature neighbourhood. -/
def localStepFactor (lambda theta : ℝ) : ℝ := 2 * (1 + theta) / lambda

/-- A positive local threshold obtained from the actual cubic shift. The five bounds
control the quadratic recurrence, the Taylor radius, return to the original ball,
and the two estimates required for very successful acceptance. -/
def localQuadraticThreshold (lambda L theta M eta : ℝ) : ℝ :=
  let C := localStepFactor lambda theta
  min (1 / (((L + theta + M) / 2) * C ^ 2))
    (min (lambda / (4 * L * C))
      (min (lambda ^ 2 / (16 * L))
        (min (3 * (1 - eta) * lambda / (4 * L * C)) (lambda / (4 * theta * C)))))

/-- The local step factor is positive for positive curvature and nonnegative tolerance. -/
theorem localStepFactor_pos {lambda theta : ℝ} (hlambda : 0 < lambda) (htheta : 0 ≤ theta) :
    0 < localStepFactor lambda theta := by unfold localStepFactor; positivity

/-- Every constraint defining the corrected local threshold is strictly positive. -/
theorem localQuadraticThreshold_pos {lambda L theta M eta : ℝ}
    (hlambda : 0 < lambda) (hL : 0 < L) (htheta : 0 < theta) (hM : 0 ≤ M)
    (heta : eta < 1) : 0 < localQuadraticThreshold lambda L theta M eta := by
  have hC := localStepFactor_pos hlambda htheta.le
  unfold localQuadraticThreshold
  dsimp only
  positivity

/-- The five operational inequalities encoded by the corrected local threshold. -/
theorem localQuadraticThreshold_bounds {lambda L theta M eta : ℝ}
    (hlambda : 0 < lambda) (hL : 0 < L) (htheta : 0 < theta) (hM : 0 ≤ M) :
    let C := localStepFactor lambda theta
    let R := localQuadraticThreshold lambda L theta M eta
    ((L + theta + M) / 2) * C ^ 2 * R ≤ 1 ∧
      C * R ≤ lambda / (4 * L) ∧ R ≤ lambda ^ 2 / (16 * L) ∧
      L * (C * R) ≤ 3 * (1 - eta) * lambda / 4 ∧ theta * (C * R) ≤ lambda / 4 := by
  dsimp only
  have hC := localStepFactor_pos hlambda htheta.le
  have hA : 0 < (L + theta + M) / 2 := by positivity
  let R := localQuadraticThreshold lambda L theta M eta
  change ((L + theta + M) / 2) * localStepFactor lambda theta ^ 2 * R ≤ 1 ∧ _
  have hh : R ≤ localQuadraticThreshold lambda L theta M eta := le_rfl
  rw [localQuadraticThreshold, le_min_iff, le_min_iff, le_min_iff, le_min_iff] at hh
  obtain ⟨h1, h2, h3, h4, h5⟩ := hh
  have hb1 := (le_div_iff₀ (show 0 < ((L + theta + M) / 2) *
    localStepFactor lambda theta ^ 2 by positivity)).mp h1
  have hb2 := (le_div_iff₀ (show 0 < 4 * L * localStepFactor lambda theta by positivity)).mp h2
  have hb4 := (le_div_iff₀ (show 0 < 4 * L * localStepFactor lambda theta by positivity)).mp h4
  have hb5 := (le_div_iff₀ (show 0 < 4 * theta * localStepFactor lambda theta by positivity)).mp h5
  refine ⟨by nlinarith only [hb1], ?_, h3, by nlinarith only [hb4], by nlinarith only [hb5]⟩
  apply (le_div_iff₀ (by positivity : 0 < 4 * L)).mpr
  nlinarith only [hb2]

/-- An actual cubic run with strengthened relative residual is quadratically convergent
and very successful inside the corrected region. Its successor stays in the same region.
All bounds concern actual derivatives, actual iterates, and the actual Taylor ratio. -/
theorem IsRun.local_step [Nontrivial E] {p : ParameterUpdates.RegularizationParameters}
    {f : E → ℝ} {x s : ℕ → E} {sigma : ℕ → ℝ} {L theta M lambda : ℝ}
    (h : IsRun p theta f x s sigma) (hf : HessianLipschitz f L)
    (hL : 0 < L) (htheta : 0 < theta) (hlambda : 0 < lambda)
    {xstar : E} (hstar : lambda ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) xstar))
    (hg : fderiv ℝ f xstar = 0) (k : ℕ) (hM : sigma k ≤ M)
    (hrel : ‖fderiv ℝ (cubicModel f (x k) (sigma k)) (s k)‖ ≤
      theta * ‖gradient f (x k)‖)
    (hx : ‖x k - xstar‖ ≤ lambda / (4 * L))
    (hsmall : ‖gradient f (x k)‖ ≤ localQuadraticThreshold lambda L theta M p.eta2) :
    p.eta2 ≤ ratio f (x k) (s k) (sigma k) ∧
      ‖x (k + 1) - xstar‖ ≤ lambda / (4 * L) ∧
      ‖gradient f (x (k + 1))‖ ≤
        ‖gradient f (x k)‖ ^ 2 / localQuadraticThreshold lambda L theta M p.eta2 := by
  let C := localStepFactor lambda theta
  let R := localQuadraticThreshold lambda L theta M p.eta2
  have hsigma := (h.toRegularizationUpdates.pos k).le
  have hM0 : 0 ≤ M := hsigma.trans hM
  have hC : 0 < C := localStepFactor_pos hlambda htheta.le
  have hR : 0 < R := localQuadraticThreshold_pos hlambda hL htheta hM0 p.eta2_lt_one
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
    localQuadraticThreshold_bounds (eta := p.eta2) hlambda hL htheta hM0
  change ((L + theta + M) / 2) * C ^ 2 * R ≤ 1 at hb1
  change C * R ≤ _ at hb2
  change R ≤ _ at hb3
  change L * (C * R) ≤ _ at hb4
  change theta * (C * R) ≤ _ at hb5
  have hhalf : ‖x k - xstar‖ ≤ lambda / (2 * L) := by
    apply hx.trans
    apply div_le_div_of_nonneg_left hlambda.le (by positivity)
    linarith
  have hcurv : lambda / 2 * ‖s k‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) (x k) (s k) (s k) :=
    apply_self_ge_half_on_closedBall hL hstar (hf.curried_bound (x k) xstar)
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hhalf) (s k)
  have hs : ‖s k‖ ≤ C * ‖gradient f (x k)‖ := by
    have hh := norm_step_le_of_relative_residual hf.smooth.contDiffAt hsigma
      (by positivity : 0 < lambda / 2) hcurv hrel
    convert hh using 1
    dsimp [C, localStepFactor]
    ring
  have hsR : ‖s k‖ ≤ C * R := hs.trans (mul_le_mul_of_nonneg_left hsmall hC.le)
  have hr := ratio_ge_of_curvature_residual hf hsigma (by positivity : 0 < lambda / 2)
    p.eta2_lt_one hcurv (h.residual k)
    (by nlinarith only [mul_le_mul_of_nonneg_left hsR htheta.le, hb5])
    (by nlinarith only [mul_le_mul_of_nonneg_left hsR hL.le, hb4])
  have hi : x (k + 1) = x k + s k := by
    rw [h.iterate k, ite_eq_left (p.eta_le.trans hr)]
  have hnext : ‖gradient f (x (k + 1))‖ ≤ ((L + theta + M) / 2) * ‖s k‖ ^ 2 := by
    rw [hi]
    have hh := h.trial_derivative_bound hf k
    have he : ‖fderiv ℝ f (x k + s k)‖ = ‖gradient f (x k + s k)‖ := by simp [gradient]
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  have ha : 0 ≤ (L + theta + M) / 2 := by positivity
  have hsq := pow_le_pow_left₀ (norm_nonneg (s k)) hs 2
  have hrec : ‖gradient f (x (k + 1))‖ ≤ ‖gradient f (x k)‖ ^ 2 / R := by
    apply (le_div_iff₀ hR).mpr
    have ht := mul_le_mul_of_nonneg_right (hnext.trans
      (mul_le_mul_of_nonneg_left hsq ha)) hR.le
    have hb := mul_le_mul_of_nonneg_right hb1 (sq_nonneg ‖gradient f (x k)‖)
    nlinarith only [ht, hb]
  have hnextR : ‖gradient f (x (k + 1))‖ ≤ R := by
    apply hrec.trans
    apply (div_le_iff₀ hR).mpr
    nlinarith only [hsmall, norm_nonneg (gradient f (x k))]
  have hd : L * ‖x (k + 1) - xstar‖ ≤ lambda := by
    have ht : ‖x (k + 1) - xstar‖ ≤ lambda / (4 * L) + lambda / (4 * L) := by
      rw [hi, add_sub_right_comm]
      exact (norm_add_le _ _).trans (add_le_add hx (hsR.trans hb2))
    have hh := mul_le_mul_of_nonneg_left ht hL.le
    have he : L * (lambda / (4 * L) + lambda / (4 * L)) = lambda / 2 := by field_simp; ring
    rw [he] at hh
    linarith
  have hdist := hf.distance_le_gradient hg hlambda
    ((le_leastCurvature_iff _ _).mp hstar (x (k + 1) - xstar)) hd
  have hret : ‖x (k + 1) - xstar‖ ≤ lambda / (4 * L) := by
    have ht := hdist.trans (mul_le_mul_of_nonneg_left (hnextR.trans hb3) (by positivity))
    apply ht.trans
    field_simp
    nlinarith only [hlambda]
  exact ⟨hr, hret, hrec⟩

/-- Once an actual strengthened-residual run enters the corrected region, every later
iterate remains there, every trial is very successful, and the quadratic recurrence holds. -/
theorem IsRun.local_invariant [Nontrivial E] {p : ParameterUpdates.RegularizationParameters}
    {f : E → ℝ} {x s : ℕ → E} {sigma : ℕ → ℝ} {L theta M lambda : ℝ}
    (h : IsRun p theta f x s sigma) (hf : HessianLipschitz f L)
    (hL : 0 < L) (htheta : 0 < theta) (hlambda : 0 < lambda)
    {xstar : E} (hstar : lambda ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) xstar))
    (hg : fderiv ℝ f xstar = 0) (hM : ∀ k, sigma k ≤ M)
    (hrel : ∀ k, ‖fderiv ℝ (cubicModel f (x k) (sigma k)) (s k)‖ ≤
      theta * ‖gradient f (x k)‖) (k0 : ℕ)
    (hx : ‖x k0 - xstar‖ ≤ lambda / (4 * L))
    (hsmall : ‖gradient f (x k0)‖ ≤ localQuadraticThreshold lambda L theta M p.eta2) :
    ∀ j, ‖x (k0 + j) - xstar‖ ≤ lambda / (4 * L) ∧
      ‖gradient f (x (k0 + j))‖ ≤ localQuadraticThreshold lambda L theta M p.eta2 ∧
      p.eta2 ≤ ratio f (x (k0 + j)) (s (k0 + j)) (sigma (k0 + j)) ∧
      ‖gradient f (x (k0 + j + 1))‖ ≤ ‖gradient f (x (k0 + j))‖ ^ 2 /
        localQuadraticThreshold lambda L theta M p.eta2 := by
  let R := localQuadraticThreshold lambda L theta M p.eta2
  have hM0 := (h.toRegularizationUpdates.pos 0).le.trans (hM 0)
  have hR : 0 < R := localQuadraticThreshold_pos hlambda hL htheta hM0 p.eta2_lt_one
  have hinv : ∀ j, ‖x (k0 + j) - xstar‖ ≤ lambda / (4 * L) ∧
      ‖gradient f (x (k0 + j))‖ ≤ R := by
    intro j
    induction j with
    | zero => simpa only [Nat.add_zero] using And.intro hx hsmall
    | succ j ih =>
      obtain ⟨_, hd, hr⟩ := h.local_step hf hL htheta hlambda hstar hg
        (k0 + j) (hM _) (hrel _) ih.1 ih.2
      refine ⟨by simpa only [Nat.add_assoc] using hd, ?_⟩
      have hb : ‖gradient f (x (k0 + j))‖ ^ 2 / R ≤ R := by
        apply (div_le_iff₀ hR).mpr
        nlinarith only [ih.2, norm_nonneg (gradient f (x (k0 + j)))]
      simpa only [Nat.add_assoc] using hr.trans hb
  intro j
  obtain ⟨hr, _, hrec⟩ := h.local_step hf hL htheta hlambda hstar hg
    (k0 + j) (hM _) (hrel _) (hinv j).1 (hinv j).2
  exact ⟨(hinv j).1, (hinv j).2, hr, hrec⟩

end Optimization.CubicRegularization

namespace Optimization

/-- An integer double-logarithmic bound, including the zero-iteration branch.
Rounding the ratio upward before taking natural ceiling logarithms avoids undefined
or negative real logarithmic bounds. -/
def quadraticIterationBound (scale epsilon : ℝ) : ℕ :=
  Nat.clog 2 (Nat.clog 2 ⌈scale / epsilon⌉₊)

/-- The integer double logarithm makes the doubly exponential envelope meet the tolerance. -/
theorem quadraticIterationBound_spec {scale epsilon : ℝ} (he : 0 < epsilon) :
    scale / (2 : ℝ) ^ (2 ^ quadraticIterationBound scale epsilon) ≤ epsilon := by
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈scale / epsilon⌉₊
  have h2 := Nat.le_pow_clog (by norm_num : 1 < 2) (Nat.clog 2 ⌈scale / epsilon⌉₊)
  have h3 := h1.trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h2)
  have hreal : (⌈scale / epsilon⌉₊ : ℝ) ≤
      (2 : ℝ) ^ (2 ^ quadraticIterationBound scale epsilon) := by
    exact_mod_cast h3
  have hb := (Nat.le_ceil (scale / epsilon)).trans hreal
  apply (div_le_iff₀ (by positivity :
    0 < (2 : ℝ) ^ (2 ^ quadraticIterationBound scale epsilon))).mpr
  exact (div_le_iff₀ he).mp hb |>.trans_eq (by ring)

/-- A positive quadratic recurrence started below half its scale has a doubly exponential
upper bound. This scalar fact makes no assumption about optimization algorithms. -/
theorem le_double_exponential_of_quadratic_recurrence {g : ℕ → ℝ} {scale : ℝ}
    (hs : 0 < scale) (hg : ∀ k, 0 ≤ g k) (h0 : g 0 ≤ scale / 2)
    (hrec : ∀ k, g (k + 1) ≤ g k ^ 2 / scale) :
    ∀ k, g k ≤ scale / (2 : ℝ) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => simpa only [pow_zero, pow_one] using h0
  | succ k ih =>
    have hh := (hrec k).trans (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (hg k) ih 2) hs.le)
    apply hh.trans_eq
    rw [pow_succ (2 : ℕ) k, pow_mul]
    field_simp

/-- A quadratic recurrence reaches the desired accuracy within the integer double-log bound. -/
theorem quadratic_recurrence_meets_tolerance {g : ℕ → ℝ} {scale epsilon : ℝ}
    (hs : 0 < scale) (he : 0 < epsilon) (hg : ∀ k, 0 ≤ g k)
    (h0 : g 0 ≤ scale / 2) (hrec : ∀ k, g (k + 1) ≤ g k ^ 2 / scale) :
    g (quadraticIterationBound scale epsilon) ≤ epsilon :=
  (le_double_exponential_of_quadratic_recurrence hs hg h0 hrec _).trans
    (quadraticIterationBound_spec he)

/-- Counting a prefix is monotone in its endpoint. -/
theorem ParameterUpdates.successCount_mono (accepted : ℕ → Prop) {i j : ℕ} (hij : i ≤ j) :
    ParameterUpdates.successCount accepted i ≤ ParameterUpdates.successCount accepted j := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

/-- Extending a prefix by `j` trials can add at most `j` successes. -/
theorem ParameterUpdates.successCount_add_le (accepted : ℕ → Prop) (i j : ℕ) :
    ParameterUpdates.successCount accepted (i + j) ≤
      ParameterUpdates.successCount accepted i + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hh := ParameterUpdates.successCount_succ_le accepted (i + j)
    simpa only [Nat.add_assoc] using hh.trans (Nat.add_le_add_right ih 1)

/-- A threshold bounded by `upper/2` can be reduced to an independent local threshold,
with a parameter-dependent multiplicative cost. -/
theorem phase_entry_scale_bound {zeta upper R : ℝ} (hz : 0 < zeta)
    (hR : 0 < R) (hzupper : zeta ≤ upper / 2) :
    zeta ≤ max 1 (upper / R) * min zeta (R / 2) := by
  by_cases h : zeta ≤ R / 2
  · rw [min_eq_left h]
    exact le_mul_of_one_le_left hz.le (le_max_left _ _)
  · rw [min_eq_right (le_of_not_ge h)]
    have hh := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (upper / R))
      (by positivity : 0 ≤ R / 2)
    have he : upper / R * (R / 2) = upper / 2 := by field_simp
    rw [he] at hh
    exact hzupper.trans hh

/-- The smaller entry threshold costs only a fixed multiple of the original
three-halves global budget. -/
theorem phase_entry_budget {zeta upper R gap : ℝ} (hz : 0 < zeta)
    (hR : 0 < R) (hzupper : zeta ≤ upper / 2) (hgap : 0 ≤ gap) :
    gap / min zeta (R / 2) ^ (3 / 2 : ℝ) ≤
      max 1 (upper / R) ^ (3 / 2 : ℝ) * (gap / zeta ^ (3 / 2 : ℝ)) := by
  have ht : 0 < min zeta (R / 2) := lt_min hz (by positivity)
  have hD : 0 < max 1 (upper / R) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb := Real.rpow_le_rpow hz.le (phase_entry_scale_bound hz hR hzupper)
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow hD.le ht.le] at hb
  apply (div_le_iff₀ (Real.rpow_pos_of_pos ht _)).mpr
  have he : max 1 (upper / R) ^ (3 / 2 : ℝ) * (gap / zeta ^ (3 / 2 : ℝ)) *
      min zeta (R / 2) ^ (3 / 2 : ℝ) =
      gap * (max 1 (upper / R) ^ (3 / 2 : ℝ) * min zeta (R / 2) ^ (3 / 2 : ℝ)) /
        zeta ^ (3 / 2 : ℝ) := by ring
  rw [he, le_div_iff₀ (Real.rpow_pos_of_pos hz _)]
  exact mul_le_mul_of_nonneg_left hb hgap

end Optimization
