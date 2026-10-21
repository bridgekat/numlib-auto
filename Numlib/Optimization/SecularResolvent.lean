import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor

/-!
# Norm-squared resolvents

The function is the squared norm of the actual inverse of a shifted self-adjoint operator.
The spectral sum is proved from Mathlib's orthonormal eigenbasis, rather than assumed as data.
Statements using the inverse require every shifted eigenvalue to be nonzero; positivity of
all shifted eigenvalues is the natural secular domain.
-/

open scoped BigOperators Topology
open Set Filter

namespace Optimization.SecularResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Squared norm of the shifted resolvent applied to a vector. Regularity theorems below
are restricted to nonsingular shifts. -/
noncomputable def normSqResolvent (H : E →ₗ[ℝ] E) (g : E) (t : ℝ) : ℝ :=
  ‖Ring.inverse (H + t • (1 : E →ₗ[ℝ] E)) g‖ ^ 2

/-- The scalar spectral expression associated with real eigenvalues and real coordinates. -/
noncomputable def spectralNormSq {ι : Type*} [Fintype ι] (e γ : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, γ i ^ 2 / (t + e i) ^ 2

section SpectralBridge

variable [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)

/-- All shifted eigenvalues are positive. This formulation also covers the zero-dimensional
space, without requiring a choice of a smallest eigenvalue. -/
def Admissible (t : ℝ) : Prop :=
  ∀ i, 0 < t + hH.eigenvalues (n := Module.finrank ℝ E) rfl i

/-- In spectral coordinates a shifted self-adjoint operator acts coordinatewise. -/
theorem repr_shift_apply (t : ℝ) (x : E) (i : Fin (Module.finrank ℝ E)) :
    (hH.eigenvectorBasis rfl).repr ((H + t • (1 : E →ₗ[ℝ] E)) x) i =
      (t + hH.eigenvalues rfl i) * (hH.eigenvectorBasis rfl).repr x i := by
  simp [hH.eigenvectorBasis_apply_self_apply, add_mul, add_comm]

/-- Avoiding every spectral pole makes the shifted operator invertible. -/
theorem isUnit_shift (t : ℝ)
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    IsUnit (H + t • (1 : E →ₗ[ℝ] E)) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply (hH.eigenvectorBasis rfl).repr.injective
  apply PiLp.ext
  intro i
  have hi := congrArg (fun y => (hH.eigenvectorBasis rfl).repr y i) hx
  rw [repr_shift_apply] at hi
  simpa using (mul_eq_zero.mp (by simpa using hi)).resolve_left (ht i)

/-- The genuine resolvent solves the shifted system. -/
theorem shift_inverse_apply (g : E) (t : ℝ)
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    (H + t • (1 : E →ₗ[ℝ] E))
      (Ring.inverse (H + t • (1 : E →ₗ[ℝ] E)) g) = g := by
  exact congrArg (fun A : E →ₗ[ℝ] E => A g)
    (Ring.mul_inverse_cancel _ (isUnit_shift hH t ht))

/-- Coordinates of the actual inverse in the orthonormal eigenbasis. -/
theorem repr_inverse_apply (g : E) (t : ℝ)
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0)
    (i : Fin (Module.finrank ℝ E)) :
    (hH.eigenvectorBasis rfl).repr (Ring.inverse (H + t • (1 : E →ₗ[ℝ] E)) g) i =
      (hH.eigenvectorBasis rfl).repr g i / (t + hH.eigenvalues rfl i) := by
  apply (eq_div_iff (ht i)).2
  have hi := congrArg (fun y => (hH.eigenvectorBasis rfl).repr y i)
    (shift_inverse_apply hH g t ht)
  rw [repr_shift_apply] at hi
  simpa [mul_comm] using hi

/-- Parseval's identity identifies the inverse norm with the spectral sum. -/
theorem normSqResolvent_eq_spectralNormSq (g : E) (t : ℝ)
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    normSqResolvent H g t =
      spectralNormSq (hH.eigenvalues rfl) (fun i => (hH.eigenvectorBasis rfl).repr g i) t := by
  unfold normSqResolvent spectralNormSq
  rw [← (hH.eigenvectorBasis rfl).repr.norm_map,
    EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [repr_inverse_apply hH g t ht, div_pow]

end SpectralBridge

section Scalar

variable {ι : Type*} [Fintype ι] (e γ : ι → ℝ)

/-- Regularity of the scalar spectral expression away from its poles. -/
theorem contDiffAt_spectralNormSq {t : ℝ} (ht : ∀ i, t + e i ≠ 0)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (spectralNormSq e γ) t := by
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow 2)
    (pow_ne_zero _ (ht i))

/-- Coefficient identity for differentiating an inverse square. -/
theorem inverseSquare_derivative_coefficient (j : ℕ) :
    (∏ i ∈ Finset.range j, (-2 - (i : ℝ))) =
      (-1 : ℝ) ^ j * (j + 1).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, ih, pow_succ, Nat.factorial_succ (j + 1)]
    push_cast
    ring

/-- All derivatives of the squared spectral resolvent, with no assumed derivative data. -/
theorem iteratedDeriv_spectralNormSq (j : ℕ) {t : ℝ}
    (ht : ∀ i, t + e i ≠ 0) :
    iteratedDeriv j (spectralNormSq e γ) t =
      (-1 : ℝ) ^ j * (j + 1).factorial *
        ∑ i, γ i ^ 2 / (t + e i) ^ (j + 2) := by
  unfold spectralNormSq
  rw [iteratedDeriv_fun_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hfun : (fun x : ℝ => γ i ^ 2 / (x + e i) ^ 2) =
        (fun x : ℝ => γ i ^ 2 * (x + e i) ^ (-2 : ℤ)) := by
      ext x
      simp [zpow_neg, div_eq_mul_inv]
    rw [hfun, iteratedDeriv_const_mul_field]
    have hshift := congrFun (iteratedDeriv_comp_add_const j
      (fun x : ℝ => x ^ (-2 : ℤ)) (e i)) t
    rw [hshift, iteratedDeriv_eq_iterate, iter_deriv_zpow]
    simp only [Int.cast_neg, Int.cast_ofNat]
    rw [inverseSquare_derivative_coefficient]
    have hz : (-2 : ℤ) - (j : ℤ) = -((j + 2 : ℕ) : ℤ) := by omega
    rw [hz, zpow_neg, zpow_natCast]
    ring
  · intro i _
    exact contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow 2)
      (pow_ne_zero _ (ht i))

/-- The scalar squared resolvent is nonnegative, even at a totalized pole. -/
theorem spectralNormSq_nonneg (t : ℝ) : 0 ≤ spectralNormSq e γ t := by
  exact Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- A nonzero spectral coordinate makes the squared resolvent positive off the poles. -/
theorem spectralNormSq_pos {t : ℝ} (ht : ∀ i, t + e i ≠ 0)
    (hγ : ∃ i, γ i ≠ 0) : 0 < spectralNormSq e γ t := by
  obtain ⟨i, hi⟩ := hγ
  apply Finset.sum_pos' (fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  exact ⟨i, Finset.mem_univ _, div_pos (sq_pos_of_ne_zero hi) (sq_pos_of_ne_zero (ht i))⟩

/-- Strict alternating derivative signs on the positive shifted spectrum. -/
theorem sign_iteratedDeriv_spectralNormSq (j : ℕ) {t : ℝ}
    (ht : ∀ i, 0 < t + e i) (hγ : ∃ i, γ i ≠ 0) :
    0 < (-1 : ℝ) ^ j * iteratedDeriv j (spectralNormSq e γ) t := by
  rw [iteratedDeriv_spectralNormSq e γ j (fun i => ne_of_gt (ht i))]
  have hs : 0 < ∑ i, γ i ^ 2 / (t + e i) ^ (j + 2) := by
    obtain ⟨i, hi⟩ := hγ
    apply Finset.sum_pos' (fun k _ => div_nonneg (sq_nonneg _) (le_of_lt (pow_pos (ht k) _)))
    exact ⟨i, Finset.mem_univ _, div_pos (sq_pos_of_ne_zero hi) (pow_pos (ht i) _)⟩
  have hsq : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by
    rw [← mul_pow]; simp
  calc
    0 < (j + 1).factorial * ∑ i, γ i ^ 2 / (t + e i) ^ (j + 2) := by positivity
    _ = _ := by rw [← mul_assoc, ← mul_assoc, hsq, one_mul]

/-- Strict decrease follows directly from the positive spectral denominators. -/
theorem strictAntiOn_spectralNormSq (a : ℝ) (ha : ∀ i, 0 ≤ a + e i)
    (hγ : ∃ i, γ i ≠ 0) : StrictAntiOn (spectralNormSq e γ) (Ioi a) := by
  intro x hx y hy hxy
  unfold spectralNormSq
  apply Finset.sum_lt_sum
  · intro i _
    have hxi : 0 < x + e i := by linarith [ha i, hx.out]
    have hyi : 0 < y + e i := by linarith [ha i, hy.out]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hxi)
      (sq_le_sq₀ hxi.le hyi.le |>.2 (by linarith))
  · obtain ⟨i, hi⟩ := hγ
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have hxi : 0 < x + e i := by linarith [ha i, hx.out]
    have hyi : 0 < y + e i := by linarith [ha i, hy.out]
    exact div_lt_div_of_pos_left (sq_pos_of_ne_zero hi) (sq_pos_of_pos hxi)
      (sq_lt_sq₀ hxi.le hyi.le |>.2 (by linarith))

/-- Every finite spectral squared resolvent tends to zero at infinity. -/
theorem tendsto_spectralNormSq_atTop :
    Tendsto (spectralNormSq e γ) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
      (tendsto_atTop_add_const_right atTop (e i) tendsto_id)).const_div_atTop
      (γ i ^ 2))
  unfold spectralNormSq
  simpa only [Finset.sum_const_zero, Function.comp_apply, id_eq] using h

end Scalar

section OperatorDerivatives

variable [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)

/-- The spectral equality holds throughout a neighborhood of every nonsingular shift. -/
theorem eventuallyEq_normSqResolvent (g : E) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    normSqResolvent H g =ᶠ[𝓝 t]
      spectralNormSq (hH.eigenvalues rfl) (fun i => (hH.eigenvectorBasis rfl).repr g i) := by
  have h : ∀ᶠ x in 𝓝 t, ∀ i, x + hH.eigenvalues rfl i ≠ 0 := by
    rw [eventually_all]
    intro i
    exact (continuousAt_id.add continuousAt_const).eventually_ne (ht i)
  filter_upwards [h] with x hx
  exact normSqResolvent_eq_spectralNormSq hH g x hx

/-- Exact all-order derivative formula for the norm of the actual operator resolvent. -/
theorem iteratedDeriv_normSqResolvent (g : E) (j : ℕ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    iteratedDeriv j (normSqResolvent H g) t =
      (-1 : ℝ) ^ j * (j + 1).factorial *
        ∑ i, ((hH.eigenvectorBasis rfl).repr g i) ^ 2 /
          (t + hH.eigenvalues rfl i) ^ (j + 2) := by
  rw [(eventuallyEq_normSqResolvent hH g ht).iteratedDeriv_eq j]
  exact iteratedDeriv_spectralNormSq _ _ j ht

/-- A nonzero vector has a nonzero coordinate in the eigenbasis. -/
theorem exists_repr_ne_zero {g : E} (hg : g ≠ 0) :
    ∃ i, (hH.eigenvectorBasis rfl).repr g i ≠ 0 := by
  by_contra h
  push Not at h
  apply hg
  apply (hH.eigenvectorBasis rfl).repr.injective
  apply PiLp.ext
  intro i
  simpa using h i

/-- Strict alternating derivative signs of a nonzero genuine resolvent on its positive domain. -/
theorem sign_iteratedDeriv_normSqResolvent {g : E} (hg : g ≠ 0) (j : ℕ)
    {t : ℝ} (ht : Admissible hH t) :
    0 < (-1 : ℝ) ^ j * iteratedDeriv j (normSqResolvent H g) t := by
  rw [(eventuallyEq_normSqResolvent hH g (fun i => ne_of_gt (ht i))).iteratedDeriv_eq j]
  exact sign_iteratedDeriv_spectralNormSq _ _ j ht (exists_repr_ne_zero hH hg)

/-- Strict decrease on any half-line to the right of all spectral poles. -/
theorem strictAntiOn_normSqResolvent {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) :
    StrictAntiOn (normSqResolvent H g) (Ioi a) := by
  intro x hx y hy hxy
  have hp (x : ℝ) (hx : x ∈ Ioi a) : ∀ i, x + hH.eigenvalues rfl i ≠ 0 := by
    intro i
    have := ha i
    exact ne_of_gt (by linarith [hx.out])
  rw [normSqResolvent_eq_spectralNormSq hH g x (hp x hx),
    normSqResolvent_eq_spectralNormSq hH g y (hp y hy)]
  exact strictAntiOn_spectralNormSq _ _ a ha (exists_repr_ne_zero hH hg) hx hy hxy

include hH in
/-- The norm of a genuine finite-dimensional resolvent decays at infinity. -/
theorem tendsto_normSqResolvent_atTop (g : E) :
    Tendsto (normSqResolvent H g) atTop (𝓝 0) := by
  apply (tendsto_spectralNormSq_atTop (hH.eigenvalues rfl)
    (fun i => (hH.eigenvectorBasis rfl).repr g i)).congr'
  have h : ∀ᶠ x : ℝ in atTop, ∀ i, x + hH.eigenvalues rfl i ≠ 0 := by
    rw [eventually_all]
    intro i
    filter_upwards [eventually_gt_atTop (-hH.eigenvalues rfl i)] with x hx
    exact ne_of_gt (by linarith)
  filter_upwards [h] with x hx
  exact (normSqResolvent_eq_spectralNormSq hH g x hx).symm

end OperatorDerivatives

/-- A strictly decreasing continuous function that tends to zero crosses a nondecreasing
continuous target exactly once if it starts above the target and the target is positive somewhere.
A right boundary inequality is used through a point just to the right of that boundary, so no
value of a singular inverse is used at the boundary. -/
theorem existsUnique_crossing {f τ : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f (Ioi a)) (hτ : ContinuousOn τ (Ioi a))
    (hanti : StrictAntiOn f (Ioi a)) (hmono : MonotoneOn τ (Ioi a))
    (hlim : Tendsto f atTop (𝓝 0))
    (habove : ∃ x ∈ Ioi a, τ x < f x) (hpos : ∃ z ∈ Ioi a, 0 < τ z) :
    ∃! x, x ∈ Ioi a ∧ f x = τ x := by
  obtain ⟨x, hx, hfx⟩ := habove
  obtain ⟨z, hz, hτz⟩ := hpos
  obtain ⟨y, hy, hyx, hyz⟩ :=
    ((hlim.eventually_lt_const hτz).and
      ((eventually_gt_atTop x).and (eventually_gt_atTop z))).exists
  have hya : y ∈ Ioi a := lt_trans hx hyx
  have hτzy : τ z ≤ τ y := hmono hz hya hyz.le
  have hcont : ContinuousOn (fun t => f t - τ t) (Icc x y) :=
    (hf.sub hτ).mono (fun t ht => lt_of_lt_of_le hx ht.1)
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc' hyx.le hcont
    (show (0 : ℝ) ∈ Icc (f y - τ y) (f x - τ x) by constructor <;> linarith)
  have hra : r ∈ Ioi a := lt_of_lt_of_le hx hr.1
  have hroot : f r = τ r := sub_eq_zero.mp heq
  refine ⟨r, ⟨hra, hroot⟩, ?_⟩
  intro s hs
  rcases lt_trichotomy s r with hsr | hsr | hrs
  · have := hanti hs.1 hra hsr
    have := hmono hs.1 hra hsr.le
    rw [hs.2, hroot] at *
    linarith
  · exact hsr
  · have := hanti hra hs.1 hrs
    have := hmono hra hs.1 hrs.le
    rw [hs.2, hroot] at *
    linarith

section Root

variable [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)

/-- The genuine norm-squared resolvent has a unique intersection with a monotone continuous
positive target, provided it lies above that target at some regular shift. -/
theorem existsUnique_secular_root {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) {τ : ℝ → ℝ}
    (hτ : ContinuousOn τ (Ioi a)) (hmono : MonotoneOn τ (Ioi a))
    (habove : ∃ x ∈ Ioi a, τ x < normSqResolvent H g x)
    (hpos : ∃ z ∈ Ioi a, 0 < τ z) :
    ∃! x, x ∈ Ioi a ∧ normSqResolvent H g x = τ x := by
  apply existsUnique_crossing _ hτ (strictAntiOn_normSqResolvent hH hg a ha) hmono
    (tendsto_normSqResolvent_atTop hH g) habove hpos
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hx' : ∀ i, x + hH.eigenvalues rfl i ≠ 0 := by
    intro i
    exact ne_of_gt (by linarith [ha i, hx.out])
  exact ((contDiffAt_spectralNormSq _ _ hx' 0).continuousAt).congr
    (eventuallyEq_normSqResolvent hH g hx').symm

end Root

section Taylor

variable [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)

/-- The genuine resolvent norm is smooth away from the spectral poles. -/
theorem contDiffAt_normSqResolvent (g : E) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (normSqResolvent H g) t :=
  (contDiffAt_spectralNormSq _ _ ht n).congr_of_eventuallyEq
    (eventuallyEq_normSqResolvent hH g ht)

/-- The standard Taylor polynomial computed from the full derivatives. -/
noncomputable def taylorApprox (H : E →ₗ[ℝ] E) (g : E) (k : ℕ) (c x : ℝ) : ℝ :=
  taylorWithinEval (normSqResolvent H g) k univ c x

omit [FiniteDimensional ℝ E] in
/-- Expansion of the Taylor approximant in actual iterated derivatives. -/
theorem taylorApprox_eq_sum (H : E →ₗ[ℝ] E) (g : E) (k : ℕ) (c x : ℝ) :
    taylorApprox H g k c x = ∑ j ∈ Finset.range (k + 1),
      iteratedDeriv j (normSqResolvent H g) c * (x - c) ^ j / j.factorial := by
  simp only [taylorApprox, taylor_within_apply, iteratedDerivWithin_univ, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positivity of every shifted eigenvalue is preserved along a segment. -/
theorem admissible_uIcc {c x : ℝ} (hc : Admissible hH c) (hx : Admissible hH x)
    {y : ℝ} (hy : y ∈ uIcc c x) : Admissible hH y := by
  intro i
  rcases le_total c x with hcx | hxc
  · rw [uIcc_of_le hcx] at hy
    linarith [hc i, hy.1]
  · rw [uIcc_of_ge hxc] at hy
    linarith [hx i, hy.1]

/-- Lagrange remainder on the positive shifted spectrum, expressed using full derivatives. -/
theorem normSqResolvent_taylor_remainder (g : E) (k : ℕ) {c x : ℝ}
    (hcx : c ≠ x) (hc : Admissible hH c) (hx : Admissible hH x) :
    ∃ y ∈ uIoo c x,
      normSqResolvent H g x - taylorApprox H g k c x =
        iteratedDeriv (k + 1) (normSqResolvent H g) y * (x - c) ^ (k + 1) /
          (k + 1).factorial := by
  have hdiff (n : WithTop ℕ∞) : ContDiffOn ℝ n (normSqResolvent H g) (uIcc c x) := by
    intro y hy
    exact (contDiffAt_normSqResolvent hH g
      (fun i => ne_of_gt (admissible_uIcc hH hc hx hy i)) n).contDiffWithinAt
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hcx (hdiff (k + 1))
  refine ⟨y, hy, ?_⟩
  have hTaylor : taylorWithinEval (normSqResolvent H g) k (uIcc c x) c x =
      taylorApprox H g k c x := by
    simp only [taylorApprox, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDerivWithin_univ,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hcx)
        (contDiffAt_normSqResolvent hH g (fun i => ne_of_gt (hc i)) j) (left_mem_uIcc)]
  simpa only [hTaylor] using heq

/-- To the right of a regular center the Taylor remainder has alternating strict signs.
Thus even Taylor polynomials overestimate and odd Taylor polynomials underestimate. -/
theorem normSqResolvent_taylor_right {g : E} (hg : g ≠ 0) (k : ℕ) {c x : ℝ}
    (hcx : c < x) (hc : Admissible hH c) (hx : Admissible hH x) :
    0 < (-1 : ℝ) ^ (k + 1) *
      (normSqResolvent H g x - taylorApprox H g k c x) := by
  obtain ⟨y, hy, heq⟩ := normSqResolvent_taylor_remainder hH g k hcx.ne hc hx
  rw [heq]
  have hsign := sign_iteratedDeriv_normSqResolvent hH hg (k + 1)
    (admissible_uIcc hH hc hx (show y ∈ uIcc c x from ⟨hy.1.le, hy.2.le⟩))
  have hpow : 0 < (x - c) ^ (k + 1) := pow_pos (sub_pos.mpr hcx) _
  have hfact : (0 : ℝ) < (k + 1).factorial := by positivity
  convert div_pos (mul_pos hsign hpow) hfact using 1
  ring

/-- To the left of a regular center every Taylor polynomial underestimates. -/
theorem normSqResolvent_taylor_left {g : E} (hg : g ≠ 0) (k : ℕ) {c x : ℝ}
    (hxc : x < c) (hc : Admissible hH c) (hx : Admissible hH x) :
    taylorApprox H g k c x < normSqResolvent H g x := by
  obtain ⟨y, hy, heq⟩ := normSqResolvent_taylor_remainder hH g k hxc.ne' hc hx
  have hsign := sign_iteratedDeriv_normSqResolvent hH hg (k + 1)
    (admissible_uIcc hH hc hx (show y ∈ uIcc c x from ⟨hy.1.le, hy.2.le⟩))
  have hpow : 0 < (c - x) ^ (k + 1) := pow_pos (sub_pos.mpr hxc) _
  have hfact : (0 : ℝ) < (k + 1).factorial := by positivity
  have hpos := div_pos (mul_pos hsign hpow) hfact
  have hprod : (-1 : ℝ) ^ (k + 1) * (c - x) ^ (k + 1) = (x - c) ^ (k + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  have heq' : (-1 : ℝ) ^ (k + 1) *
      iteratedDeriv (k + 1) (normSqResolvent H g) y * (c - x) ^ (k + 1) /
        (k + 1).factorial = normSqResolvent H g x - taylorApprox H g k c x := by
    rw [heq, mul_right_comm _ _ ((c-x)^(k+1)), hprod]
    ring
  rw [heq'] at hpos
  linarith

/-- Left Taylor approximants strictly increase with the degree. -/
theorem taylorApprox_lt_succ_of_lt {g : E} (hg : g ≠ 0) (k : ℕ) {c x : ℝ}
    (hxc : x < c) (hc : Admissible hH c) :
    taylorApprox H g k c x < taylorApprox H g (k + 1) c x := by
  unfold taylorApprox
  rw [taylorWithinEval_succ, iteratedDerivWithin_univ]
  have hsign := sign_iteratedDeriv_normSqResolvent hH hg (k + 1) hc
  have hpow : 0 < (c - x) ^ (k + 1) := pow_pos (sub_pos.mpr hxc) _
  have hprod : (-1 : ℝ) ^ (k + 1) * (c - x) ^ (k + 1) = (x - c) ^ (k + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  have hpos := mul_pos hsign hpow
  have hpos' : 0 < (x-c) ^ (k+1) * iteratedDeriv (k+1) (normSqResolvent H g) c := by
    convert hpos using 1
    rw [mul_right_comm _ _ ((c-x)^(k+1)), hprod, mul_comm]
  have hcoef : (0 : ℝ) < ((k : ℝ) + 1) * k.factorial := by positivity
  simp only [smul_eq_mul]
  have := mul_pos (inv_pos.mpr hcoef) hpos'
  nlinarith

/-- The alternating right bounds and increasing left lower bounds for all Taylor degrees. -/
theorem normSqResolvent_taylor_bounds {g : E} (hg : g ≠ 0) {c x : ℝ}
    (hc : Admissible hH c) (hx : Admissible hH x) :
    (c < x → ∀ k, 0 < (-1 : ℝ) ^ (k + 1) *
      (normSqResolvent H g x - taylorApprox H g k c x)) ∧
    (x < c → ∀ k, taylorApprox H g k c x < taylorApprox H g (k + 1) c x ∧
      taylorApprox H g (k + 1) c x < normSqResolvent H g x) := by
  constructor
  · intro hcx k
    exact normSqResolvent_taylor_right hH hg k hcx hc hx
  · intro hxc k
    exact ⟨taylorApprox_lt_succ_of_lt hH hg k hxc hc,
      normSqResolvent_taylor_left hH hg (k + 1) hxc hc hx⟩

omit [FiniteDimensional ℝ E] in
@[simp] theorem normSqResolvent_zero (H : E →ₗ[ℝ] E) (t : ℝ) :
    normSqResolvent H 0 t = 0 := by simp [normSqResolvent]

omit [FiniteDimensional ℝ E] in
@[simp] theorem taylorApprox_zero (H : E →ₗ[ℝ] E) (k : ℕ) (c x : ℝ) :
    taylorApprox H 0 k c x = 0 := by
  unfold taylorApprox
  have hz : normSqResolvent H (0 : E) = (fun _ => (0 : ℝ)) :=
    funext (normSqResolvent_zero H)
  rw [hz, taylor_within_apply]
  simp

/-- Nonstrict Taylor bounds, including the identically zero right-hand side. -/
theorem normSqResolvent_taylor_bounds_nonneg (g : E) {c x : ℝ}
    (hc : Admissible hH c) (hx : Admissible hH x) :
    (c < x → ∀ k, 0 ≤ (-1 : ℝ) ^ (k + 1) *
      (normSqResolvent H g x - taylorApprox H g k c x)) ∧
    (x < c → ∀ k, taylorApprox H g k c x ≤ taylorApprox H g (k + 1) c x ∧
      taylorApprox H g (k + 1) c x ≤ normSqResolvent H g x) := by
  by_cases hg : g = 0
  · subst g
    simp
  · have h := normSqResolvent_taylor_bounds hH hg hc hx
    exact ⟨fun hcx k => (h.1 hcx k).le,
      fun hxc k => ⟨(h.2 hxc k).1.le, (h.2 hxc k).2.le⟩⟩

end Taylor

section BoundaryRoot

variable [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)

/-- A formulation of the root theorem directly with a strict right-boundary comparison.
The comparison may be obtained from finite right limits or an infinite resolvent pole. -/
theorem existsUnique_secular_root_of_boundary {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) {τ : ℝ → ℝ}
    (hτ : ContinuousOn τ (Ioi a)) (hmono : MonotoneOn τ (Ioi a))
    (hboundary : ∀ᶠ x in 𝓝[>] a, τ x < normSqResolvent H g x)
    (hpos : ∃ z ∈ Ioi a, 0 < τ z) :
    ∃! x, x ∈ Ioi a ∧ normSqResolvent H g x = τ x := by
  apply existsUnique_secular_root hH hg a ha hτ hmono _ hpos
  obtain ⟨x, hx, hx'⟩ := (hboundary.and self_mem_nhdsWithin).exists
  exact ⟨x, hx', hx⟩

/-- Positivity of the genuine norm-squared resolvent for a nonzero right-hand side. -/
theorem normSqResolvent_pos {g : E} (hg : g ≠ 0) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    0 < normSqResolvent H g t := by
  rw [normSqResolvent_eq_spectralNormSq hH g t ht]
  exact spectralNormSq_pos _ _ ht (exists_repr_ne_zero hH hg)

/-- A positive power of the resolvent norm is strictly decreasing on its positive domain. -/
theorem strictAntiOn_rpow_normSqResolvent {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) {β : ℝ} (hβ : 0 < β) :
    StrictAntiOn (fun t => normSqResolvent H g t ^ β) (Ioi a) := by
  intro x hx y hy hxy
  apply Real.rpow_lt_rpow
  · exact (normSqResolvent_pos hH hg (fun i => ne_of_gt (by linarith [ha i, hy.out]))).le
  · exact strictAntiOn_normSqResolvent hH hg a ha hx hy hxy
  · exact hβ

/-- A negative power of the resolvent norm is strictly increasing on its positive domain. -/
theorem strictMonoOn_rpow_normSqResolvent {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) {β : ℝ} (hβ : β < 0) :
    StrictMonoOn (fun t => normSqResolvent H g t ^ β) (Ioi a) := by
  intro x hx y hy hxy
  apply Real.rpow_lt_rpow_of_neg
  · exact normSqResolvent_pos hH hg (fun i => ne_of_gt (by linarith [ha i, hy.out]))
  · exact strictAntiOn_normSqResolvent hH hg a ha hx hy hxy
  · exact hβ

include hH in
/-- Positive powers of the resolvent norm tend to zero at infinity. -/
theorem tendsto_rpow_normSqResolvent_atTop (g : E) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun t => normSqResolvent H g t ^ β) atTop (𝓝 0) := by
  have := (tendsto_normSqResolvent_atTop hH g).rpow tendsto_const_nhds (Or.inr hβ)
  simpa [Real.zero_rpow hβ.ne'] using this

/-- Negative powers of a nonzero resolvent norm diverge to infinity. -/
theorem tendsto_rpow_neg_normSqResolvent_atTop {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) {β : ℝ} (hβ : β < 0) :
    Tendsto (fun t => normSqResolvent H g t ^ β) atTop atTop := by
  apply (tendsto_rpow_neg_nhdsGT_zero hβ).comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_normSqResolvent_atTop hH g, ?_⟩
  filter_upwards [eventually_gt_atTop a] with t ht
  exact normSqResolvent_pos hH hg (fun i => ne_of_gt (by linarith [ha i]))

end BoundaryRoot

end Optimization.SecularResolvent
