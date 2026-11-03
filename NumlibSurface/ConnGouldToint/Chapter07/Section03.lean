import Numlib.Nonlinear.ScalarNewton
import Numlib.Optimization.Subproblem.Bracketing
import Numlib.Optimization.Subproblem.SecularIteration
import Numlib.Optimization.Subproblem.Multiplier

/-!
# The Moré–Sorensen secular equation

Section 7.3 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter07

open Subproblem Set Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {g : E} {H : E →L[ℝ] E}
  {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-- The shifted step `s(λ)` from (7.3.1). -/
noncomputable abbrev shiftedStep (g : E) (H : E →L[ℝ] E) : ℝ → E := step g H

/-- The Moré–Sorensen secular function (7.3.6), expressed using the squared step norm. -/
noncomputable abbrev phi (g : E) (H : E →L[ℝ] E) (Δ : ℝ) : ℝ → ℝ :=
  trSecular g H Δ (-1 / 2)

private theorem sq_rpow_neg_half (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (x ^ 2) ^ (-(k : ℝ) / 2) = (x ^ k)⁻¹ := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx,
    show (2 : ℝ) * (-(k : ℝ) / 2) = -(k : ℝ) by ring, Real.rpow_neg hx, Real.rpow_natCast]

omit [FiniteDimensional ℝ E] in
/-- The secular function is the reciprocal step norm minus the reciprocal radius. -/
theorem phi_eq_inv_norm_sub_inv (g : E) (H : E →L[ℝ] E) (Δ lam : ℝ) :
    phi g H Δ lam = 1 / ‖shiftedStep g H lam‖ - 1 / Δ := by
  have h : secular g H lam ^ (-1 / 2 : ℝ) = ‖step g H lam‖⁻¹ := by
    simpa [secular] using sq_rpow_neg_half ‖step g H lam‖ (norm_nonneg _) 1
  rw [phi, trSecular, h, show (2 : ℝ) * (-1 / 2) = -1 by norm_num, Real.rpow_neg_one]
  simp only [shiftedStep, one_div]

/-- Lemma 7.3.1. The Moré–Sorensen secular function is strictly increasing and concave
above the leftmost pole, and has the derivatives (7.3.7)–(7.3.9). -/
theorem lemma_7_3_1 (hg : g ≠ 0) (Δ : ℝ) :
    StrictMonoOn (phi g H Δ) (Ioi (-leftmost hH)) ∧
    ConcaveOn ℝ (Ioi (-leftmost hH)) (phi g H Δ) ∧
    ∀ lam : ℝ, -leftmost hH < lam →
      let s := shiftedStep g H lam
      let d := -(Ring.inverse (H + lam • 1)) s
      HasDerivAt (shiftedStep g H) d lam ∧
        deriv (phi g H Δ) lam = -⟪s, d⟫ / ‖s‖ ^ 3 ∧
        iteratedDeriv 2 (phi g H Δ) lam =
          3 * (⟪s, d⟫ ^ 2 - ‖s‖ ^ 2 * ‖d‖ ^ 2) / ‖s‖ ^ 5 := by
  obtain ⟨hcv, hm, -⟩ := trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)
  refine ⟨hm, hcv, fun lam hlam => ?_⟩
  let s := step g H lam
  let d := stepDeriv g H 1 lam
  have hstep (x : ℝ) : stepDeriv g H 0 x = step g H x := stepDeriv_zero x
  have hD : HasDerivAt (shiftedStep g H) d lam := by
    rw [← show stepDeriv g H 0 = shiftedStep g H from funext hstep]
    exact hasDerivAt_stepDeriv (g := g) hlam 0
  have hd : -(Ring.inverse (H + lam • 1)) s = d := by
    simp [d, s, stepDeriv, step, pow_two]
  change HasDerivAt (shiftedStep g H) (-(Ring.inverse (H + lam • 1)) s) lam ∧ _
  rw [hd]
  refine ⟨hD, ?_⟩
  change deriv (phi g H Δ) lam = -⟪s, d⟫ / ‖s‖ ^ 3 ∧
    iteratedDeriv 2 (phi g H Δ) lam =
      3 * (⟪s, d⟫ ^ 2 - ‖s‖ ^ 2 * ‖d‖ ^ 2) / ‖s‖ ^ 5
  have hπ1 : deriv (secular g H) lam = 2 * ⟪s, d⟫ := by
    simpa [s, d, iteratedDeriv_one, secularCoeff_zero, hstep] using
      (iteratedDeriv_secular (g := g) hlam 0).1
  have hπ2 : iteratedDeriv 2 (secular g H) lam = 6 * ‖d‖ ^ 2 := by
    have hc : secularCoeff 1 = 6 := by norm_num [secularCoeff, Nat.factorial_succ]
    simpa [hc, d] using (iteratedDeriv_secular (g := g) hlam 0).2
  have hpow3 : secular g H lam ^ ((-1 / 2 : ℝ) - 1) = (‖s‖ ^ 3)⁻¹ := by
    simpa [s, secular, show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] using
      sq_rpow_neg_half ‖s‖ (norm_nonneg _) 3
  have hpow5 : secular g H lam ^ ((-1 / 2 : ℝ) - 2) = (‖s‖ ^ 5)⁻¹ := by
    simpa [s, secular, show (-1 / 2 : ℝ) - 2 = -5 / 2 by norm_num] using
      sq_rpow_neg_half ‖s‖ (norm_nonneg _) 5
  constructor
  · rw [(hasDerivAt_trSecular hg hlam Δ (-1 / 2)).deriv, hπ1, hpow3]
    ring
  · have heq : iteratedDeriv 2 (phi g H Δ) lam =
        iteratedDeriv 2 (fun t => secular g H t ^ (-1 / 2 : ℝ)) lam := by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]
      congr 1
      funext x
      exact deriv_sub_const _
    rw [heq, iteratedDeriv_two_secular_rpow hg hlam, hπ1, hπ2, hpow3, hpow5]
    have hs : ‖s‖ ≠ 0 := by
      intro hz
      have hp := secular_pos (hH := hH) hg hlam
      change 0 < ‖s‖ ^ 2 at hp
      simp [hz] at hp
    field_simp
    ring

/-- The scalar Newton step for the Moré–Sorensen equation (7.3.11). -/
noncomputable abbrev moreSorensenNewtonStep (g : E) (H : E →L[ℝ] E) (Δ : ℝ) : ℝ → ℝ :=
  Newton.scalarStep (phi g H Δ) (deriv (phi g H Δ))

/-- Algorithm 7.3.1. A nonsingular Cholesky factor and one triangular solve give
the Newton step without computing the full derivative of the shifted step. -/
theorem algorithm_7_3_1_step (hg : g ≠ 0) {Δ lam : ℝ} (hΔ : 0 < Δ)
    (hlam : -leftmost hH < lam) (L : E →L[ℝ] E) (hL : Function.Injective L)
    (hfac : L.comp L.adjoint = H + lam • 1) {w : E}
    (hw : L w = shiftedStep g H lam) :
    moreSorensenNewtonStep g H Δ lam =
      lam + ((‖shiftedStep g H lam‖ - Δ) / Δ) * (‖shiftedStep g H lam‖ ^ 2 / ‖w‖ ^ 2) := by
  let s := shiftedStep g H lam
  let z := (Ring.inverse (H + lam • 1)) s
  have hsol : L (L.adjoint z) = s := by
    rw [← ContinuousLinearMap.comp_apply, hfac]
    exact add_smul_inverse_apply hlam s
  have hz : L.adjoint z = w := hL (hsol.trans hw.symm)
  have hinner : ⟪s, z⟫ = ‖w‖ ^ 2 := by
    rw [← show L w = s from hw, ← ContinuousLinearMap.adjoint_inner_right, hz,
      real_inner_self_eq_norm_sq]
  have hder := ((lemma_7_3_1 (hH := hH) hg Δ).2.2 lam hlam).2.1
  change deriv (phi g H Δ) lam = -⟪s, -z⟫ / ‖s‖ ^ 3 at hder
  rw [inner_neg_right, neg_neg, hinner] at hder
  have hs₀ : s ≠ 0 := by
    intro hs
    have hp := secular_pos (hH := hH) hg hlam
    change 0 < ‖s‖ ^ 2 at hp
    simp [hs] at hp
  have hw₀ : w ≠ 0 := fun h => hs₀ (by simpa [h] using hw.symm)
  rw [moreSorensenNewtonStep, Newton.scalarStep, phi_eq_inv_norm_sub_inv, hder]
  change lam - (1 / ‖s‖ - 1 / Δ) / (‖w‖ ^ 2 / ‖s‖ ^ 3) =
    lam + ((‖s‖ - Δ) / Δ) * (‖s‖ ^ 2 / ‖w‖ ^ 2)
  field_simp [norm_ne_zero_iff.mpr hs₀, norm_ne_zero_iff.mpr hw₀, hΔ.ne']
  ring

omit [FiniteDimensional ℝ E] in
private theorem phi_root {Δ r : ℝ} (hΔ : 0 < Δ) (hroot : secular g H r = Δ ^ 2) :
    phi g H Δ r = 0 := by
  rw [phi, trSecular, hroot, ← Real.rpow_two, ← Real.rpow_mul hΔ.le, sub_self]

private theorem moreSorensenNewtonStep_eq (hg : g ≠ 0) {Δ x : ℝ} (hΔ : 0 < Δ)
    (hx : -leftmost hH < x) :
    moreSorensenNewtonStep g H Δ x = x + trNewtonCorrection g H Δ x := by
  rw [moreSorensenNewtonStep, Newton.scalarStep, trNewtonCorrection_eq hg hx hΔ, sub_eq_add_neg,
    neg_div]

/-- A negative secular value in the open shift interval ensures a unique root
in that interval. -/
theorem existsUnique_secular_root_of_phi_neg (hg : g ≠ 0) {Δ x : ℝ} (hΔ : 0 < Δ)
    (hx : -leftmost hH < x) (hbelow : phi g H Δ x < 0) :
    ∃! r, -leftmost hH < r ∧ secular g H r = Δ ^ 2 := by
  have hspos : 0 < ‖step g H x‖ := by
    have hp := secular_pos (hH := hH) hg hx
    rw [secular] at hp
    exact norm_pos_iff.2 fun h => by simp [h] at hp
  have hs : Δ < ‖step g H x‖ := by
    by_contra! hn
    rw [phi_eq_inv_norm_sub_inv] at hbelow
    have h := one_div_le_one_div_of_le hspos hn
    linarith only [hbelow, h]
  have hπx : Δ ^ 2 < secular g H x :=
    (pow_lt_pow_iff_left₀ hΔ.le hspos.le two_ne_zero).mpr hs
  obtain ⟨-, hπc, hπa, -, hπ0, -⟩ := secular_shape (hH := hH) hg 1
  obtain ⟨b, hxb, hb⟩ := ((eventually_ge_atTop x).and
    (hπ0.eventually (gt_mem_nhds (pow_pos hΔ 2)))).exists
  obtain ⟨r, hmem, hr⟩ := intermediate_value_Icc' hxb
    (hπc.mono fun _ hy => hx.trans_le hy.1) ⟨hb.le, hπx.le⟩
  have hrd := hx.trans_le hmem.1
  exact ⟨r, ⟨hrd, hr⟩, fun y hy => hπa.injOn hy.1 hrd (hy.2.trans hr.symm)⟩

/-- If the gradient is an eigenvector, the secular function is affine in its domain,
and one Newton step reaches the root exactly. -/
theorem moreSorensenNewtonStep_eq_root_of_eigenvector (hg : g ≠ 0)
    (heig : ∃ c : ℝ, H g = c • g) {Δ r x : ℝ} (hΔ : 0 < Δ)
    (hr : -leftmost hH < r) (hroot : secular g H r = Δ ^ 2)
    (hx : -leftmost hH < x) :
    moreSorensenNewtonStep g H Δ x = r := by
  have hxr : x + (r - x) = r := by ring
  have ht := (secular_rpow_tangent (hH := hH) hg hx (δ := r - x) (by rwa [hxr])
    (-1 / 2)).2.2.2.2 rfl heig
  rw [hxr] at ht
  have hderiv : deriv (phi g H Δ) x = deriv (fun t => secular g H t ^ (-1 / 2 : ℝ)) x :=
    deriv_sub_const _
  have hlin : phi g H Δ r = phi g H Δ x + deriv (phi g H Δ) x * (r - x) := by
    rw [hderiv]
    unfold phi trSecular
    linarith only [ht]
  rw [phi_root hΔ hroot] at hlin
  have hd := (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.2 x hx
  change x - phi g H Δ x / deriv (phi g H Δ) x = r
  field_simp [ne_of_gt hd]
  linarith only [hlin]

/-- Lemma 7.3.2. Newton iterates from below an interior root stay in the shift domain,
increase to the root, and satisfy the global linear and eventual quadratic error bounds.
An affine secular function can reach the root exactly, so the secular value is allowed
to be zero at subsequent iterates. -/
theorem lemma_7_3_2 (hg : g ≠ 0) {Δ r x₀ : ℝ} (hΔ : 0 < Δ)
    (hr : -leftmost hH < r) (hroot : secular g H r = Δ ^ 2)
    (hx₀ : -leftmost hH < x₀) (hbelow : phi g H Δ x₀ < 0) :
    let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
    let γ := 1 - deriv (phi g H Δ) r / deriv (phi g H Δ) x₀
    (∀ k, -leftmost hH < x k ∧ phi g H Δ (x k) ≤ 0) ∧
      Monotone x ∧ γ ∈ Ico 0 1 ∧ (∀ k, r - x (k + 1) ≤ γ * (r - x k)) ∧
      ConvergesWithOrder x r 2 := by
  let N := moreSorensenNewtonStep g H Δ
  let x := fun k : ℕ => N^[k] x₀
  obtain ⟨-, hm, hd⟩ := trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)
  have hr₀ := phi_root hΔ hroot
  have hxr : x₀ ≤ r := by
    by_contra! hn
    exact hbelow.not_gt (hr₀ ▸ hm hr hx₀ hn)
  have hupdate (k : ℕ) : x (k + 1) = moreSorensenNewtonStep g H Δ (x k) :=
    Function.iterate_succ_apply' N k x₀
  have hmem (k : ℕ) : x k ∈ Ioc (-leftmost hH) r := by
    induction k with
    | zero => exact ⟨hx₀, hxr⟩
    | succ k ih =>
      have hstep := trNewtonCorrection_mem hΔ hr hroot ih.1
      rw [hupdate, moreSorensenNewtonStep_eq hg hΔ ih.1]
      exact ⟨ih.1.trans_le (hstep.2 ih.2), hstep.1⟩
  have hstep (k : ℕ) :
      x k + trNewtonCorrection g H Δ (x k) ≤ x (k + 1) ∧ x (k + 1) ≤ r :=
    ⟨by rw [hupdate, moreSorensenNewtonStep_eq hg hΔ (hmem k).1], (hmem _).2⟩
  obtain ⟨hmono, htend, hγ, hlinear, -⟩ :=
    tendsto_of_trNewtonCorrection_le hΔ hr hroot (hmem 0) hstep
  refine ⟨fun k => ⟨(hmem k).1, hr₀ ▸ hm.monotoneOn (hmem k).1 hr (hmem k).2⟩,
    hmono, hγ, hlinear, htend, ?_⟩
  have hsmooth : ContDiffOn ℝ 2 (phi g H Δ) (Ioi (-leftmost hH)) :=
    (contDiffOn_secular_rpow (hH := hH) hg _).sub contDiffOn_const
  obtain ⟨ε, hε, hlocal⟩ := Newton.hasIterationOrder_scalarStep_two hr₀
    (hsmooth.contDiffAt (isOpen_Ioi.mem_nhds hr)) (hd r hr).ne'
  obtain ⟨j, hj⟩ := eventually_atTop.mp (htend.eventually (Metric.ball_mem_nhds r hε))
  obtain ⟨-, C, hC, hbound⟩ := hlocal (x j) (hj j le_rfl)
  obtain ⟨l, hl⟩ := eventually_atTop.mp hbound
  refine ⟨C, hC, eventually_atTop.mpr ⟨l + j, fun k hk => ?_⟩⟩
  have he := hl (k - j) (by omega)
  change ‖N^[k - j + 1] (N^[j] x₀) - r‖ ≤ C * ‖N^[k - j] (N^[j] x₀) - r‖ ^ (2 : ℝ) at he
  rwa [← Function.iterate_add_apply, ← Function.iterate_add_apply,
    show k - j + 1 + j = k + 1 by omega, show k - j + j = k by omega] at he

/-- Lemma 7.3.3. A Newton step from positive secular value does not exceed the
optimal multiplier. The next iterate either leaves the shift domain or has
nonpositive secular value. The multiplier may be at the pole or at an interior
solution of the trust-region subproblem. -/
theorem lemma_7_3_3 (hg : g ≠ 0) {Δ r x : ℝ} (hΔ : 0 < Δ)
    {sM : E} (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (hx : -leftmost hH < x) (hpos : 0 < phi g H Δ x) :
    let x' := moreSorensenNewtonStep g H Δ x
    x' < x ∧ x' ≤ r ∧ ((-leftmost hH < x' ∧ phi g H Δ x' ≤ 0) ∨ x' ≤ -leftmost hH) := by
  let y := moreSorensenNewtonStep g H Δ x
  have hr : -leftmost hH ≤ r := neg_leftmost_le_shiftThreshold.trans
    (shiftThreshold_le_of_isPositive (hH := hH) hmul.nonneg hmul.isPositive)
  have hd := (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.2 x hx
  have hyx : y < x := sub_lt_self _ (div_pos hpos hd)
  refine ⟨hyx, ?_⟩
  rcases lt_or_ge (-leftmost hH) y with hy | hy
  · have hxy : x + (y - x) = y := by ring
    have htan := (secular_rpow_tangent (hH := hH) hg hx (δ := y - x) (by rwa [hxy])
      (-1 / 2)).2.2.1 (by norm_num)
    rw [hxy] at htan
    have hderiv : deriv (phi g H Δ) x = deriv (fun t => secular g H t ^ (-1 / 2 : ℝ)) x :=
      deriv_sub_const _
    have hphi : phi g H Δ y ≤ 0 := by
      have ht : phi g H Δ y ≤ phi g H Δ x + deriv (phi g H Δ) x * (y - x) := by
        rw [hderiv]
        unfold phi trSecular
        linarith only [htan]
      have hz : phi g H Δ x + deriv (phi g H Δ) x * (y - x) = 0 := by
        dsimp [y, moreSorensenNewtonStep, Newton.scalarStep]
        field_simp [ne_of_gt hd]
        ring
      exact ht.trans_eq hz
    refine ⟨?_, Or.inl ⟨hy, hphi⟩⟩
    by_contra! hy'
    have hsq := (secular_lt_norm_sq_of_shifted (hH := hH) hg hr hmul.shifted hy').trans_le
      (pow_le_pow_left₀ (norm_nonneg _) hsM 2)
    have hnorm : ‖step g H y‖ < Δ := by
      rw [secular] at hsq
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hΔ.le two_ne_zero).mp hsq
    have hnpos : 0 < ‖step g H y‖ := by
      have hp := secular_pos (hH := hH) hg hy
      rw [secular] at hp
      exact norm_pos_iff.2 fun h => by simp [h] at hp
    have hgt : 0 < phi g H Δ y := by
      rw [phi_eq_inv_norm_sub_inv]
      exact sub_pos.mpr (one_div_lt_one_div_of_lt hnpos hnorm)
    exact hphi.not_gt hgt
  · exact ⟨hy.trans hr, Or.inr hy⟩

omit [FiniteDimensional ℝ E] in
private theorem quadModel_eq_of_shifted_comparison (hH' : (H : E →ₗ[ℝ] E).IsSymmetric)
    {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (u : E) :
    quadModel g H u =
      (1 / 2) * (⟪u - s, (H + μ • (1 : E →L[ℝ] E)) (u - s)⟫ -
        ⟪s, (H + μ • (1 : E →L[ℝ] E)) s⟫ - μ * ‖u‖ ^ 2) := by
  have hd := quadModel_sub_eq_of_shifted hH' hs u
  rw [quadModel_eq_of_shifted hs, inner_eq_of_shifted hs] at hd
  linarith

private theorem quadModel_lower_bound_of_shifted {μ Δ : ℝ} {s u : E}
    (hμ : 0 ≤ μ) (hlam : -leftmost hH < μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hu : ‖u‖ ≤ Δ) :
    -(1 / 2) * (⟪s, (H + μ • (1 : E →L[ℝ] E)) s⟫ + μ * Δ ^ 2) ≤ quadModel g H u := by
  have hp := isPositive_add_smul_of_le (hH := hH) hlam.le
  have hquad := ContinuousLinearMap.inner_apply_nonneg_of_isPositive hp (u - s)
  have hnorm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) hu 2) hμ
  rw [quadModel_eq_of_shifted_comparison hH hs]
  nlinarith only [hquad, hnorm]

/-- An acceptable approximation to the model minimizer, as defined in (7.3.19). -/
def IsAcceptableModelStep (g : E) (H : E →L[ℝ] E) (Δ κopt κtr : ℝ) (s sM : E) : Prop :=
  quadModel g H s ≤ κopt * quadModel g H sM ∧ ‖s‖ ≤ κtr * Δ

omit [FiniteDimensional ℝ E] in
/-- For a nonpositive reference value, decreasing the objective coefficient weakens the
acceptance test. The coefficient comparisons in the prose following Lemmas 7.3.5 and 7.3.6
therefore need to be reversed. -/
theorem IsAcceptableModelStep.weaken {Δ κopt κtr κopt' κtr' : ℝ} {s sM : E}
    (h : IsAcceptableModelStep g H Δ κopt κtr s sM) (hΔ : 0 ≤ Δ)
    (hval : quadModel g H sM ≤ 0) (hopt : κopt' ≤ κopt) (htr : κtr ≤ κtr') :
    IsAcceptableModelStep g H Δ κopt' κtr' s sM :=
  ⟨h.1.trans (mul_le_mul_of_nonpos_right hopt hval),
    h.2.trans (mul_le_mul_of_nonneg_right htr hΔ)⟩

/-- Lemma 7.3.5. When the shifted step has norm close to the radius, its model value
is at most `(1 - κ)²` times the model value at any feasible comparison point. -/
theorem lemma_7_3_5 {μ Δ κ : ℝ} (hμ : 0 ≤ μ) (hlam : -leftmost hH < μ)
    (hΔ : 0 < Δ) (hκ : κ ∈ Ioo 0 1) {u : E} (hu : ‖u‖ ≤ Δ)
    (hnear : |‖shiftedStep g H μ‖ - Δ| ≤ κ * Δ) :
    quadModel g H (shiftedStep g H μ) ≤ (1 - κ) ^ 2 * quadModel g H u := by
  let s := shiftedStep g H μ
  let A := H + μ • (1 : E →L[ℝ] E)
  have hs : A s = -g := (step_spec (g := g) hlam).1
  have hlower := quadModel_lower_bound_of_shifted (hH := hH) hμ hlam hs hu
  have hpos := ContinuousLinearMap.inner_apply_nonneg_of_isPositive
    (isPositive_add_smul_of_le (hH := hH) hlam.le) s
  have hlen : (1 - κ) * Δ ≤ ‖s‖ := by
    dsimp [s]
    nlinarith only [(abs_le.mp hnear).1]
  have hκ' : 0 ≤ 1 - κ := sub_nonneg.mpr hκ.2.le
  have hscale : (1 - κ) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hκ' (show 1 - κ ≤ 1 by linarith [hκ.1]) 2
  have hnorm := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg hκ' hΔ.le) hlen 2) hμ
  have hcurv := mul_le_mul_of_nonneg_right hscale hpos
  calc
    quadModel g H s ≤ (1 - κ) ^ 2 * (-(1 / 2) * (⟪s, A s⟫ + μ * Δ ^ 2)) := by
      rw [quadModel_eq_of_shifted_comparison hH hs]
      simp only [sub_self, map_zero, inner_zero_left, zero_sub]
      change μ * ((1 - κ) * Δ) ^ 2 ≤ μ * ‖s‖ ^ 2 at hnorm
      change (1 - κ) ^ 2 * ⟪s, A s⟫ ≤ 1 * ⟪s, A s⟫ at hcurv
      nlinarith only [hnorm, hcurv]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (sq_nonneg _)

/-- Lemma 7.3.6. A correction with the stated shifted curvature bound that reaches
the boundary has model value at most `(1 - κ)` times any feasible comparison value. -/
theorem lemma_7_3_6 {μ Δ κ : ℝ} (hμ : 0 ≤ μ) (hlam : -leftmost hH < μ)
    (hκ : κ ∈ Ioo 0 1) {u v : E} (hu : ‖u‖ ≤ Δ)
    (hboundary : ‖shiftedStep g H μ + v‖ = Δ)
    (hdir : ⟪v, (H + μ • (1 : E →L[ℝ] E)) v⟫ ≤ κ *
      (⟪shiftedStep g H μ, (H + μ • (1 : E →L[ℝ] E)) (shiftedStep g H μ)⟫ + μ * Δ ^ 2)) :
    quadModel g H (shiftedStep g H μ + v) ≤ (1 - κ) * quadModel g H u := by
  let s := shiftedStep g H μ
  let A := H + μ • (1 : E →L[ℝ] E)
  have hs : A s = -g := (step_spec (g := g) hlam).1
  have hlower := quadModel_lower_bound_of_shifted (hH := hH) hμ hlam hs hu
  calc
    quadModel g H (s + v) ≤ (1 - κ) * (-(1 / 2) * (⟪s, A s⟫ + μ * Δ ^ 2)) := by
      rw [quadModel_eq_of_shifted_comparison hH hs, add_sub_cancel_left]
      change ‖s + v‖ = Δ at hboundary
      rw [hboundary]
      change ⟪v, A v⟫ ≤ κ * (⟪s, A s⟫ + μ * Δ ^ 2) at hdir
      change (1 / 2) * (⟪v, A v⟫ - ⟪s, A s⟫ - μ * Δ ^ 2) ≤ _
      nlinarith only [hdir]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hκ.2.le)

omit [FiniteDimensional ℝ E] in
private theorem quadModel_nonpos_of_isMinOn {Δ : ℝ} (hΔ : 0 ≤ Δ) {sM : E}
    (hmin : IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM) :
    quadModel g H sM ≤ 0 := by
  simpa using hmin (show (0 : E) ∈ Metric.closedBall 0 Δ by simpa using hΔ)

/-- The easy-case norm test yields an acceptable approximation with
`κopt ≤ (1 - κ)²` and `1 + κ ≤ κtr`. -/
theorem acceptable_of_easy_stopping_rule {μ Δ κ κopt κtr : ℝ} (hμ : 0 ≤ μ)
    (hlam : -leftmost hH < μ) (hΔ : 0 < Δ) (hκ : κ ∈ Ioo 0 1)
    {sM : E} (hsM : ‖sM‖ ≤ Δ)
    (hmin : IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM)
    (hnear : |‖shiftedStep g H μ‖ - Δ| ≤ κ * Δ)
    (hopt : κopt ≤ (1 - κ) ^ 2) (htr : 1 + κ ≤ κtr) :
    IsAcceptableModelStep g H Δ κopt κtr (shiftedStep g H μ) sM := by
  have h : IsAcceptableModelStep g H Δ ((1 - κ) ^ 2) (1 + κ) (shiftedStep g H μ) sM :=
    ⟨lemma_7_3_5 hμ hlam hΔ hκ hsM hnear, by nlinarith only [(abs_le.mp hnear).2]⟩
  exact h.weaken hΔ.le (quadModel_nonpos_of_isMinOn hΔ.le hmin) hopt htr

/-- The hard-case shifted curvature test yields an acceptable approximation with
`κopt ≤ 1 - κ` and `1 ≤ κtr`. -/
theorem acceptable_of_hard_stopping_rule {μ Δ κ κopt κtr : ℝ} (hμ : 0 ≤ μ)
    (hlam : -leftmost hH < μ) (hκ : κ ∈ Ioo 0 1) {sM v : E} (hsM : ‖sM‖ ≤ Δ)
    (hmin : IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM)
    (hboundary : ‖shiftedStep g H μ + v‖ = Δ)
    (hdir : ⟪v, (H + μ • (1 : E →L[ℝ] E)) v⟫ ≤ κ *
      (⟪shiftedStep g H μ, (H + μ • (1 : E →L[ℝ] E)) (shiftedStep g H μ)⟫ + μ * Δ ^ 2))
    (hopt : κopt ≤ 1 - κ) (htr : 1 ≤ κtr) :
    IsAcceptableModelStep g H Δ κopt κtr (shiftedStep g H μ + v) sM := by
  have hΔ := (norm_nonneg sM).trans hsM
  have h : IsAcceptableModelStep g H Δ (1 - κ) 1 (shiftedStep g H μ + v) sM :=
    ⟨lemma_7_3_6 hμ hlam hκ hsM hboundary hdir, by simp [hboundary]⟩
  exact h.weaken hΔ (quadModel_nonpos_of_isMinOn hΔ hmin) hopt htr

/-- The safeguarded geometric trial multiplier in (7.3.14). -/
noncomputable abbrev moreSorensenTrial (θ lo hi : ℝ) : ℝ := bracketEstimate 1 θ lo hi

/-- The multiplier update in Algorithm 7.3.4.
With a zero gradient and a successful factorization, the raw step is zero.
This is the upper-bracket branch for positive radius, and it skips Newton's
formula because both triangular solves would give zero.
Here `b` is the lower-bound estimate from the Cholesky direction or partial
factorization. The test against the pole represents the positive definite
factorization test. The return value contains the new lower and upper
endpoints and the next trial. Termination and the step correction are separate. -/
noncomputable def moreSorensenSafeguardedStep (g : E) (H : E →L[ℝ] E)
    (pole Δ θ lo hi x b : ℝ) : ℝ × ℝ × ℝ :=
  if pole < x then
    if ‖g‖ = 0 then
      let lo' := max lo b
      (lo', x, moreSorensenTrial θ lo' x)
    else
      let x' := moreSorensenNewtonStep g H Δ x
      if 0 < phi g H Δ x then
        let lo' := max lo b
        if pole < x' then (lo', x, x')
        else
          let lo'' := max lo' x'
          (lo'', x, moreSorensenTrial θ lo'' x)
      else (max lo x, hi, x')
  else
    let lo' := max (max lo x) b
    (lo', hi, moreSorensenTrial θ lo' hi)

/-- From a positive secular value the safeguarded update either enters the
Newton interval or strengthens the lower endpoint with the failed candidate.
The supplied lower bound may be used in either branch. -/
theorem moreSorensenSafeguardedStep_of_positive_phi (hg : g ≠ 0)
    {Δ θ lo hi x b r : ℝ} (hΔ : 0 < Δ)
    {sM : E} (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (hx : -leftmost hH < x) (hpos : 0 < phi g H Δ x) (hb : b ≤ r)
    (hlo : 0 ≤ lo) (hlr : lo ≤ r) (hrx : r ≤ x) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    let s := moreSorensenSafeguardedStep g H (-leftmost hH) Δ θ lo hi x b
    let x' := moreSorensenNewtonStep g H Δ x
    s.1 ≤ r ∧ s.2.1 = x ∧
      ((s.2.2 = x' ∧ -leftmost hH < x' ∧ phi g H Δ x' ≤ 0 ∧ x' ≤ r) ∨
        (x' ≤ -leftmost hH ∧ x' ≤ s.1 ∧ s.2.2 ∈ Icc s.1 s.2.1)) := by
  have hN := lemma_7_3_3 hg hΔ hsM hmul hx hpos
  dsimp only at hN ⊢
  rcases hN.2.2 with hgood | hbad
  · simp only [moreSorensenSafeguardedStep, ite_eq_left hx,
      ite_eq_right (norm_ne_zero_iff.mpr hg), ite_eq_left hpos, ite_eq_left hgood.1]
    exact ⟨max_le hlr hb, trivial, Or.inl ⟨trivial, hgood.1, hgood.2, hN.2.1⟩⟩
  · simp only [moreSorensenSafeguardedStep, ite_eq_left hx,
      ite_eq_right (norm_ne_zero_iff.mpr hg), ite_eq_left hpos, ite_eq_right (not_lt.mpr hbad)]
    have hnew := max_le (max_le hlr hb) hN.2.1
    exact ⟨hnew, trivial, Or.inr ⟨hbad, le_max_right _ _,
      bracketEstimate_mem_Icc (hlo.trans ((le_max_left _ _).trans (le_max_left _ _)))
        (hnew.trans hrx) (by simp) hθ⟩⟩

omit [FiniteDimensional ℝ E] in
/-- The zero-gradient safeguard tightens the upper endpoint and uses
a bracket trial instead of a Newton candidate. -/
theorem moreSorensenSafeguardedStep_zero_gradient {pole Δ θ lo hi x b : ℝ}
    (hx : pole < x) :
    moreSorensenSafeguardedStep (0 : E) H pole Δ θ lo hi x b =
      (max lo b, x, moreSorensenTrial θ (max lo b) x) := by
  simp [moreSorensenSafeguardedStep, hx]

omit [FiniteDimensional ℝ E] in
/-- Repeating the zero-gradient safeguard gives a hard bracketing run when
the pole is nonnegative. Certified pivot or curvature estimates may tighten
its lower endpoint without changing the multiplier limit. -/
theorem moreSorensen_zero_gradient_run {pole Δ θ : ℝ} {lo hi x b : ℕ → ℝ}
    (hθ : θ ∈ Ioo 0 1) (hlo : 0 ≤ lo 0) (hlp : lo 0 ≤ pole) (hph : pole ≤ hi 0)
    (hx0 : x 0 ∈ Icc (lo 0) (hi 0)) (hb : ∀ k, b k ≤ pole)
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep (0 : E) H pole Δ θ (lo k) (hi k) (x k) (b k)) :
    IsBracketRun pole pole θ θ lo hi x ∧ Tendsto x atTop (𝓝 pole) := by
  have hleft (k : ℕ) (hx : x k ≤ pole) :
      lo (k + 1) = max (max (lo k) (x k)) (b k) ∧ hi (k + 1) = hi k ∧
      x (k + 1) = moreSorensenTrial θ (max (max (lo k) (x k)) (b k)) (hi k) := by
    simpa only [moreSorensenSafeguardedStep, ite_eq_right (not_lt.mpr hx),
      Prod.mk.injEq] using hrec k
  have hright (k : ℕ) (hx : pole < x k) :
      lo (k + 1) = max (lo k) (b k) ∧ hi (k + 1) = x k ∧
      x (k + 1) = moreSorensenTrial θ (max (lo k) (b k)) (x k) := by
    simpa only [moreSorensenSafeguardedStep_zero_gradient hx, Prod.mk.injEq] using hrec k
  have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2.le⟩
  have hinv (k : ℕ) :
      0 ≤ lo k ∧ lo k ≤ pole ∧ pole ≤ hi k ∧ x k ∈ Icc (lo k) (hi k) := by
    induction k with
    | zero => exact ⟨hlo, hlp, hph, hx0⟩
    | succ k ih =>
      rcases le_or_gt (x k) pole with hx | hx
      · obtain ⟨hl, hu, ht⟩ := hleft k hx
        rw [hl, hu, ht]
        have h0 : 0 ≤ max (max (lo k) (x k)) (b k) :=
          ih.1.trans ((le_max_left _ _).trans (le_max_left _ _))
        have hp := max_le (max_le ih.2.1 hx) (hb k)
        exact ⟨h0, hp, ih.2.2.1,
          bracketEstimate_mem_Icc h0 (hp.trans ih.2.2.1) (by simp) hθ'⟩
      · obtain ⟨hl, hu, ht⟩ := hright k hx
        rw [hl, hu, ht]
        have h0 := ih.1.trans (le_max_left _ (b k))
        have hp := max_le ih.2.1 (hb k)
        exact ⟨h0, hp, hx.le, bracketEstimate_mem_Icc h0 (hp.trans hx.le) (by simp) hθ'⟩
  have hrun : IsBracketRun pole pole θ θ lo hi x := by
    refine ⟨hlo, hlp, hph, ?_, ?_, ?_⟩
    · exact fun k hk => (hk.1.not_ge hk.2).elim
    · intro k hx
      obtain ⟨hl, hu, ht⟩ := hleft k hx
      exact ⟨hu, Or.inr ⟨b k, hb k, hl⟩, θ, ⟨le_rfl, le_rfl⟩, 1, by simp,
        by rw [hl, hu, ht]⟩
    · intro k hx
      obtain ⟨hl, hu, ht⟩ := hright k hx
      refine ⟨hu.trans (min_eq_right (hinv k).2.2.2.2).symm, Or.inr ⟨b k, hb k, hl⟩,
        θ, ⟨le_rfl, le_rfl⟩, θ, ⟨le_rfl, le_rfl⟩, le_rfl, 1, by simp, 1, by simp, le_rfl, ?_⟩
      rw [hl, hu, ht]
      exact ⟨le_rfl, le_rfl⟩
  exact ⟨hrun, (hrun.tendsto_bracket_of_never_mem le_rfl hθ.1 hθ.2
    (fun _ hk => hk.1.not_ge hk.2)).2.2⟩

/-- The spectral bounds (7.3.18) on the multiplier of a boundary solution. -/
theorem multiplier_bounds_of_boundary {μ Δ : ℝ} {s : E} (hΔ : 0 < Δ)
    (hμ : -leftmost hH ≤ μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hn : ‖s‖ = Δ) :
    ‖g‖ / Δ - rightmost hH ≤ μ ∧ μ ≤ ‖g‖ / Δ - leftmost hH := by
  obtain ⟨hl, hu⟩ := norm_add_smul_apply_bounds (hH := hH) hμ s
  rw [hs, norm_neg, hn] at hl hu
  exact ⟨sub_le_iff_le_add.mpr ((div_le_iff₀ hΔ).2 hu),
    le_sub_iff_add_le.mpr ((le_div_iff₀ hΔ).2 hl)⟩

/-- The finite-entry part of Theorem 7.3.4 for the safeguarded bracketing phase.
With a nonempty Newton interval and a strictly lower initial bracket end, a trial
multiplier reaches that interval. -/
theorem moreSorensen_bracketing_enters_newton {r θ : ℝ} {lo hi lam : ℕ → ℝ}
    (hrun : IsBracketRun (shiftThreshold hH) r θ θ lo hi lam)
    (hr : shiftThreshold hH < r) (hlo : lo 0 < r) (hθ : θ ∈ Ioo 0 1) :
    ∃ k, lam k ∈ Ioc (shiftThreshold hH) r := by
  obtain ⟨k, -, hk⟩ := hrun.exists_mem hr hlo hθ.1 hθ.2
  exact ⟨k, hk⟩

/-- The multiplier part of Theorem 7.3.4 when safeguarding continues indefinitely.
Every trial lies outside the Newton interval, so the contracting brackets give convergence
to the optimal multiplier. -/
theorem moreSorensen_bracketing_tendsto {r θ : ℝ} {lo hi lam : ℕ → ℝ}
    (hrun : IsBracketRun (shiftThreshold hH) r θ θ lo hi lam)
    (hr : shiftThreshold hH ≤ r) (hθ : θ ∈ Ioo 0 1)
    (hnever : ∀ k, lam k ∉ Ioc (shiftThreshold hH) r) :
    Tendsto lam atTop (𝓝 r) :=
  (hrun.tendsto_bracket_of_never_mem hr hθ.1 hθ.2 hnever).2.2

/-- The easy Newton phase in Theorem 7.3.4. Once a trial has negative secular value above
the pole, the Newton iterates converge quadratically to the root and the shifted steps
converge to the corresponding trust-region solution. -/
theorem moreSorensen_easy_newton_convergence (hg : g ≠ 0) {Δ r x₀ : ℝ}
    (hΔ : 0 < Δ) (hr : -leftmost hH < r) (hr₀ : 0 ≤ r)
    (hroot : secular g H r = Δ ^ 2) (hx₀ : -leftmost hH < x₀) (hbelow : phi g H Δ x₀ < 0) :
    let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
    let sM := shiftedStep g H r
    ConvergesWithOrder x r 2 ∧ Tendsto (fun k => shiftedStep g H (x k)) atTop (𝓝 sM) ∧
      ‖sM‖ ≤ Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM := by
  have hconv := (lemma_7_3_2 hg hΔ hr hroot hx₀ hbelow).2.2.2.2
  have hfun : stepDeriv g H 0 = shiftedStep g H := funext stepDeriv_zero
  have hcont : ContinuousAt (shiftedStep g H) r := by
    rw [← hfun]
    exact (hasDerivAt_stepDeriv (g := g) hr 0).continuousAt
  have hnorm : ‖shiftedStep g H r‖ = Δ := by
    change ‖shiftedStep g H r‖ ^ 2 = Δ ^ 2 at hroot
    nlinarith [norm_nonneg (shiftedStep g H r)]
  have hmul : IsTrustRegionMultiplier g H Δ (shiftedStep g H r) r :=
    ⟨hr₀, (step_spec hr).1, isPositive_add_smul_of_le hr.le, by simp [hnorm]⟩
  exact ⟨hconv, hcont.tendsto.comp hconv.tendsto, hnorm.le, hmul.isMinOn hH⟩

/-- With an interior secular root, safeguarding either finds the root exactly
or supplies a starting value from which the Newton phase converges quadratically. -/
theorem moreSorensen_easy_bracket_then_newton (hg : g ≠ 0) {Δ r θ : ℝ}
    {lo hi lam : ℕ → ℝ} (hΔ : 0 < Δ) (hr : shiftThreshold hH < r)
    (hroot : secular g H r = Δ ^ 2) (hlo : lo 0 < r) (hθ : θ ∈ Ioo 0 1)
    (hrun : IsBracketRun (shiftThreshold hH) r θ θ lo hi lam) :
    ∃ k, lam k = r ∨
      let x := fun j : ℕ => (moreSorensenNewtonStep g H Δ)^[j] (lam k)
      ConvergesWithOrder x r 2 ∧
        Tendsto (fun j => shiftedStep g H (x j)) atTop (𝓝 (shiftedStep g H r)) := by
  obtain ⟨k, hk⟩ := moreSorensen_bracketing_enters_newton hrun hr hlo hθ
  have ha : -leftmost hH < r := neg_leftmost_le_shiftThreshold.trans_lt hr
  refine ⟨k, ?_⟩
  rcases hk.2.lt_or_eq with hkr | hkr
  · have hx : -leftmost hH < lam k := neg_leftmost_le_shiftThreshold.trans_lt hk.1
    have hm := (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.1
    have hbelow : phi g H Δ (lam k) < 0 := phi_root hΔ hroot ▸ hm hx ha hkr
    have h := moreSorensen_easy_newton_convergence hg hΔ ha
      (shiftThreshold_nonneg.trans hr.le) hroot hx hbelow
    exact Or.inr ⟨h.1, h.2.1⟩
  · exact Or.inl hkr

/-- The finite interior branch of Theorem 7.3.4: a feasible unshifted solve
with a positive definite Hessian is already a model minimizer. -/
theorem moreSorensen_interior_solution {Δ : ℝ} (hHpos : -leftmost hH < 0)
    (hs : ‖shiftedStep g H 0‖ ≤ Δ) :
    shiftedStep g H 0 ∈ Metric.closedBall 0 Δ ∧
      IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) (shiftedStep g H 0) := by
  have hmul : IsTrustRegionMultiplier g H Δ (shiftedStep g H 0) 0 :=
    ⟨le_rfl, (step_spec hHpos).1, isPositive_add_smul_of_le hHpos.le, zero_mul _⟩
  exact hmul.isMinOn_of_norm_le hH hs

/-- Interior stopping at zero shift also applies to a singular positive
semidefinite Hessian when an unshifted solve supplies a feasible step. -/
theorem moreSorensen_interior_solution_of_unshifted_solve {Δ : ℝ} {s : E}
    (hHpos : -leftmost hH ≤ 0) (hsolve : H s = -g) (hs : ‖s‖ ≤ Δ) :
    s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) s := by
  have hmul : IsTrustRegionMultiplier g H Δ s 0 :=
    ⟨le_rfl, by simpa using hsolve, isPositive_add_smul_of_le hHpos, zero_mul _⟩
  exact hmul.isMinOn_of_norm_le hH hs

/-- When the gradient vanishes, zero solves the positive semidefinite
case. With a negative leftmost eigenvalue, a scaled unit leftmost eigenvector
solves the boundary problem, with multiplier equal to the pole. -/
theorem moreSorensen_zero_gradient_solution {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ s : E, ‖s‖ ≤ Δ ∧ IsTrustRegionMultiplier (0 : E) H Δ s (shiftThreshold hH) := by
  by_cases hp : -leftmost hH ≤ 0
  · have ht : shiftThreshold hH = 0 := max_eq_left hp
    rw [ht]
    exact ⟨0, by simpa using hΔ, le_rfl, by simp, isPositive_add_smul_of_le hp, zero_mul _⟩
  · have hp' : 0 < -leftmost hH := lt_of_not_ge hp
    have ht : shiftThreshold hH = -leftmost hH := max_eq_right hp'.le
    rw [ht]
    rcases subsingleton_or_nontrivial E with hE | hE
    · rw [leftmost_eq_zero_of_subsingleton (hH := hH), neg_zero] at hp'
      exact (lt_irrefl _ hp').elim
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
    let u : E := hH.eigenvectorBasis rfl i
    have hu : ‖u‖ = 1 := (hH.eigenvectorBasis rfl).orthonormal.norm_eq_one i
    have heig : H u = leftmost hH • u := by
      rw [← hi]
      exact hH.apply_eigenvectorBasis rfl i
    have hnorm : ‖Δ • u‖ = Δ := by simp [norm_smul, abs_of_nonneg hΔ, hu]
    have hsolve : (H + (-leftmost hH) • (1 : E →L[ℝ] E)) (Δ • u) = -(0 : E) := by
      simp [add_apply, smul_apply, one_apply_eq_self, map_smul, heig, neg_smul]
    exact ⟨Δ • u, hnorm.le, hp'.le, hsolve, isPositive_add_smul_of_le le_rfl, by simp [hnorm]⟩

/-- An exact unit leftmost eigenvector provides a direction with the vanishing
shifted curvature required in (7.3.16). This gives an eigensolver-based alternative
to requiring that property of the LINPACK heuristic. -/
theorem moreSorensen_exact_leftmost_curvature_tendsto {u : E} (hu : ‖u‖ = 1)
    (heig : H u = leftmost hH • u) {lam : ℕ → ℝ}
    (hlam : Tendsto lam atTop (𝓝 (-leftmost hH))) :
    Tendsto (fun k => ⟪u, (H + lam k • (1 : E →L[ℝ] E)) u⟫) atTop (𝓝 0) := by
  have heq (k : ℕ) : ⟪u, (H + lam k • (1 : E →L[ℝ] E)) u⟫ = lam k + leftmost hH := by
    simp only [add_apply, smul_apply, one_apply_eq_self, heig, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
    exact add_comm _ _
  simpa only [heq, neg_add_cancel] using hlam.add_const (leftmost hH)

/-- A hard-case boundary correction preserves the vanishing shifted curvature in
(7.3.16). Its scalar coefficient is bounded by twice the radius, since both the
raw and the corrected steps lie in the ball. -/
theorem moreSorensen_hard_correction_curvature_tendsto {Δ : ℝ}
    (lam α : ℕ → ℝ) (u : ℕ → E) (hlam : ∀ k, -leftmost hH < lam k)
    (hraw : ∀ k, ‖shiftedStep g H (lam k)‖ ≤ Δ) (hunit : ∀ k, ‖u k‖ = 1)
    (hboundary : ∀ k, ‖shiftedStep g H (lam k) + α k • u k‖ = Δ)
    (hcurv : Tendsto (fun k => ⟪u k, (H + lam k • (1 : E →L[ℝ] E)) (u k)⟫) atTop (𝓝 0)) :
    Tendsto (fun k => ⟪α k • u k, (H + lam k • (1 : E →L[ℝ] E)) (α k • u k)⟫)
      atTop (𝓝 0) := by
  let A := fun k => H + lam k • (1 : E →L[ℝ] E)
  have hpos (k : ℕ) (w : E) : 0 ≤ ⟪w, A k w⟫ :=
    ContinuousLinearMap.inner_apply_nonneg_of_isPositive
      (isPositive_add_smul_of_le (hlam k).le) w
  have halpha (k : ℕ) : |α k| ≤ 2 * Δ := calc
    _ = ‖α k • u k‖ := by rw [norm_smul, hunit, mul_one, Real.norm_eq_abs]
    _ = ‖(shiftedStep g H (lam k) + α k • u k) - shiftedStep g H (lam k)‖ := by
      rw [add_sub_cancel_left]
    _ ≤ _ := by
      have hn := norm_sub_le (shiftedStep g H (lam k) + α k • u k)
        (shiftedStep g H (lam k))
      rw [hboundary] at hn
      linarith [hraw k]
  have hbound (k : ℕ) : ⟪α k • u k, A k (α k • u k)⟫ ≤ (2 * Δ) ^ 2 * ⟪u k, A k (u k)⟫ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sq]
    apply mul_le_mul_of_nonneg_right _ (hpos k _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (halpha k) 2
  exact squeeze_zero (fun k => hpos k _) hbound
    (by simpa only [mul_zero] using hcurv.const_mul ((2 * Δ) ^ 2))

/-- The hard-case conclusion of Theorem 7.3.4 for boundary corrections whose shifted
curvature tends to zero. Model values converge to the minimum, and every subsequential
limit is a minimizer. In the hard case a single vector limit requires additional control
of the correction directions or uniqueness of the minimizer. -/
theorem moreSorensen_hard_model_convergence {Δ : ℝ} {sM : E} (hsM : ‖sM‖ ≤ Δ)
    (hmin : IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) sM)
    (lam : ℕ → ℝ) (v : ℕ → E) (hlam₀ : ∀ k, 0 ≤ lam k)
    (hlam : ∀ k, -leftmost hH < lam k)
    (hboundary : ∀ k, ‖shiftedStep g H (lam k) + v k‖ = Δ)
    (hcurv : Tendsto (fun k => ⟪v k, (H + lam k • (1 : E →L[ℝ] E)) (v k)⟫) atTop (𝓝 0)) :
    let s := fun k => shiftedStep g H (lam k) + v k
    Tendsto (fun k => quadModel g H (s k)) atTop (𝓝 (quadModel g H sM)) ∧
      (∀ (j : ℕ → ℕ) (u : E), Tendsto j atTop atTop →
        Tendsto (s ∘ j) atTop (𝓝 u) →
        u ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) u) ∧
      ((∀ u ∈ Metric.closedBall 0 Δ,
        IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) u → u = sM) →
        Tendsto s atTop (𝓝 sM)) := by
  let s := fun k => shiftedStep g H (lam k) + v k
  have hfeas (k : ℕ) : s k ∈ Metric.closedBall 0 Δ :=
    mem_closedBall_zero_iff.mpr (hboundary k).le
  have hgap (k : ℕ) : quadModel g H (s k) - quadModel g H sM ≤
      (1 / 2) * ⟪v k, (H + lam k • (1 : E →L[ℝ] E)) (v k)⟫ := by
    have hs := (step_spec (g := g) (hlam k)).1
    have hlow := quadModel_lower_bound_of_shifted (hH := hH) (hlam₀ k) (hlam k) hs hsM
    have heq := quadModel_eq_of_shifted_comparison hH hs (s k)
    have hdiff : s k - shiftedStep g H (lam k) = v k := by dsimp [s]; abel
    rw [show step g H (lam k) = shiftedStep g H (lam k) from rfl, hdiff, hboundary k] at heq
    linarith only [hlow, heq]
  have ht : Tendsto (fun k => quadModel g H (s k) - quadModel g H sM) atTop (𝓝 0) :=
    squeeze_zero (fun k => sub_nonneg.mpr ((isMinOn_iff.mp hmin) _ (hfeas k))) hgap
      (by simpa only [mul_zero] using hcurv.const_mul (1 / 2))
  have hval : Tendsto (fun k => quadModel g H (s k)) atTop (𝓝 (quadModel g H sM)) := by
    simpa only [sub_add_cancel, zero_add] using ht.add_const (quadModel g H sM)
  have hcluster (j : ℕ → ℕ) (u : E) (hj : Tendsto j atTop atTop)
      (hu : Tendsto (s ∘ j) atTop (𝓝 u)) :
      u ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) u := by
    refine ⟨Metric.isClosed_closedBall.mem_of_tendsto hu
      (Eventually.of_forall fun k => hfeas (j k)), ?_⟩
    have hq : quadModel g H u = quadModel g H sM :=
      tendsto_nhds_unique ((continuous_quadModel g H).continuousAt.tendsto.comp hu) (hval.comp hj)
    rw [isMinOn_iff]
    intro x hx
    rw [hq]
    exact (isMinOn_iff.mp hmin) x hx
  refine ⟨hval, hcluster, fun hunique => ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hbad
  have hfreq : ∃ᶠ k in atTop, ¬ dist (s k) sM < ε := by
    simpa only [Filter.Frequently, not_not] using hbad
  have hin : ∃ᶠ k in atTop, s k ∈ Metric.closedBall 0 Δ ∩ (Metric.ball sM ε)ᶜ :=
    hfreq.mono fun k hk => ⟨hfeas k, hk⟩
  obtain ⟨u, hu, j, hj, hju⟩ :=
    ((isCompact_closedBall (0 : E) Δ).inter_right
      Metric.isOpen_ball.isClosed_compl).tendsto_subseq' hin
  obtain ⟨huf, hum⟩ := hcluster j u hj.tendsto_atTop hju
  have heq : u = sM := hunique u huf hum
  exact hu.2 (by simpa [heq, Metric.mem_ball] using hε)

/-- In the hard bracketing phase, a strictly feasible upper endpoint guarantees
arbitrarily late positive-definite trials. -/
theorem moreSorensen_hard_bracketing_subsequence {θ : ℝ} {lo hi lam : ℕ → ℝ}
    (hθ : θ ∈ Ioo 0 1) (hrun : IsBracketRun (-leftmost hH) (-leftmost hH) θ θ lo hi lam)
    (hhi : -leftmost hH < hi 0) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧ ∀ k, -leftmost hH < lam (j k) :=
  exists_seq_forall_of_frequently (hrun.frequently_gt_of_eq rfl hhi hθ.1 hθ.2)

/-- A fixed root of the boundary equation in Step 3b(iii) of Algorithm 7.3.4
for a unit correction direction. Fixing the root makes the correction continuous. -/
noncomputable def moreSorensenBoundaryCoefficient (Δ : ℝ) (s u : E) : ℝ :=
  √(Δ ^ 2 - ‖s‖ ^ 2 + ⟪s, u⟫ ^ 2) - ⟪s, u⟫

omit [FiniteDimensional ℝ E] in
/-- The selected correction reaches the boundary from any step in the ball. -/
theorem norm_add_boundaryCorrection {Δ : ℝ} {s u : E} (hs : ‖s‖ ≤ Δ) (hu : ‖u‖ = 1) :
    ‖s + moreSorensenBoundaryCoefficient Δ s u • u‖ = Δ := by
  let c := ⟪s, u⟫
  let d := √(Δ ^ 2 - ‖s‖ ^ 2 + c ^ 2)
  have hsq := pow_le_pow_left₀ (norm_nonneg s) hs 2
  have hd : d ^ 2 = Δ ^ 2 - ‖s‖ ^ 2 + c ^ 2 :=
    Real.sq_sqrt (add_nonneg (sub_nonneg.mpr hsq) (sq_nonneg _))
  change ‖s + (d - c) • u‖ = Δ
  have heq : ‖s + (d - c) • u‖ ^ 2 = Δ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
    change ‖s‖ ^ 2 + 2 * ((d - c) * c) + (d - c) ^ 2 = Δ ^ 2
    nlinarith only [hd]
  have hΔ := (norm_nonneg s).trans hs
  simpa only [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hΔ] using
    (sq_eq_sq_iff_abs_eq_abs _ _).mp heq

/-- A corrected hard-phase version of Theorem 7.3.4. Safeguarding converges to the
pole. On the positive-definite subsequence, using a fixed unit leftmost eigenvector
and a fixed root formula for the boundary correction gives a vector limit that
minimizes the model. The correction uses exact spectral data in place of the
LINPACK direction heuristic. -/
theorem moreSorensen_hard_bracket_then_exact_correction (hg : g ≠ 0)
    {Δ θ : ℝ} {sM : E} {lo hi lam : ℕ → ℝ} (hθ : θ ∈ Ioo 0 1)
    (hrun : IsBracketRun (-leftmost hH) (-leftmost hH) θ θ lo hi lam)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM (-leftmost hH))
    (hhi : -leftmost hH < hi 0) {u : E} (hu : ‖u‖ = 1) (heig : H u = leftmost hH • u) :
    Tendsto lam atTop (𝓝 (-leftmost hH)) ∧
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      (∀ k, -leftmost hH < lam (j k)) ∧
      let α := fun k => moreSorensenBoundaryCoefficient Δ (shiftedStep g H (lam (j k))) u
      let s := fun k => shiftedStep g H (lam (j k)) + α k • u
      (∀ k, ‖s k‖ = Δ) ∧
      Tendsto (fun k => quadModel g H (s k)) atTop (𝓝 (quadModel g H sM)) ∧
      ∃ w : E, Tendsto s atTop (𝓝 w) ∧ w ∈ Metric.closedBall 0 Δ ∧
        IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) w := by
  have hlim := (hrun.tendsto_bracket_of_never_mem le_rfl hθ.1 hθ.2 (fun k => by simp)).2.2
  obtain ⟨j, hj, hpos⟩ := moreSorensen_hard_bracketing_subsequence hθ hrun hhi
  have hraw (k : ℕ) : ‖shiftedStep g H (lam (j k))‖ ≤ Δ := by
    have hs := (secular_lt_norm_sq_of_shifted (hH := hH) hg le_rfl hmul.shifted (hpos k)).le
    have hΔ : 0 ≤ Δ := (norm_nonneg sM).trans hsM
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hΔ two_ne_zero).mp
      (hs.trans (pow_le_pow_left₀ (norm_nonneg sM) hsM 2))
  let α := fun k => moreSorensenBoundaryCoefficient Δ (shiftedStep g H (lam (j k))) u
  have hboundary (k : ℕ) : ‖shiftedStep g H (lam (j k)) + α k • u‖ = Δ :=
    norm_add_boundaryCorrection (hraw k) hu
  have hcurv := moreSorensen_exact_leftmost_curvature_tendsto hu heig (hlim.comp hj)
  have hvc := moreSorensen_hard_correction_curvature_tendsto
    (lam ∘ j) α (fun _ => u) hpos hraw (fun _ => hu) hboundary hcurv
  have h := moreSorensen_hard_model_convergence (hH := hH) hsM (hmul.isMinOn hH)
    (lam ∘ j) (fun k => α k • u) (fun k => hmul.nonneg.trans (hpos k).le) hpos hboundary hvc
  let p := particular hH g (-leftmost hH)
  have hgorth := (particular_add_of_shifted (hH := hH) hmul.shifted).1
  have hright : Tendsto (lam ∘ j) atTop (𝓝[>] (-leftmost hH)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim.comp hj, Eventually.of_forall hpos⟩
  have hp : Tendsto (fun k => shiftedStep g H (lam (j k))) atTop (𝓝 p) :=
    ((tendsto_step_threshold (hH := hH)).1 hgorth).1.comp hright
  have hcont : Continuous (fun s : E => moreSorensenBoundaryCoefficient Δ s u) := by
    unfold moreSorensenBoundaryCoefficient
    fun_prop
  let w := p + moreSorensenBoundaryCoefficient Δ p u • u
  have hw : Tendsto (fun k => shiftedStep g H (lam (j k)) + α k • u) atTop (𝓝 w) :=
    hp.add ((hcont.continuousAt.tendsto.comp hp).smul tendsto_const_nhds)
  refine ⟨hlim, j, hj, hpos, hboundary, h.1, w, hw, ?_⟩
  exact h.2.1 id w tendsto_id hw

end ConnGouldToint.Chapter07
