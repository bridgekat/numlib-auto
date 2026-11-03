import Numlib.Nonlinear.ScalarNewton
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

end ConnGouldToint.Chapter07
