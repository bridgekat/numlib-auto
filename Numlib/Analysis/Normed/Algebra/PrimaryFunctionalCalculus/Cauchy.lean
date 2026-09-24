import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Basic

/-!
# The Cauchy integral of the primary functional calculus

The Cauchy integral representation of `pfc` ([golub2013matrix] (9.2.8)), for contours that are
circles, the only contours Mathlib integrates over (`circleIntegral`): if `f` is holomorphic on a
closed disc whose interior contains the spectrum of `a`, then

  `f(a) = (2πi)⁻¹ ∮_{|z - c| = R} f(z) (z - a)⁻¹ dz`.

A general closed contour enclosing the spectrum is not formalized (it needs winding numbers).

## Main results

* `circleIntegral_div_sub_pow`: the scalar Cauchy formula for derivatives at any point of the disc,
  `∮ f(z)/(z - w)^{j+1} dz = 2πi f⁽ʲ⁾(w)/j!` (Mathlib has it at the centre only).
* `inverse_sub_eq_sum_spectralIdempotent`: the resolvent in the spectral decomposition,
  `(z - a)⁻¹ = ∑_λ ∑_{j < m_λ} (z - λ)^{-(j+1)} (a - λ)ʲ E_λ` for `z` outside the spectrum.
* `pfc_eq_circleIntegral`: the Cauchy integral formula for `pfc`.

The route avoids contour deformation: both sides are read on the spectral decomposition, and the
scalar formula at a non-central point comes from the Taylor expansion with analytic remainder
(`AnalyticAt.exists_eq_sum_add_pow_mul`) and Cauchy's theorem for the remainder.
-/

open Polynomial Hermite Complex Metric
open scoped Real

section Resolvent

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [Ring A] [Algebra 𝕜 A]

/-- **The resolvent in the spectral decomposition**: for `z` not an eigenvalue of `a` (integral,
split minimal polynomial), `(z - a)⁻¹ = ∑_λ ∑_{j < m_λ} (z - λ)^{-(j+1)} (a - λ)ʲ E_λ`. -/
theorem inverse_sub_eq_sum_spectralIdempotent [DecidableEq 𝕜] {a : A} (ha : IsIntegral 𝕜 a)
    (hs : (minpoly 𝕜 a).Splits) {z : 𝕜} (hz : z ∉ (minpoly 𝕜 a).roots) :
    Ring.inverse (algebraMap 𝕜 A z - a) = ∑ l ∈ (minpoly 𝕜 a).roots.toFinset,
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
        ((z - l) ^ (j + 1))⁻¹ • ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) := by
  set w := algebraMap 𝕜 A z - a
  set Q := ∑ l ∈ (minpoly 𝕜 a).roots.toFinset,
    ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
      ((z - l) ^ (j + 1))⁻¹ • ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l)
  have hwQ : w * Q = 1 := by
    rw [← sum_spectralIdempotent ha hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hzl : z - l ≠ 0 := sub_ne_zero.mpr fun h =>
      hz (h ▸ Multiset.mem_toFinset.mp hl)
    set N := a - algebraMap 𝕜 A l
    set E := spectralIdempotent a l
    have hw : w = (z - l) • 1 - N := by
      simp only [w, N, Algebra.smul_def, mul_one, map_sub]
      abel
    set F : ℕ → A := fun j => ((z - l) ^ j)⁻¹ • (N ^ j * E)
    have hterm : ∀ j, w * (((z - l) ^ (j + 1))⁻¹ • (N ^ j * E)) = F j - F (j + 1) := by
      intro j
      simp only [F, hw, sub_mul, smul_mul_assoc, one_mul, mul_smul_comm, ← mul_assoc,
        ← pow_succ']
      rw [pow_succ, mul_inv, mul_comm, smul_sub, smul_smul, mul_right_comm ((z - l)⁻¹),
        inv_mul_cancel₀ hzl, one_mul]
    rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_range_sub']
    simp only [F, pow_zero, inv_one, one_smul, one_mul, pow_mul_spectralIdempotent ha hs l,
      smul_zero, sub_zero, N, E]
  have hcomm : Commute w Q := by
    refine Commute.sum_right _ _ _ fun l _ => Commute.sum_right _ _ _ fun j _ => ?_
    refine Commute.smul_right ?_ _
    have h1 : Commute w a := (Algebra.commute_algebraMap_left z a).sub_left (Commute.refl a)
    have h2 : Commute w (a - algebraMap 𝕜 A l) :=
      h1.sub_right (Algebra.commute_algebraMap_right l w)
    have h3 : Commute w (spectralIdempotent a l) := by
      have := commute_spectralIdempotent a l
      exact ((Algebra.commute_algebraMap_left z _).sub_left this)
    exact (h2.pow_right j).mul_right h3
  have hQw : Q * w = 1 := hcomm.eq ▸ hwQ
  rw [Ring.inverse_unit ⟨w, Q, hwQ, hQw⟩]
  rfl

end Resolvent

section Scalar

/-- **Cauchy's formula for derivatives at any point of the disc**: if `f` is holomorphic on the
closed disc `closedBall c R` and `w` lies in the open disc, then
`∮_{|z - c| = R} f(z)/(z - w)^{j+1} dz = 2πi f⁽ʲ⁾(w)/j!`. -/
theorem circleIntegral_div_sub_pow {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) (j : ℕ) :
    (∮ z in C(c, R), f z / (z - w) ^ (j + 1)) = 2 * π * I * taylorJet f w j := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hwa : AnalyticAt ℂ f w :=
    hf.analyticAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hw) ball_subset_closedBall)
  have hsh : AnalyticAt ℂ (fun z => f (w + z)) 0 :=
    hwa.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun z : ℂ => w + z) 0) (by simp)
  obtain ⟨F, hFa, hF⟩ := AnalyticAt.exists_eq_sum_add_pow_mul hsh (j + 1)
  simp only [iteratedDeriv_comp_const_add, add_zero, smul_eq_mul] at hF
  set T : ℂ → ℂ := fun y => ∑ i ∈ Finset.range (j + 1),
    (y - w) ^ i / (i.factorial : ℂ) * iteratedDeriv i f w
  set H : ℂ → ℂ := fun z => F (z - w)
  set G : ℂ → ℂ := fun y => (f y - T y) / (y - w) ^ (j + 1)
  have hHG : ∀ y, y ≠ w → H y = G y := fun y hy => by
    have hyw : (y - w) ^ (j + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hy)
    have := hF (y - w)
    rw [add_sub_cancel] at this
    simp only [H, G, T, this, add_sub_cancel_left, mul_div_cancel_left₀ _ hyw]
  have hHG' : ∀ y, y ≠ w → H =ᶠ[nhds y] G := fun y hy =>
    (isOpen_compl_singleton.eventually_mem hy).mono fun x hx => hHG x hx
  have hsphere : ∀ z ∈ sphere c R, z ≠ w := fun z hz h => by
    rw [h, mem_sphere] at hz
    exact (ne_of_lt (mem_ball.mp hw)) hz
  have hTc : Continuous T := by fun_prop
  -- `H` is continuous on the closed disc and holomorphic inside
  have hHc : ContinuousOn H (closedBall c R) := by
    intro z hz
    by_cases hzw : z = w
    · subst hzw
      exact (hFa.continuousAt.comp_of_eq (continuousAt_id.sub continuousAt_const)
        (by simp)).continuousWithinAt
    · have hG : ContinuousWithinAt G (closedBall c R) z :=
        ((hf.continuousOn z hz).sub hTc.continuousWithinAt).div
          (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hzw))
      exact hG.congr_of_eventuallyEq (nhdsWithin_le_nhds (hHG' z hzw)) (hHG z hzw)
  have hH : (∮ z in C(c, R), H z) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      (Set.countable_singleton w) hHc fun z hz => ?_
    have hzw : z ≠ w := hz.2
    have hfz : DifferentiableAt ℂ f z :=
      hf.differentiableAt
        (Filter.mem_of_superset (isOpen_ball.mem_nhds hz.1) ball_subset_closedBall)
    have hG : DifferentiableAt ℂ G z :=
      (hfz.sub (by fun_prop)).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hzw))
    exact hG.congr_of_eventuallyEq (hHG' z hzw)
  -- the Taylor expansion on the circle
  have hexp : Set.EqOn (fun z => f z / (z - w) ^ (j + 1)) (fun z =>
      ∑ i ∈ Finset.range (j + 1), taylorJet f w i * (z - w) ^ ((i : ℤ) - (j + 1)) + H z)
      (sphere c R) := by
    intro z hz
    have hzw : z - w ≠ 0 := sub_ne_zero.mpr (hsphere z hz)
    simp only
    rw [hHG z (hsphere z hz)]
    have hsum : ∑ i ∈ Finset.range (j + 1), taylorJet f w i * (z - w) ^ ((i : ℤ) - (j + 1)) =
        T z / (z - w) ^ (j + 1) := by
      simp only [T, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zpow_sub₀ hzw, zpow_natCast, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, taylorJet]
      field_simp
    simp only [G]
    rw [hsum]
    ring
  have hterm : ∀ i ∈ Finset.range (j + 1), CircleIntegrable
      (fun z => taylorJet f w i * (z - w) ^ ((i : ℤ) - (j + 1))) c R := fun i _ =>
    ContinuousOn.circleIntegrable hR.le (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).zpow₀ _
        fun z hz => Or.inl (sub_ne_zero.mpr (hsphere z hz))))
  rw [circleIntegral.integral_congr hR.le hexp, circleIntegral.integral_add
    (CircleIntegrable.fun_sum _ hterm)
    (hHc.mono sphere_subset_closedBall |>.circleIntegrable hR.le),
    hH, add_zero, circleIntegral.integral_fun_sum hterm]
  simp only [circleIntegral.integral_const_mul]
  rw [Finset.sum_eq_single j (fun i hi hij => ?_) (by simp)]
  · have : ((j : ℤ) - (j + 1)) = -1 := by ring
    simp only [this, zpow_neg, zpow_one]
    rw [circleIntegral.integral_sub_inv_of_mem_ball hw]
    ring
  · rw [circleIntegral.integral_sub_zpow_of_ne (by omega), mul_zero]

end Scalar

section Integral

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **The Cauchy integral formula for `pfc`** ([golub2013matrix] (9.2.8), circular contours): if
`f` is holomorphic on the closed disc `closedBall c R` and the spectrum of the integral element `a`
lies in the open disc, then `f(a) = (2πi)⁻¹ ∮_{|z - c| = R} f(z) (z - a)⁻¹ dz`. -/
theorem pfc_eq_circleIntegral {a : A} (ha : IsIntegral ℂ a) {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hσ : spectrum ℂ a ⊆ ball c R) :
    pfc f a = (2 * π * I)⁻¹ • ∮ z in C(c, R), f z • Ring.inverse (algebraMap ℂ A z - a) := by
  classical
  have hs := IsAlgClosed.splits (minpoly ℂ a)
  have hball : ∀ l ∈ (minpoly ℂ a).roots.toFinset, l ∈ ball c R := fun l hl => hσ (by
    rw [spectrum.mem_iff_isRoot_minpoly ha]
    exact (mem_roots (minpoly.ne_zero ha)).mp (Multiset.mem_toFinset.mp hl))
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  have hR : 0 ≤ R := by
    obtain ⟨l, hl⟩ := hs.exists_eval_eq_zero
      (ne_of_gt (natDegree_pos_iff_degree_pos.mp (minpoly.natDegree_pos ha)))
    exact (pos_of_mem_ball (hσ ((spectrum.mem_iff_isRoot_minpoly ha).mpr hl))).le
  set X : ℂ → ℕ → A := fun l j => (a - algebraMap ℂ A l) ^ j * spectralIdempotent a l
  have hne : ∀ l ∈ (minpoly ℂ a).roots.toFinset, ∀ z ∈ sphere c R, z - l ≠ 0 :=
      fun l hl z hz h => by
    rw [sub_eq_zero.mp h, mem_sphere] at hz
    exact (ne_of_lt (mem_ball.mp (hball l hl))) hz
  have hcongr : Set.EqOn (fun z => f z • Ring.inverse (algebraMap ℂ A z - a))
      (fun z => ∑ l ∈ (minpoly ℂ a).roots.toFinset,
        ∑ j ∈ Finset.range ((minpoly ℂ a).rootMultiplicity l),
          (f z / (z - l) ^ (j + 1)) • X l j) (sphere c R) := by
    intro z hz
    have hz' : z ∉ (minpoly ℂ a).roots := fun h =>
      hne z (Multiset.mem_toFinset.mpr h) z hz (sub_self z)
    simp only
    rw [inverse_sub_eq_sum_spectralIdempotent ha hs hz', Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, div_eq_mul_inv]
  have hint : ∀ l ∈ (minpoly ℂ a).roots.toFinset, ∀ j,
      CircleIntegrable (fun z => (f z / (z - l) ^ (j + 1)) • X l j) c R := fun l hl j =>
    ContinuousOn.circleIntegrable hR (((hf.continuousOn.mono sphere_subset_closedBall).div
      (by fun_prop) fun z hz => pow_ne_zero _ (hne l hl z hz)).smul continuousOn_const)
  rw [circleIntegral.integral_congr hR hcongr,
    circleIntegral.integral_fun_sum fun l hl => CircleIntegrable.fun_sum _ fun j _ => hint l hl j]
  rw [Finset.sum_congr rfl fun l hl => circleIntegral.integral_fun_sum fun j _ => hint l hl j]
  simp only [circleIntegral.integral_smul_const]
  rw [pfc_eq_sum_spectralIdempotent ha hs, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [circleIntegral_div_sub_pow hf (hball l hl), smul_smul, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_mul]

end Integral
