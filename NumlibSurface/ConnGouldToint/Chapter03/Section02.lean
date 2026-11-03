import Numlib.Optimization.Optimality.Unconstrained

/-! # Optimality conditions

Unconstrained smooth minimization in Section 3.2 of [conn2000trust].
The Fréchet differential is zero exactly when the Euclidean gradient vanishes.
-/

open Set Filter Topology

namespace ConnGouldToint.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 3.2.1.** The differential vanishes at a differentiable unconstrained
local minimizer. -/
theorem theorem_3_2_1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) {x : E} (hx : IsLocalMin f x) :
    fderiv ℝ f x = 0 :=
  hx.hasFDerivAt_eq_zero (hf.differentiable (by norm_num) x).hasFDerivAt

/-- **AF.1.** The objective function is twice continuously differentiable. -/
abbrev AF1 (f : E → ℝ) : Prop := ContDiff ℝ 2 f

/-- **Theorem 3.2.2.** At a twice continuously differentiable unconstrained local minimizer,
the differential vanishes and the Hessian is positive semidefinite. -/
theorem theorem_3_2_2 {f : E → ℝ} (hf : AF1 f) {x : E} (hx : IsLocalMin f x) :
    fderiv ℝ f x = 0 ∧ ∀ s : E, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => s) :=
  ⟨theorem_3_2_1 (hf.of_le (by norm_num)) hx,
    IsLocalMin.iteratedFDeriv_two_apply_self_nonneg hx hf.contDiffAt⟩

/-- **Theorem 3.2.3.** A stationary point with positive-definite Hessian is a strict
local minimizer and has a neighbourhood containing no other local minimizers. -/
theorem theorem_3_2_3 [FiniteDimensional ℝ E] {f : E → ℝ} (hf : AF1 f)
    {x : E} (hx : fderiv ℝ f x = 0)
    (hpos : ∀ s : E, s ≠ 0 → 0 < iteratedFDeriv ℝ 2 f x (fun _ => s)) :
    Optimization.IsStrictLocalMin f x ∧ ∀ᶠ y in 𝓝 x, IsLocalMin f y → y = x := by
  refine ⟨Optimization.isStrictLocalMin_of_fderiv_eq_zero_of_posDef hf.contDiffAt hx hpos, ?_⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Eventually.of_forall fun y _ => Subsingleton.elim y x
  let H := iteratedFDeriv ℝ 2 f
  let c := minCurvature (H x)
  obtain ⟨v, hv, hvc⟩ := exists_eq_minCurvature (H x)
  have hc : 0 < c := by
    rw [show c = H x (fun _ => v) from hvc.symm]
    exact hpos v (by rintro rfl; simp at hv)
  have hH : Continuous H := hf.continuous_iteratedFDeriv'
  have hclose : ∀ᶠ z in 𝓝 x, dist (H z) (H x) < c :=
    hH.continuousAt (Metric.ball_mem_nhds (H x) hc)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hclose
  have hcurv (z : E) (hz : dist z x < r) : 0 < minCurvature (H z) := by
    have h := abs_minCurvature_sub_le (A := H z) (B := H x)
    have h' := hball (y := z) hz
    rw [dist_eq_norm] at h'
    linarith [neg_abs_le (minCurvature (H z) - minCurvature (H x))]
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy hymin
  by_contra hyx
  let d := y - x
  let g : ℝ → ℝ := fun t => fderiv ℝ f (x + t • d) d
  have hd : ∀ t : ℝ, HasDerivAt g (fderiv ℝ (fderiv ℝ f) (x + t • d) d d) t := by
    intro t
    have hseg : HasDerivAt (fun u : ℝ => x + u • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hF : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have h := hF.differentiable (by norm_num) (x + t • d)
    simpa [g] using (h.hasFDerivAt.comp_hasDerivAt t hseg).clm_apply (hasDerivAt_const t d)
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope g (by norm_num : (0 : ℝ) < 1)
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
  have hnear : dist (x + t • d) x < r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
    have hy' : ‖d‖ < r := by simpa [Metric.mem_ball, dist_eq_norm, d] using hy
    exact (mul_le_of_le_one_left (norm_nonneg d) ht.2.le).trans_lt hy'
  have hdpos : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hyx)) _
  have hdiag : 0 < H (x + t • d) (fun _ => d) :=
    (mul_pos (hcurv _ hnear) hdpos).trans_le (minCurvature_mul_norm_sq_le _ _)
  have hstat := theorem_3_2_1 (hf.of_le (by norm_num)) hymin
  have hy' : x + d = y := by dsimp [d]; abel
  rw [(hd t).deriv] at he
  simp [g, hy', hstat, hx] at he
  exact hdiag.ne' (by simpa [H, iteratedFDeriv_two_apply] using he)

end ConnGouldToint.Chapter03
