import NumlibSurface.ConnGouldToint.Chapter06.Section04

/-! # Asymptotically convex models -/

open Set Filter Topology

namespace ConnGouldToint.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The step bound (6.5.2). The Hessian bound (6.5.1) is expressed as a bound on its
quadratic form in the step direction. The BTR decrease condition supplies
`m (x + s) ≤ m x`. The derivative norm equals the gradient norm in Euclidean space. -/
theorem lemma_6_5_1 {m : E → ℝ} {x s : E} {ε : ℝ} (hε : 0 < ε)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ m (x + t • s))
    (hDm : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fderiv ℝ m) (x + t • s))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ε * ‖s‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ m) (x + t • s) s s)
    (hdec : m (x + s) ≤ m x) : ‖s‖ ≤ 2 / ε * ‖fderiv ℝ m x‖ := by
  let c := ε * ‖s‖ ^ 2
  let a := fderiv ℝ m x s
  let v (t : ℝ) := fderiv ℝ m (x + t • s) s - c * t
  have hv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt v (fderiv ℝ (fderiv ℝ m) (x + t • s) s s - c) t := by
    simpa [v] using ((hDm t ht).hasDerivAt_comp_add_smul.clm_apply
      (hasDerivAt_const t s)).fun_sub ((hasDerivAt_id t).const_mul c)
  have hmono : MonotoneOn v (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht ↦ (hv t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ by
        rw [(hv t (interior_subset ht)).deriv]
        exact sub_nonneg.mpr (hH t (interior_subset ht)))
  let w (t : ℝ) := m (x + t • s) - (a * t + c * t ^ 2 / 2)
  have hw (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt w (v t - a) t := by
    refine ((hm t ht).hasDerivAt_comp_add_smul.sub
      (((hasDerivAt_id t).const_mul a).add
        ((((hasDerivAt_id t).fun_pow 2).const_mul c).div_const 2))).congr_deriv ?_
    simp [v]
    ring
  have hmono' : MonotoneOn w (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht ↦ (hw t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hw t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ by
        rw [(hw t (interior_subset ht)).deriv, sub_nonneg]
        simpa [v, a] using hmono (by simp) (interior_subset ht) (interior_subset ht).1)
  have hstep : m x ≤ m (x + s) - (a + c / 2) := by
    simpa [w] using hmono' (show (0 : ℝ) ∈ Icc 0 1 by simp)
      (show (1 : ℝ) ∈ Icc 0 1 by simp) zero_le_one
  have ha : -a ≤ ‖fderiv ℝ m x‖ * ‖s‖ :=
    (neg_le_abs a).trans ((Real.norm_eq_abs a).symm ▸ (fderiv ℝ m x).le_opNorm s)
  rcases eq_or_ne s 0 with rfl | hs
  · rw [norm_zero]
    positivity
  have hs' := norm_pos_iff.mpr hs
  have hprod : (ε * ‖s‖) * ‖s‖ ≤ (2 * ‖fderiv ℝ m x‖) * ‖s‖ := by
    dsimp [c] at hstep
    nlinarith only [hstep, hdec, ha]
  have hb := le_of_mul_le_mul_right hprod hs'
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hε).mpr (by linarith)

/-- AM.5, agreement of the Hessians at the model centers when the objective
derivatives at those centers tend to zero. -/
def ModelHessianAgreement (f : E → ℝ) (m : ℕ → E → ℝ) (x : ℕ → E) : Prop :=
  Tendsto (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop (𝓝 0) →
    Tendsto (fun k ↦ ‖fderiv ℝ (fderiv ℝ f) (x k) - fderiv ℝ (fderiv ℝ (m k)) (x k)‖)
      atTop (𝓝 0)

/-- Uniform vanishing of the Hessian variation on a family of step segments. -/
def HessianVariationVanishes (m : ℕ → E → ℝ) (x s : ℕ → E) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
    ‖fderiv ℝ (fderiv ℝ (m k)) (x k + t • s k) - fderiv ℝ (fderiv ℝ (m k)) (x k)‖ ≤ ε

private theorem abs_model_error_le {f m : E → ℝ} {x s : E} {B : ℝ}
    (hf : ContDiff ℝ 2 f) (hval : f x = m x) (hgrad : fderiv ℝ f x = fderiv ℝ m x)
    (hm : ∀ z ∈ segment ℝ x (x + s), DifferentiableAt ℝ m z)
    (hDm : ∀ z ∈ segment ℝ x (x + s), DifferentiableAt ℝ (fderiv ℝ m) z)
    (hB : ∀ z ∈ segment ℝ x (x + s),
      ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ m) z‖ ≤ B) :
    |f (x + s) - m (x + s)| ≤ (1 / 2 : ℝ) * B * ‖s‖ ^ 2 := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  let S := segment ℝ x (x + s)
  let D := f - m
  have hS : Convex ℝ S := convex_segment ..
  have hx : x ∈ S := left_mem_segment ..
  have hs : x + s ∈ S := right_mem_segment ..
  have hdiff (z : E) (hz : z ∈ S) : DifferentiableAt ℝ D z :=
    (hf.differentiable (by norm_num) z).sub (hm z hz)
  have hderiv (z : E) (hz : z ∈ S) :
      fderiv ℝ D z = fderiv ℝ f z - fderiv ℝ m z :=
    fderiv_sub (hf.differentiable (by norm_num) z) (hm z hz)
  have hd (z : E) (hz : z ∈ S) :
      HasFDerivWithinAt (fderiv ℝ D)
        (fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ m) z) S z :=
    (((hDf.differentiable (by norm_num) z).hasFDerivAt.sub
      (hDm z hz).hasFDerivAt).hasFDerivWithinAt).congr hderiv (hderiv z hz)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • s ∈ S := by
    simpa only [add_sub_cancel_left] using hS.add_smul_sub_mem hx hs ht
  have hbound := norm_sub_firstOrder_le_of_lipschitz_on_segment
    (f := D) (x := x) (s := s) (γ := B) (fun t ht ↦ hdiff _ (hseg t ht)) (by
      intro t ht
      have hb := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hB hx (hseg t ht)
      simpa only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1, mul_assoc] using hb)
  simpa [D, hval, hderiv x hx, hgrad, Real.norm_eq_abs] using hbound

/-- Corrected Lemma 6.5.3. The two variation assumptions supply the uniform
control along vanishing steps used in the printed proof. Pointwise twice
differentiability alone does not give this control. The center gradient limit
is supplied by Theorem 6.4.6 for a BTR run. -/
theorem lemma_6_5_3 {P : BTRParams} {f : E → ℝ}
    {x s : ℕ → E} {m : ℕ → E → ℝ} {j : ℕ → ℕ} (hj : Tendsto j atTop atTop)
    {κ : ℝ} (hκ : 0 < κ) (hf : ContDiff ℝ 2 f)
    (hm : ∀ k z, z ∈ segment ℝ (x k) (x k + s k) → DifferentiableAt ℝ (m k) z)
    (hDm : ∀ k z, z ∈ segment ℝ (x k) (x k + s k) →
      DifferentiableAt ℝ (fderiv ℝ (m k)) z)
    (hval : ∀ k, f (x k) = m k (x k))
    (hgrad : ∀ k, fderiv ℝ f (x k) = fderiv ℝ (m k) (x k))
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop (𝓝 0))
    (hagree : ModelHessianAgreement f m x)
    (hFvar : HessianVariationVanishes (fun _ ↦ f) (x ∘ j) (s ∘ j))
    (hMvar : HessianVariationVanishes (m ∘ j) (x ∘ j) (s ∘ j))
    (hdec : ∀ᶠ i in atTop, 0 < κ * ‖s (j i)‖ ^ 2 ∧
      κ * ‖s (j i)‖ ^ 2 ≤ m (j i) (x (j i)) - m (j i) (x (j i) + s (j i))) :
    ∀ᶠ i in atTop, P.η₂ ≤ btrRatio f (m (j i)) (x (j i)) (s (j i)) := by
  let δ := κ * (1 - P.η₂) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity [sub_pos.mpr P.eta₂_lt_one]
  have hc := ((hagree hcrit).comp hj).eventually (gt_mem_nhds hδ)
  filter_upwards [hFvar δ hδ, hMvar δ hδ, hc, hdec] with i hF hM hc hi
  let k := j i
  let Hf := fderiv ℝ (fderiv ℝ f)
  let Hm := fderiv ℝ (fderiv ℝ (m k))
  have hB (z : E) (hz : z ∈ segment ℝ (x k) (x k + s k)) :
      ‖Hf z - Hm z‖ ≤ 3 * δ := by
    rw [segment_eq_image] at hz
    rcases hz with ⟨t, ht, rfl⟩
    have heq : (1 - t) • x k + t • (x k + s k) = x k + t • s k := by
      rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
    dsimp only
    rw [heq]
    have hEq :
        Hf (x k + t • s k) - Hm (x k + t • s k) =
          (Hf (x k + t • s k) - Hf (x k)) + (Hf (x k) - Hm (x k)) -
            (Hm (x k + t • s k) - Hm (x k)) := by abel
    rw [hEq]
    have h₁ : ‖Hf (x k + t • s k) - Hf (x k)‖ ≤ δ := hF t ht
    have h₂ : ‖Hf (x k) - Hm (x k)‖ ≤ δ := le_of_lt hc
    have h₃ : ‖Hm (x k + t • s k) - Hm (x k)‖ ≤ δ := hM t ht
    have hb := norm_sub_le
      (Hf (x k + t • s k) - Hf (x k) + (Hf (x k) - Hm (x k)))
      (Hm (x k + t • s k) - Hm (x k))
    linarith only [hb, norm_add_le (Hf (x k + t • s k) - Hf (x k))
      (Hf (x k) - Hm (x k)), h₁, h₂, h₃]
  have he := abs_model_error_le hf (hval k) (hgrad k) (hm k) (hDm k) hB
  have hp := hi.1.trans_le hi.2
  have hcoef : (1 / 2 : ℝ) * (3 * δ) ≤ (1 - P.η₂) * κ := by
    dsimp [δ]
    nlinarith only [mul_nonneg hκ.le (sub_nonneg.mpr P.eta₂_lt_one.le)]
  have herr : |f (x k + s k) - m k (x k + s k)| ≤
      (1 - P.η₂) * (m k (x k) - m k (x k + s k)) := calc
    _ ≤ (1 / 2 : ℝ) * (3 * δ) * ‖s k‖ ^ 2 := he
    _ ≤ ((1 - P.η₂) * κ) * ‖s k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ = (1 - P.η₂) * (κ * ‖s k‖ ^ 2) := mul_assoc ..
    _ ≤ _ := mul_le_mul_of_nonneg_left hi.2 (sub_nonneg.mpr P.eta₂_lt_one.le)
  have hfit : f (x k) - (m k (x k) - m k (x k + s k)) = m k (x k + s k) := by
    rw [hval k, sub_sub_cancel]
  have h := Optimization.le_reductionRatio_of_abs_sub_le
    (f := f) (x := x k) (s := s k) hp (by rwa [hfit])
  simpa [btrRatio] using h

/-- Corrected Lemma 6.5.4. Once the ratio estimate is valid on the full
sequence, radius updates give a positive lower bound, including the finite prefix. -/
theorem lemma_6_5_4 {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    {κ : ℝ} (hκ : 0 < κ) (hf : ContDiff ℝ 2 f)
    (hm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hgrad : ∀ k, fderiv ℝ f (run.x k) = fderiv ℝ (run.model k) (run.x k))
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    (hagree : ModelHessianAgreement f run.model run.x)
    (hFvar : HessianVariationVanishes (fun _ ↦ f) run.x run.s)
    (hMvar : HessianVariationVanishes run.model run.x run.s)
    (hdec : ∀ᶠ k in atTop, 0 < κ * ‖run.s k‖ ^ 2 ∧
      κ * ‖run.s k‖ ^ 2 ≤ run.model k (run.x k) - run.model k (run.x k + run.s k)) :
    (∀ᶠ k in atTop, k ∈ run.verySuccessful) ∧ ∃ δ > 0, ∀ k, δ ≤ run.Δ k := by
  have hv : ∀ᶠ k in atTop, k ∈ run.verySuccessful :=
    lemma_6_5_3 (P := P) (j := id) tendsto_id hκ hf hm hDm hval hgrad hcrit hagree hFvar hMvar hdec
  obtain ⟨N, hN⟩ := eventually_atTop.mp hv
  have hprefix (n : ℕ) : ∃ δ > 0, ∀ k ≤ n, δ ≤ run.Δ k := by
    induction n with
    | zero =>
      exact ⟨run.Δ 0, run.delta_pos 0, fun k hk ↦ by simp [Nat.eq_zero_of_le_zero hk]⟩
    | succ n ih =>
      obtain ⟨δ, hδ, hδn⟩ := ih
      refine ⟨min δ (run.Δ (n + 1)), lt_min hδ (run.delta_pos _), fun k hk ↦ ?_⟩
      rcases Nat.lt_or_eq_of_le hk with h | rfl
      · exact (min_le_left _ _).trans (hδn k (Nat.le_of_lt_succ h))
      · exact min_le_right _ _
  obtain ⟨δ, hδ, hδN⟩ := hprefix N
  refine ⟨hv, δ, hδ, fun k ↦ ?_⟩
  induction k with
  | zero => exact hδN 0 (Nat.zero_le _)
  | succ k ih =>
    by_cases hk : N ≤ k
    · exact ih.trans ((run.radius_update k).very_successful (hN k hk))
    · exact hδN (k + 1) (Nat.succ_le_of_lt (lt_of_not_ge hk))

private theorem norm_fderiv_lower_bound {f : E → ℝ} {x₀ : E}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x₀) (hzero : fderiv ℝ f x₀ = 0)
    {σ : ℝ} (hσ : 0 < σ) (hH : ∀ v, σ * ‖v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x₀ v‖) :
    ∃ R > 0, ∀ x, ‖x - x₀‖ < R → (σ / 2) * ‖x - x₀‖ ≤ ‖fderiv ℝ f x‖ := by
  have h := Asymptotics.isLittleO_iff.mp hf.hasFDerivAt.isLittleO (half_pos hσ)
  obtain ⟨R, hR, hRsub⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨R, hR, fun x hx ↦ ?_⟩
  have hx' := hRsub x (show x ∈ Metric.ball x₀ R by simpa [dist_eq_norm] using hx)
  rw [hzero, sub_zero] at hx'
  have ht := norm_sub_le (fderiv ℝ f x)
    (fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x₀ (x - x₀))
  rw [sub_sub_cancel] at ht
  linarith only [ht, hx', hH (x - x₀)]

omit [NormedSpace ℝ E] in
private theorem tendsto_of_local_step_bound {x : ℕ → E} {x₀ : E} {u : ℕ → ℝ}
    {R C c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hu : Tendsto u atTop (𝓝 0))
    {j : ℕ → ℕ} (hj : Tendsto j atTop atTop) (hx : Tendsto (x ∘ j) atTop (𝓝 x₀))
    (hlower : ∀ k, ‖x k - x₀‖ < R → c * ‖x k - x₀‖ ≤ u k)
    (hstep : ∀ᶠ k in atTop, ‖x k - x₀‖ < R → ‖x (k + 1) - x k‖ ≤ C * u k) :
    Tendsto x atTop (𝓝 x₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let r := min (R / 2) ε
  have hr : 0 < r := lt_min (half_pos hR) hε
  have hrR : r ≤ R / 2 := min_le_left _ _
  have ht : ∀ᶠ k in atTop, C * u k < R / 2 :=
    (by simpa using (tendsto_const_nhds (x := C)).mul hu : Tendsto (C * u ·) atTop (𝓝 0)).eventually
      (gt_mem_nhds (half_pos hR))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hstep.and (ht.and (hu.eventually (gt_mem_nhds (mul_pos hc hr)))))
  have hentry := (hx.eventually (Metric.ball_mem_nhds x₀ hr)).and
    (hj.eventually (eventually_ge_atTop N))
  obtain ⟨i, hi, hiN⟩ := hentry.exists
  have hstart : ‖x (j i) - x₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hi
  have hind (d : ℕ) : ‖x (j i + d) - x₀‖ < r := by
    induction d with
    | zero => simpa using hstart
    | succ d ih =>
      let k := j i + d
      have hkN : N ≤ k := hiN.trans (Nat.le_add_right _ _)
      have hkR : ‖x k - x₀‖ < R := ih.trans_le (hrR.trans (by linarith))
      have hs := ((hN k hkN).1 hkR).trans_lt (hN k hkN).2.1
      have htri := norm_add_le (x (k + 1) - x k) (x k - x₀)
      rw [sub_add_sub_cancel] at htri
      have hnext : ‖x (k + 1) - x₀‖ < R := by linarith only [htri, hs, ih, hrR]
      have hbound := (hlower (k + 1) hnext).trans_lt
        (hN (k + 1) (hkN.trans (Nat.le_succ _))).2.2
      exact lt_of_mul_lt_mul_left hbound hc.le
  refine ⟨j i, fun k hk ↦ ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [dist_eq_norm]
  exact (hind d).trans_le (min_le_right _ _)

private theorem step_norm_le_of_model_curvature {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    {k : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hm : ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k), DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k),
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hgrad : fderiv ℝ f (run.x k) = fderiv ℝ (run.model k) (run.x k))
    (hcurv : ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k), μ * ‖run.s k‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (run.model k)) z (run.s k) (run.s k)) :
    ‖run.s k‖ ≤ 2 / μ * ‖fderiv ℝ f (run.x k)‖ := by
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      run.x k + t • run.s k ∈ segment ℝ (run.x k) (run.x k + run.s k) := by
    simpa only [add_sub_cancel_left] using
      (convex_segment (𝕜 := ℝ) (run.x k) (run.x k + run.s k)).add_smul_sub_mem
        (left_mem_segment ℝ (run.x k) _) (right_mem_segment ℝ (run.x k) _) ht
  rw [hgrad]
  exact lemma_6_5_1 hμ (fun t ht ↦ hm _ (hseg t ht)) (fun t ht ↦ hDm _ (hseg t ht))
    (fun t ht ↦ hcurv _ (hseg t ht)) (sub_nonneg.mp (run.predicted_pos k).le)

/-- Theorem 6.5.2. A subsequence converges to a first-order point with a nonsingular
Hessian. The lower bound on the Hessian as a linear map is the finite-dimensional
form of nonsingularity. Uniform local model convexity need only hold along the
trial steps. The gradient limit is supplied by Theorem 6.4.6. -/
theorem theorem_6_5_2 {P : BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop} (run : BTRRun f P sufficient)
    {x₀ : E} {j : ℕ → ℕ} (hj : Tendsto j atTop atTop)
    (hx : Tendsto (run.x ∘ j) atTop (𝓝 x₀)) (hf : ContDiff ℝ 2 f)
    (hzero : fderiv ℝ f x₀ = 0)
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    {σ R μ : ℝ} (hσ : 0 < σ) (hR : 0 < R) (hμ : 0 < μ)
    (hH : ∀ v, σ * ‖v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x₀ v‖)
    (hm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hgrad : ∀ k, fderiv ℝ f (run.x k) = fderiv ℝ (run.model k) (run.x k))
    (hcurv : ∀ᶠ k in atTop, ‖run.x k - x₀‖ < R →
      ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k), μ * ‖run.s k‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (run.model k)) z (run.s k) (run.s k)) :
    Tendsto run.x atTop (𝓝 x₀) := by
  have hd := (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
    (by norm_num) x₀
  obtain ⟨r, hr, hlow⟩ := norm_fderiv_lower_bound hd hzero hσ hH
  refine tendsto_of_local_step_bound (C := 2 / μ) (lt_min hR hr) (half_pos hσ)
    hcrit hj hx (fun k hk ↦ hlow _ (hk.trans_le (min_le_right _ _))) ?_
  filter_upwards [hcurv] with k hk hnear
  have hb := step_norm_le_of_model_curvature run hμ (hm k) (hDm k) (hgrad k)
    (hk (hnear.trans_le (min_le_left _ _)))
  by_cases hs : k ∈ run.successful
  · rw [run.iterate_update, Optimization.acceptStep_of_le hs, add_sub_cancel_left]
    exact hb
  · rw [run.iterate_eq_of_unsuccessful hs, sub_self, norm_zero]
    exact mul_nonneg (div_nonneg (by norm_num) hμ.le) (norm_nonneg _)

private theorem hessianVariationVanishes_of_tendsto {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {x s : ℕ → E} {x₀ : E} (hx : Tendsto x atTop (𝓝 x₀)) (hs : Tendsto s atTop (𝓝 0)) :
    HessianVariationVanishes (fun _ ↦ f) x s := by
  intro ε hε
  let H := fderiv ℝ (fderiv ℝ f)
  have hH : ContinuousAt H x₀ :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).fderiv_right
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuous.continuousAt
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hH (ε / 2) (half_pos hε)
  filter_upwards [hx.eventually (Metric.ball_mem_nhds x₀ (half_pos hδ)),
    hs.eventually (Metric.ball_mem_nhds 0 (half_pos hδ))] with k hxk hsk t ht
  have hxk' : ‖x k - x₀‖ < δ / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hxk
  have hsk' : ‖s k‖ < δ / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hsk
  have hts : ‖t • s k‖ ≤ ‖s k‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hseg : dist (x k + t • s k) x₀ < δ := by
    rw [dist_eq_norm, add_comm (x k), add_sub_assoc]
    linarith only [norm_add_le (t • s k) (x k - x₀), hts, hxk', hsk']
  have h₁ := hd hseg
  have h₂ := hd (show dist (x k) x₀ < δ by rw [dist_eq_norm]; linarith)
  rw [dist_eq_norm] at h₁ h₂
  have hb := norm_sub_le (H (x k + t • s k) - H x₀) (H (x k) - H x₀)
  rw [sub_sub_sub_cancel_right] at hb
  exact hb.trans (by linarith)

/-- Corrected Theorem 6.5.5. The local model curvature condition keeps trial
steps near a positive-definite limit once the iterates enter its neighborhood.
Center Hessian agreement alone does not control the models on whole trial
segments. The uniform model variation condition supplies the remaining
hypothesis of the ratio estimate once the steps vanish. -/
theorem theorem_6_5_5 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {P : BTRParams} {f : F → ℝ}
    {sufficient : ℕ → (F → ℝ) → F → F → Prop} (run : BTRRun f P sufficient)
    {x₀ : F} {j : ℕ → ℕ} (hj : Tendsto j atTop atTop)
    (hx : Tendsto (run.x ∘ j) atTop (𝓝 x₀)) (hf : ContDiff ℝ 2 f)
    (hzero : fderiv ℝ f x₀ = 0)
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0))
    {σ R μ K B κ : ℝ} (hσ : 0 < σ) (hR : 0 < R) (hμ : 0 < μ)
    (hK : 0 < K) (hB : 0 < B) (hκ : 0 < κ)
    (hH : ∀ v, σ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x₀ v v)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (β : ℕ → ℝ) (hβ : ∀ k, 0 < β k) (hβB : ∀ k, β k ≤ B)
    (hm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k z, z ∈ segment ℝ (run.x k) (run.x k + run.s k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hgrad : ∀ k, fderiv ℝ f (run.x k) = fderiv ℝ (run.model k) (run.x k))
    (hagree : ModelHessianAgreement f run.model run.x)
    (hcurv : ∀ᶠ k in atTop, ‖run.x k - x₀‖ < R →
      ∀ z ∈ segment ℝ (run.x k) (run.x k + run.s k), μ * ‖run.s k‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (run.model k)) z (run.s k) (run.s k))
    (hMvar : Tendsto run.s atTop (𝓝 0) → HessianVariationVanishes run.model run.x run.s)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ) :
    Tendsto run.x atTop (𝓝 x₀) ∧ (∀ᶠ k in atTop, k ∈ run.verySuccessful) ∧
      ∃ δ > 0, ∀ k, δ ≤ run.Δ k := by
  have hlower (v : F) : σ * ‖v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x₀ v‖ := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hop := (fderiv ℝ (fderiv ℝ f) x₀ v).le_opNorm v
    rw [Real.norm_eq_abs] at hop
    have hb := (hH v).trans ((le_abs_self _).trans hop)
    exact le_of_mul_le_mul_right (by simpa [pow_two, mul_assoc] using hb) (norm_pos_iff.mpr hv)
  have hconv := theorem_6_5_2 run hj hx hf hzero hcrit hσ hR hμ hlower
    hm hDm hgrad hcurv
  have hstep : ∀ᶠ k in atTop, ‖run.s k‖ ≤ 2 / μ * ‖fderiv ℝ f (run.x k)‖ := by
    filter_upwards [hcurv, hconv.eventually (Metric.ball_mem_nhds x₀ hR)] with k hk hnear
    exact step_norm_le_of_model_curvature run hμ (hm k) (hDm k) (hgrad k)
      (hk (by simpa [Metric.mem_ball, dist_eq_norm] using hnear))
  have ht : Tendsto (fun k ↦ 2 / μ * ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 2 / μ)).mul hcrit
  have hsnorm : Tendsto (fun k ↦ ‖run.s k‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ ↦ norm_nonneg _) hstep
  have hs : Tendsto run.s atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hsnorm
  let a := μ / 2
  let b := min (a / B) (1 / K)
  have ha : 0 < a := half_pos hμ
  have hb : 0 < b := lt_min (div_pos ha hB) (div_pos zero_lt_one hK)
  have hq : ∀ᶠ k in atTop, 0 < (κ * a * b) * ‖run.s k‖ ^ 2 ∧
      (κ * a * b) * ‖run.s k‖ ^ 2 ≤
        run.model k (run.x k) - run.model k (run.x k + run.s k) := by
    filter_upwards [hstep] with k hk
    let u := ‖run.s k‖
    let g := ‖gradient f (run.x k)‖
    have hgnorm : g = ‖fderiv ℝ f (run.x k)‖ := by
      unfold g gradient
      exact LinearIsometryEquiv.norm_map _ _
    have hgu : a * u ≤ g := by
      rw [hgnorm]
      change u ≤ 2 / μ * ‖fderiv ℝ f (run.x k)‖ at hk
      rw [div_mul_eq_mul_div] at hk
      dsimp [a]
      linarith only [(le_div_iff₀ hμ).mp hk]
    have hfeas : run.p k (run.s k) ≤ run.Δ k := by
      have h := run.feasible k
      simpa [trustRegion] using h
    have hΔ : u / K ≤ run.Δ k :=
      (div_le_iff₀ hK).mpr ((hnorm k (run.s k)).trans
        (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hfeas hK.le))
    have hmin : b * u ≤ min (g / β k) (run.Δ k) := by
      refine le_min ?_ ?_
      · calc
          _ ≤ (a / B) * u := mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
          _ = (a * u) / B := by ring
          _ ≤ g / β k := div_le_div₀ (norm_nonneg _) hgu (hβ k) (hβB k)
      · exact (mul_le_mul_of_nonneg_right (min_le_right (a / B) (1 / K))
          (norm_nonneg _)).trans (by simpa [one_div, div_eq_mul_inv, mul_comm] using hΔ)
    have hu : 0 < u := by
      apply norm_pos_iff.mpr
      intro hz
      have hp := run.predicted_pos k
      simp [hz] at hp
    refine ⟨mul_pos (mul_pos (mul_pos hκ ha) hb) (pow_pos hu _), ?_⟩
    calc
      _ = (κ * (a * u)) * (b * u) := by ring
      _ ≤ (κ * g) * min (g / β k) (run.Δ k) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hgu hκ.le) hmin
          (mul_nonneg hb.le hu.le) (mul_nonneg hκ.le (norm_nonneg _))
      _ ≤ _ := (hdec k).2
  exact ⟨hconv, lemma_6_5_4 run (mul_pos (mul_pos hκ ha) hb) hf hm hDm hval hgrad hcrit
    hagree (hessianVariationVanishes_of_tendsto hf hconv hs) (hMvar hs) hq⟩

end ConnGouldToint.Chapter06
