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

end ConnGouldToint.Chapter06
