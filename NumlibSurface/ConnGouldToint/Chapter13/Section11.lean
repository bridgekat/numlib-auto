import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.ConnGouldToint.Chapter06.Section04

/-! # Affine scaling for nonnegative bounds -/

open Filter Set
open scoped Topology

namespace ConnGouldToint.Chapter13

open Chapter06

variable {ι : Type*} [Fintype ι]

/-- The norm of a step in the Dikin ellipsoid centered at `x`. -/
noncomputable def affineScalingPrimalNorm (x s : EuclideanSpace ℝ ι) : ℝ :=
  Real.sqrt (∑ i, (s i / x i) ^ 2)

/-- The dual norm of the gradient in (13.11.3). -/
noncomputable def affineScalingGradientNorm (x g : EuclideanSpace ℝ ι) : ℝ :=
  Real.sqrt (∑ i, (x i * g i) ^ 2)

/-- Algorithm 13.11.1 as a BTR run with Dikin norms, quadratic models,
the second-order decrease test, and an upper radius cap below one. -/
structure AffineScalingRun (f : EuclideanSpace ℝ ι → ℝ) (P : BTRParams) where
  run : BTRRun f P (fun _ _ _ _ ↦ True)
  Δmax : ℝ
  β : ℕ → ℝ
  τ : ℕ → ℝ
  κ : ℝ
  initial_positive : ∀ i, 0 < run.x 0 i
  initial_at_cap : run.Δ 0 = Δmax
  cap_lt_one : Δmax < 1
  radius_le_cap : ∀ k, run.Δ k ≤ Δmax
  primal_norm : ∀ k s, run.p k s = affineScalingPrimalNorm (run.x k) s
  quadratic_model : ∀ k, ∃ H : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι,
    (∀ u v, inner ℝ u (H v) = inner ℝ (H u) v) ∧
    ∀ s, run.model k (run.x k + s) =
      quadraticModel (f (run.x k)) (gradient f (run.x k)) H s
  curvature_pos : ∀ k, 0 < β k
  curvature_nonpositive : ∀ k, τ k ≤ 0
  decrease_constant : κ ∈ Ioo (0 : ℝ) 1
  sufficient_decrease : ∀ k,
    let π := affineScalingGradientNorm (run.x k) (gradient f (run.x k))
    κ * max (π * min (π / β k) (run.Δ k)) (-τ k * min (τ k ^ 2) (run.Δ k ^ 2)) ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k)

/-- The cap below one makes every point in a Dikin ellipsoid strictly feasible. -/
theorem affineScaling_trial_positive {x s : EuclideanSpace ℝ ι}
    (hx : ∀ i, 0 < x i) (hs : affineScalingPrimalNorm x s < 1) :
    ∀ i, 0 < (x + s) i := by
  intro i
  have hsum : 0 ≤ ∑ j, (s j / x j) ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hsingle : (s i / x i) ^ 2 ≤ ∑ j, (s j / x j) ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (s j / x j)) (Finset.mem_univ i)
  have hs' : Real.sqrt (∑ j, (s j / x j) ^ 2) < 1 := hs
  have h : -1 < s i / x i := by
    have hsq := Real.sq_sqrt hsum
    have hp := Real.sqrt_nonneg (∑ j, (s j / x j) ^ 2)
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr hs'.le) hp,
      mul_nonneg (neg_nonneg.mpr (h.trans (by norm_num)))
        (sub_nonneg.mpr h)]
  have hn := (lt_div_iff₀ (hx i)).mp h
  change 0 < x i + s i
  linarith

/-- The radius cap preserves strict feasibility of every accepted iterate. -/
theorem AffineScalingRun.iterate_positive {f : EuclideanSpace ℝ ι → ℝ} {P : BTRParams}
    (r : AffineScalingRun f P) (k : ℕ) : ∀ i, 0 < r.run.x k i := by
  induction k with
  | zero => exact r.initial_positive
  | succ k ih =>
    by_cases hs : k ∈ r.run.successful
    · have hstep : r.run.p k (r.run.s k) ≤ r.run.Δ k := by
        simpa [trustRegion] using r.run.feasible k
      rw [r.primal_norm] at hstep
      rw [r.run.iterate_update, Optimization.acceptStep_of_le hs]
      exact affineScaling_trial_positive ih ((hstep.trans (r.radius_le_cap k)).trans_lt r.cap_lt_one)
    · rw [r.run.iterate_eq_of_unsuccessful hs]
      exact ih

private theorem euclidean_abs_coordinate_le_norm (x : EuclideanSpace ℝ ι) (i : ι) :
    |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖x j‖) (Finset.mem_univ i)

private theorem euclidean_norm_le_scaled {x y : EuclideanSpace ℝ ι} {R : ℝ}
    (hR : 0 ≤ R) (h : ∀ i, |x i| ≤ R * |y i|) : ‖x‖ ≤ R * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_sq hR, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_pow]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hR (abs_nonneg _))).mpr (h i)

private def affineScalingGradientVector (x g : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ x i * g i

private theorem affineScalingGradientNorm_eq (x g : EuclideanSpace ℝ ι) :
    affineScalingGradientNorm x g = ‖affineScalingGradientVector x g‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [affineScalingGradientNorm, affineScalingGradientVector, WithLp.ofLp_toLp,
    Real.norm_eq_abs, sq_abs]

/-- The affine-scaling convergence conclusion (13.11.3) from the uniform
model-error and criticality-variation estimates used in Theorem 13.11.1.
The variation estimate is required only between successive iterates. -/
theorem theorem_13_11_1_of_uniform_estimates {f : EuclideanSpace ℝ ι → ℝ} {P : BTRParams}
    (r : AffineScalingRun f P) {C L : ℝ}
    (hC : ∀ k, r.β k ≤ C) (hL : 0 ≤ L)
    (herr : ∀ k, |f (r.run.x k + r.run.s k) - r.run.model k (r.run.x k + r.run.s k)| ≤
      C * r.run.Δ k ^ 2)
    (hlower : BddBelow (Set.range fun k ↦ f (r.run.x k)))
    (hvariation : ∀ k,
      affineScalingGradientNorm (r.run.x k) (gradient f (r.run.x k)) -
        affineScalingGradientNorm (r.run.x (k + 1)) (gradient f (r.run.x (k + 1))) ≤
      L * r.run.Δ k) :
    Tendsto (fun k ↦ affineScalingGradientNorm (r.run.x k) (gradient f (r.run.x k)))
      atTop (𝓝 0) := by
  let run := r.run
  let value (k : ℕ) := f (run.x k)
  let u (k : ℕ) := affineScalingGradientNorm (run.x k) (gradient f (run.x k))
  have hu (k : ℕ) : 0 ≤ u k := Real.sqrt_nonneg _
  have hCpos : 0 < C := (r.curvature_pos 0).trans_le (hC 0)
  have hval (k : ℕ) : f (run.x k) = run.model k (run.x k) := by
    obtain ⟨H, _, hH⟩ := r.quadratic_model k
    simpa [run, quadraticModel] using (hH 0).symm
  have hdec (k : ℕ) : r.κ * u k * min (u k / r.β k) (run.Δ k) ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k) := by
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) r.decrease_constant.1.le).trans
      (r.sufficient_decrease k)
  have ht : Tendsto value atTop (𝓝 (⨅ k, value k)) :=
    tendsto_atTop_ciInf run.objective_antitone hlower
  have hdiff : Tendsto (fun k ↦ value k - value (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using ht.sub (ht.comp (tendsto_add_atTop_nat 1))
  have htail : Tendsto (fun k ↦ value k - ⨅ j, value j) atTop (𝓝 0) := by
    simpa only [sub_self] using ht.sub_const (⨅ j, value j)
  have hdrop {e : ℝ} (he : 0 < e) {k : ℕ} (hk : k ∈ run.successful) (heuk : e ≤ u k) :
      (P.η₁ * (r.κ * e)) * min (e / C) (run.Δ k) ≤ value k - value (k + 1) := by
    have hm := min_le_min (div_le_div₀ (hu k) heuk (r.curvature_pos k) (hC k))
      (le_refl (run.Δ k))
    have h := (mul_le_mul (mul_le_mul_of_nonneg_left heuk r.decrease_constant.1.le) hm
      (le_min (div_nonneg he.le hCpos.le) (run.delta_pos k).le)
      (mul_nonneg r.decrease_constant.1.le (hu k))).trans (hdec k)
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left h P.eta₁_pos.le).trans (run.objective_drop_of_successful hk)
  have hfreq (e : ℝ) (he : 0 < e) : ∃ᶠ k in atTop, u k < e := by
    by_contra hn
    obtain ⟨N, hN⟩ := eventually_atTop.mp (show ∀ᶠ k in atTop, e ≤ u k from by
      simpa only [Filter.Frequently, not_not, not_lt] using hn)
    let θ := r.κ * e * (1 - P.η₂) / C
    have hθ : 0 < θ := div_pos (mul_pos (mul_pos r.decrease_constant.1 he)
      (sub_pos.mpr P.eta₂_lt_one)) hCpos
    let a := min (run.Δ N) (P.γ₁ * θ)
    have ha : 0 < a := lt_min (run.delta_pos N) (mul_pos P.gamma₁_pos hθ)
    have hrad (k : ℕ) (hk : N ≤ k) : a ≤ run.Δ k := by
      have hr := (run.tail N).delta_lower_bound (θ := θ) ?_ (k - N)
      · simpa [BTRRun.tail, a, Nat.add_sub_of_le hk] using hr
      · intro j hj
        let i := N + j
        have heui := hN i (Nat.le_add_right N j)
        have hs : run.Δ i ≤ r.κ * u i * (1 - P.η₂) / C := hj.trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left heui r.decrease_constant.1.le)
            (sub_nonneg.mpr P.eta₂_lt_one.le)) hCpos.le)
        exact btrRatio_ge_eta₂_of_small_radius_of_decrease (r.curvature_pos i) (hC i)
          (run.delta_pos i) (he.trans_le heui) r.decrease_constant.1 r.decrease_constant.2
          (hval i) (hdec i) (herr i) hs
    let b := (P.η₁ * (r.κ * e)) * min (e / C) a
    have hb : 0 < b := mul_pos (mul_pos P.eta₁_pos (mul_pos r.decrease_constant.1 he))
      (lt_min (div_pos he hCpos) ha)
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hb))
    let I := max N J
    have hfail (k : ℕ) (hk : I ≤ k) : k ∉ run.successful := by
      intro hs
      have hnk : N ≤ k := (le_max_left _ _).trans hk
      have hd := hdrop he hs (hN k hnk)
      have hle := mul_le_mul_of_nonneg_left (min_le_min (le_refl (e / C)) (hrad k hnk))
        (mul_nonneg P.eta₁_pos.le (mul_nonneg r.decrease_constant.1.le he.le))
      exact (hJ k ((le_max_right _ _).trans hk)).not_ge (hle.trans hd)
    have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
    have hshrink (j : ℕ) : run.Δ (I + j) ≤ P.γ₂ ^ j * run.Δ I := by
      induction j with
      | zero => simp
      | succ j ih =>
        have hf := hfail (I + j) (Nat.le_add_right _ _)
        have hr := ((run.radius_update (I + j)).unsuccessful (lt_of_not_ge hf)).2
        rw [show I + (j + 1) = I + j + 1 by omega]
        exact hr.trans ((mul_le_mul_of_nonneg_left ih hγ.le).trans_eq (by rw [pow_succ]; ring))
    have hlim : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * run.Δ I) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const (run.Δ I)
    obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds ha)).exists
    exact hj.not_ge ((hrad (I + j) ((le_max_left _ _).trans (Nat.le_add_right _ _))).trans (hshrink j))
  rw [Metric.tendsto_atTop]
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  let c := P.η₁ * (r.κ * e)
  have hc : 0 < c := mul_pos P.eta₁_pos (mul_pos r.decrease_constant.1 he)
  have hL1 : 0 < L + 1 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hdiff.eventually (gt_mem_nhds (mul_pos hc (div_pos he hCpos))))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (htail.eventually (gt_mem_nhds (div_pos (mul_pos hc he) hL1)))
  have hstep (j : ℕ) (hj : N ≤ j) (huj : e ≤ u j) :
      c * (u j - u (j + 1)) ≤ L * (value j - value (j + 1)) := by
    by_cases hs : j ∈ run.successful
    · have hd := hdrop he hs huj
      have hr : run.Δ j ≤ e / C := by
        by_contra! hn
        rw [min_eq_left hn.le] at hd
        exact (hN j hj).not_ge hd
      rw [min_eq_right hr] at hd
      calc
        _ ≤ c * (L * run.Δ j) := mul_le_mul_of_nonneg_left (hvariation j) hc.le
        _ = L * (c * run.Δ j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hd hL
    · simp only [value, u, run.iterate_eq_of_unsuccessful hs, sub_self, mul_zero, le_refl]
  refine ⟨max N J, fun k hk ↦ ?_⟩
  have hkN := (le_max_left N J).trans hk
  have hkJ := (le_max_right N J).trans hk
  change dist (u k) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu k)]
  by_contra! hhigh
  have hex := frequently_atTop.mp (hfreq e he) k
  let j := Nat.find hex
  have hj : k ≤ j ∧ u j < e := Nat.find_spec hex
  have htel (i : ℕ) (hi : k ≤ i) : i ≤ j →
      c * (u k - u i) ≤ L * (value k - value i) := by
    induction i, hi using Nat.le_induction with
    | base => simp
    | succ i hi ih =>
      intro hij
      have hbelow : i < j := Nat.lt_of_succ_le hij
      have hui : e ≤ u i := le_of_not_gt fun hh ↦ (Nat.find_min hex hbelow) ⟨hi, hh⟩
      linarith only [ih hbelow.le, hstep i (hkN.trans hi) hui]
  have hgap : e < u k - u j := by dsimp [e] at hj ⊢; linarith [hj.2]
  have htailBound : value k - ⨅ i, value i < c * e / (L + 1) := hJ k hkJ
  have hvle : (⨅ i, value i) ≤ value j := ciInf_le hlower j
  have hdval : 0 ≤ value k - value j := sub_nonneg.mpr (run.objective_antitone hj.1)
  have hlast : L * (value k - value j) < c * e := calc
    _ ≤ (L + 1) * (value k - value j) := by gcongr; linarith
    _ ≤ (L + 1) * (value k - ⨅ i, value i) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hvle _) hL1.le
    _ < _ := by
      have hh := (lt_div_iff₀ hL1).mp htailBound
      rwa [mul_comm]
  exact hlast.not_ge ((mul_le_mul_of_nonneg_left hgap.le hc.le).trans (htel j hj.1 le_rfl))

/-- Theorem 13.11.1. Bounded affine-scaling iterates and the uniform
objective and quadratic-model curvature bounds imply convergence of the
scaled gradient. The scaled curvature constants are uniformly bounded,
as in AM.4b. -/
theorem theorem_13_11_1 {f : EuclideanSpace ℝ ι → ℝ} {P : BTRParams}
    (r : AffineScalingRun f P) (hf : ContDiff ℝ 2 f) {R L B Cβ : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hx : ∀ k, ‖r.run.x k‖ ≤ R)
    (hF : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ L)
    (hM : ∀ k, ∃ H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι,
      ‖H‖ ≤ B ∧ ∀ s, r.run.model k (r.run.x k + s) =
        quadraticModel (f (r.run.x k)) (gradient f (r.run.x k)) H.toLinearMap s)
    (hβ : ∀ k, r.β k ≤ Cβ)
    (hlower : BddBelow (Set.range fun k ↦ f (r.run.x k))) :
    Tendsto (fun k ↦ affineScalingGradientNorm (r.run.x k) (gradient f (r.run.x k)))
      atTop (𝓝 0) := by
  let run := r.run
  let g := gradient f
  have hDf := hf.fderiv_right (m := 1) (by norm_num)
  have hD (x y : EuclideanSpace ℝ ι) : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hDf.differentiable (by norm_num) z) (fun z _ ↦ hF z)
      convex_univ (mem_univ y) (mem_univ x)
  have hg (x y : EuclideanSpace ℝ ι) : ‖g x - g y‖ ≤ L * ‖x - y‖ := by
    simpa only [g, gradient, ← map_sub, LinearIsometryEquiv.norm_map] using hD x y
  let G := L * R + ‖g 0‖
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hgB (k : ℕ) : ‖g (run.x k)‖ ≤ G := by
    have hh := (norm_sub_norm_le (g (run.x k)) (g 0)).trans (hg (run.x k) 0)
    rw [sub_zero] at hh
    have hLR := mul_le_mul_of_nonneg_left (hx k) hL
    dsimp [G]
    linarith
  have hstep (k : ℕ) : ‖run.s k‖ ≤ R * run.Δ k := by
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ run.s k i / run.x k i
    have hv : ‖v‖ = affineScalingPrimalNorm (run.x k) (run.s k) := by
      rw [EuclideanSpace.norm_eq]
      simp only [v, affineScalingPrimalNorm, Real.norm_eq_abs, sq_abs]
    have hnv := euclidean_norm_le_scaled (x := run.s k) (y := v) hR (fun i ↦ by
      have hh := (euclidean_abs_coordinate_le_norm (run.x k) i).trans (hx k)
      change |run.s k i| ≤ R * |run.s k i / run.x k i|
      have he : run.s k i = run.x k i * (run.s k i / run.x k i) := by
        rw [mul_div_cancel₀ _ (r.iterate_positive k i).ne']
      calc
        _ = |run.x k i| * |run.s k i / run.x k i| := by rw [← abs_mul, ← he]
        _ ≤ _ := mul_le_mul_of_nonneg_right hh (abs_nonneg _))
    have hrad : run.p k (run.s k) ≤ run.Δ k := by simpa [trustRegion] using run.feasible k
    rw [hv, ← r.primal_norm] at hnv
    exact hnv.trans (mul_le_mul_of_nonneg_left hrad hR)
  have hdist (k : ℕ) : ‖run.x k - run.x (k + 1)‖ ≤ R * run.Δ k := by
    by_cases hs : k ∈ run.successful
    · rw [run.iterate_update, Optimization.acceptStep_of_le hs, sub_add_cancel_left, norm_neg]
      exact hstep k
    · rw [run.iterate_eq_of_unsuccessful hs, sub_self, norm_zero]
      exact mul_nonneg hR (run.delta_pos k).le
  let C := max Cβ (((L + B) / 2) * R ^ 2)
  refine theorem_13_11_1_of_uniform_estimates r (C := C) (L := (R * L + G) * R)
    (fun k ↦ (hβ k).trans (le_max_left _ _)) (by positivity) ?_ hlower ?_
  · intro k
    let x := run.x k
    let s := run.s k
    obtain ⟨H, hH, hm⟩ := hM k
    have hrem := norm_sub_firstOrder_le_of_hessian_bound
      (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ ι)))
      (mem_univ x) (mem_univ (x + s))
      (fun z _ ↦ hf.differentiable (by norm_num) z)
      (fun z _ ↦ hDf.differentiable (by norm_num) z) (fun z _ ↦ hF z)
    rw [Real.norm_eq_abs] at hrem
    have hquad : |inner ℝ s (H s)| ≤ B * ‖s‖ ^ 2 := calc
      _ ≤ ‖s‖ * ‖H s‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖s‖ * (‖H‖ * ‖s‖) := mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _)
      _ = ‖H‖ * ‖s‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hH (sq_nonneg _)
    change |f (x + s) - run.model k (x + s)| ≤ C * run.Δ k ^ 2
    rw [hm, quadraticModel, ← sub_sub, inner_gradient_left]
    refine ((abs_sub _ _).trans ?_)
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hsq := (sq_le_sq₀ (norm_nonneg s) (mul_nonneg hR (run.delta_pos k).le)).mpr (hstep k)
    have hscaled := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (L + B) / 2 by positivity)
    rw [mul_pow] at hscaled
    have hlast := mul_le_mul_of_nonneg_right (le_max_right Cβ (((L + B) / 2) * R ^ 2))
      (sq_nonneg (run.Δ k))
    change |f (x + s) - (f x + fderiv ℝ f x s)| + (1 / 2 : ℝ) * |inner ℝ s (H s)| ≤
      C * run.Δ k ^ 2
    calc
      _ ≤ ((L + B) / 2) * ‖s‖ ^ 2 := by nlinarith only [hrem, hquad]
      _ ≤ ((L + B) / 2 * R ^ 2) * run.Δ k ^ 2 := by simpa only [mul_assoc] using hscaled
      _ ≤ _ := hlast
  · intro k
    let x := run.x k
    let y := run.x (k + 1)
    let v := affineScalingGradientVector x (g x - g y)
    let w := affineScalingGradientVector (x - y) (g y)
    have hsub : affineScalingGradientVector x (g x) - affineScalingGradientVector y (g y) =
        v + w := by
      apply (WithLp.ext_iff 2).mpr
      funext i
      simp only [v, w, affineScalingGradientVector, WithLp.ofLp_add, WithLp.ofLp_sub,
        Pi.add_apply, Pi.sub_apply]
      ring
    have hv : ‖v‖ ≤ R * ‖g x - g y‖ := euclidean_norm_le_scaled hR fun i ↦ by
      change |x i * (g x - g y) i| ≤ _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ((euclidean_abs_coordinate_le_norm x i).trans (hx k))
        (abs_nonneg _)
    have hw : ‖w‖ ≤ G * ‖x - y‖ := euclidean_norm_le_scaled hG fun i ↦ by
      change |(x - y) i * g y i| ≤ _
      rw [mul_comm, abs_mul]
      exact mul_le_mul_of_nonneg_right ((euclidean_abs_coordinate_le_norm (g y) i).trans (hgB (k + 1)))
        (abs_nonneg _)
    simp only [affineScalingGradientNorm_eq]
    calc
      _ ≤ ‖affineScalingGradientVector x (g x) - affineScalingGradientVector y (g y)‖ :=
        norm_sub_norm_le _ _
      _ ≤ R * ‖g x - g y‖ + G * ‖x - y‖ := by rw [hsub]; exact (norm_add_le _ _).trans (add_le_add hv hw)
      _ ≤ (R * L + G) * ‖x - y‖ := by
        have hh := mul_le_mul_of_nonneg_left (hg x y) hR
        nlinarith only [hh]
      _ ≤ (R * L + G) * (R * run.Δ k) := mul_le_mul_of_nonneg_left (hdist k) (by positivity)
      _ = _ := by ring

end ConnGouldToint.Chapter13
