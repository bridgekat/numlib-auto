import Numlib.Optimization.Descent
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Higher-order local optimality conditions

Necessary second- and third-order conditions are proved by restricting the objective to lines.
For a convex feasible set, a radial displacement gives a feasible one-sided ray. At a local
minimum the second directional derivative is nonnegative when the first vanishes, and the
third is nonnegative when the first two vanish. For an unconstrained minimum, applying the
third-order condition to opposite directions gives equality.

The scalar lemmas use explicit derivative data and only require the last derivative at the
base point. The finite-dimensional strict sufficiency theorem converts pointwise positivity
of the second derivative into a uniform coercivity bound and delegates to
`Descent.isLocalMin_of_coercive_second`.
-/

open Filter Topology Metric Set

namespace Descent

/-- A function with strictly negative derivative just to the right of zero is strictly
smaller there than its value at zero. -/
theorem eventually_lt_of_eventually_deriv_neg_right {g g' : ℝ → ℝ}
    (hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (g' t) t)
    (hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), g' t < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < g 0 := by
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hneg.and (hg.filter_mono nhdsWithin_le_nhds))
  have hε0 : 0 < ε := hε
  have hderiv : ∀ t ∈ Icc (0 : ℝ) (ε / 2), HasDerivAt g (g' t) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with heq | hpos
    · subst t; exact hg.self_of_nhds
    · exact (hsub ⟨hpos, by linarith [ht.2]⟩).2
  have hanti : StrictAntiOn g (Icc (0 : ℝ) (ε / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro t ht
      exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t (Ioo_subset_Icc_self ht)).deriv]
      exact (hsub ⟨ht.1, by linarith [ht.2]⟩).1
  apply mem_nhdsGT_iff_exists_Ioo_subset.2
  refine ⟨ε / 2, (show 0 < ε / 2 by positivity), ?_⟩
  intro t ht
  exact hanti (left_mem_Icc.mpr (by positivity)) (Ioo_subset_Icc_self ht) ht.1


/-- The second derivative is nonnegative at a one-sided minimum when the first derivative
vanishes. All derivatives except the final one need only exist near the base point. -/
theorem nonneg_second_of_eventually_min_right {g g' : ℝ → ℝ} {a : ℝ}
    (hmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), g 0 ≤ g t)
    (hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (g' t) t)
    (hg' : HasDerivAt g' a 0) (hzero : g' 0 = 0) : 0 ≤ a := by
  by_contra hn
  have ha : a < 0 := lt_of_not_ge hn
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), g' t < 0 := by
    filter_upwards [eventually_lt_add_mul_of_hasDerivAt_lt hg' ha] with t ht
    simpa [hzero] using ht
  have hlt := eventually_lt_of_eventually_deriv_neg_right hg hneg
  obtain ⟨t, hle, hlt⟩ := (hmin.and hlt).exists
  exact (not_lt_of_ge hle) hlt

/-- If a function has a nonnegative right increment, its third derivative is nonnegative
when its first two derivatives vanish. Derivatives are only required near the base point. -/
theorem nonneg_third_of_eventually_min_right {g g' g'' : ℝ → ℝ} {a : ℝ}
    (hmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), g 0 ≤ g t)
    (hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (g' t) t)
    (hg' : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g' (g'' t) t)
    (hg'' : HasDerivAt g'' a 0) (hzero : g' 0 = 0) (hzero' : g'' 0 = 0) :
    0 ≤ a := by
  by_contra hn
  have ha : a < 0 := lt_of_not_ge hn
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), g'' t < 0 := by
    filter_upwards [eventually_lt_add_mul_of_hasDerivAt_lt hg'' ha] with t ht
    simpa [hzero'] using ht
  have hneg' : ∀ᶠ t in 𝓝[>] (0 : ℝ), g' t < 0 := by
    simpa [hzero] using eventually_lt_of_eventually_deriv_neg_right hg' hneg
  have hlt := eventually_lt_of_eventually_deriv_neg_right hg hneg'
  obtain ⟨t, hle, hlt⟩ := (hmin.and hlt).exists
  exact (not_lt_of_ge hle) hlt


/-- In finite-dimensional inner product spaces, strict positivity of the second derivative
at a stationary point gives a strict local minimum. -/
theorem isLocalMin_of_posDef_second
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiff ℝ 2 f) (hcrit : fderiv ℝ f x = 0)
    (hpos : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x v v) :
    ∃ δ > 0, ∀ y ∈ ball x δ, y ≠ x → f x < f y := by
  let B := fderiv ℝ (fderiv ℝ f) x
  let A := InnerProductSpace.continuousLinearMapOfBilin B
  have hA : (A : E →ₗ[ℝ] E).IsCoercive := by
    apply (LinearMap.isCoercive_iff_forall_pos _).2
    intro v hv
    simpa [A, B] using hpos v hv
  obtain ⟨c, hc, hcB⟩ := hA
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact isLocalMin_of_coercive_second (r := 1) zero_lt_one hc
    (fun y _ => (hf.differentiable (by norm_num) y).hasFDerivAt)
    (fun y _ => (hf'.differentiable (by norm_num) y).hasFDerivAt)
    (hf'.continuous_fderiv (by norm_num)).continuousAt hcrit
    (fun v => by simpa [LinearMap.IsCoerciveWith, A, B] using hcB v)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convex feasible displacement defines a feasible ray near zero, on which a constrained
local minimum remains a one-sided local minimum. -/
theorem eventually_le_on_ray_of_isLocalMinOn {f : E → ℝ} {C : Set E} {x d : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hd : x + d ∈ C) (hmin : IsLocalMinOn f C x) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f x ≤ f (x + t • d) := by
  have hline : Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • d) := by fun_prop
    simpa using hc.tendsto 0
  have htC : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • d ∈ C := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht ht1
    exact hC.add_smul_mem hx hd ⟨le_of_lt ht, le_of_lt ht1⟩
  have htend : Tendsto (fun t : ℝ => x + t • d) (𝓝[>] 0) (𝓝[C] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hline.mono_left nhdsWithin_le_nhds, htC⟩
  exact htend.eventually hmin

/-- Second-order necessity on a radial feasible direction with zero first derivative. -/
theorem nonneg_apply_apply_of_isLocalMinOn {f : E → ℝ} {C : Set E}
    {f' : E → E →L[ℝ] ℝ} {f'' : E →L[ℝ] E →L[ℝ] ℝ} {x d : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hd : x + d ∈ C) (hmin : IsLocalMinOn f C x)
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hf' : HasFDerivAt f' f'' x) (hcrit : f' x d = 0) : 0 ≤ f'' d d := by
  have hline : Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • d) := by fun_prop
    simpa using hc.tendsto 0
  apply nonneg_second_of_eventually_min_right
    (g := fun t : ℝ => f (x + t • d)) (g' := fun t : ℝ => f' (x + t • d) d)
  · simpa using eventually_le_on_ray_of_isLocalMinOn hC hx hd hmin
  · filter_upwards [hline.eventually hf] with t ht
    exact ht.hasLineDerivAt d |>.hasDerivAt_line
  · have hh : HasDerivAt (fun t : ℝ => f' (x + t • d)) (f'' d) 0 := hf'.hasLineDerivAt d
    simpa using hh.clm_apply (hasDerivAt_const (0 : ℝ) d)
  · simpa using hcrit

/-- Third-order necessity on a radial feasible direction with zero first two derivatives. -/
theorem nonneg_third_apply_apply_apply_of_isLocalMinOn
    {f : E → ℝ} {C : Set E} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    {f''' : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {x d : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hd : x + d ∈ C) (hmin : IsLocalMinOn f C x)
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hf' : ∀ᶠ y in 𝓝 x, HasFDerivAt f' (f'' y) y)
    (hf'' : HasFDerivAt f'' f''' x) (hcrit : f' x d = 0) (hcrit' : f'' x d d = 0) :
    0 ≤ f''' d d d := by
  have hline : Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • d) := by fun_prop
    simpa using hc.tendsto 0
  apply nonneg_third_of_eventually_min_right
    (g := fun t : ℝ => f (x + t • d))
    (g' := fun t : ℝ => f' (x + t • d) d)
    (g'' := fun t : ℝ => f'' (x + t • d) d d)
  · simpa using eventually_le_on_ray_of_isLocalMinOn hC hx hd hmin
  · filter_upwards [hline.eventually hf] with t ht
    exact ht.hasLineDerivAt d |>.hasDerivAt_line
  · filter_upwards [hline.eventually hf'] with t ht
    have hh := ht.hasLineDerivAt d |>.hasDerivAt_line
    simpa using hh.clm_apply (hasDerivAt_const t d)
  · have hh : HasDerivAt (fun t : ℝ => f'' (x + t • d)) (f''' d) 0 := hf''.hasLineDerivAt d
    have hh' := hh.clm_apply (hasDerivAt_const (0 : ℝ) d)
    simpa using hh'.clm_apply (hasDerivAt_const (0 : ℝ) d)
  · simpa using hcrit
  · simpa using hcrit'

/-- A third directional derivative vanishes at a local minimum whenever the second
 directional derivative vanishes. Only differentiability in a neighborhood is required. -/
theorem third_apply_apply_apply_eq_zero_of_isLocalMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    {f''' : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hmin : IsLocalMin f x)
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hf' : ∀ᶠ y in 𝓝 x, HasFDerivAt f' (f'' y) y)
    (hf'' : HasFDerivAt f'' f''' x) (v : E) (hv : f'' x v v = 0) :
    f''' v v v = 0 := by
  have hnonneg : ∀ w : E, f'' x w w = 0 → 0 ≤ f''' w w w := by
    intro w hw
    apply nonneg_third_apply_apply_apply_of_isLocalMinOn
      (C := Set.univ) (convex_univ : Convex ℝ (Set.univ : Set E))
      (Set.mem_univ x) (Set.mem_univ (x + w)) (hmin.isLocalMinOn _) hf hf' hf''
    · rw [hmin.hasFDerivAt_eq_zero hf.self_of_nhds]
      rfl
    · exact hw
  have hpos := hnonneg v hv
  have hneg := hnonneg (-v) (by simpa using hv)
  simp only [map_neg, neg_apply, neg_neg] at hneg
  linarith

end Descent
