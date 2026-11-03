import Numlib.Optimization.Optimality.Clarke
import Numlib.Optimization.ModelBased.ProjectedPath
import Numlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Basic real analysis

Taylor and mean-value formulas in Section 3.1 of [conn2000trust].
The derivative applied to the step represents the gradient pairing or Jacobian action.
-/

open Set Filter Topology

namespace ConnGouldToint.Chapter03

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 3.1.1.** Along a segment, the difference in the values of a scalar function
equals its directional derivative at an intermediate point. -/
theorem theorem_3_1_1 {S : Set E} (hS : IsOpen S) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f S)
    {x s : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S) :
    ∃ t ∈ Icc (0 : ℝ) 1, f (x + s) = f x + fderiv ℝ f (x + t • s) s := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => f (x + u • s)) (fderiv ℝ f (x + t • s) s) t :=
    fun t ht => DifferentiableAt.hasDerivAt_comp_add_smul
      ((hf.contDiffAt (hS.mem_nhds (hseg t ht))).differentiableAt (by norm_num))
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope
    (fun u : ℝ => f (x + u • s)) (by norm_num : (0 : ℝ) < 1)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (Ioo_subset_Icc_self hu)).differentiableAt.differentiableWithinAt)
  refine ⟨t, Ioo_subset_Icc_self ht, ?_⟩
  rw [(hd t (Ioo_subset_Icc_self ht)).deriv] at he
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at he
  linarith

/-- **Theorem 3.1.2.** The second-order Lagrange remainder equals half the Hessian
quadratic form evaluated at an intermediate point of the segment. -/
theorem theorem_3_1_2 {S : Set E} (hS : IsOpen S) {f : E → ℝ} (hf : ContDiffOn ℝ 2 f S)
    {x s : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S) :
    ∃ t ∈ Icc (0 : ℝ) 1, f (x + s) = f x + fderiv ℝ f x s +
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (x + t • s) s s := by
  let g : ℝ → ℝ := fun t => f (x + t • s)
  let U : Set ℝ := (fun t : ℝ => x + t • s) ⁻¹' S
  have hU : IsOpen U := hS.preimage (by fun_prop)
  have hsub : Icc (0 : ℝ) 1 ⊆ U := hseg
  have hg : ContDiffOn ℝ 2 g U := hf.comp (by fun_prop) (fun _ h => h)
  have hd : ∀ t ∈ U, deriv g t = fderiv ℝ f (x + t • s) s :=
    fun t ht => (DifferentiableAt.hasDerivAt_comp_add_smul
      ((hf.contDiffAt (hS.mem_nhds ht)).differentiableAt (by norm_num))).deriv
  have hdd : ∀ t ∈ U, iteratedDeriv 2 g t = fderiv ℝ (fderiv ℝ f) (x + t • s) s s := by
    intro t ht
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have he : deriv g =ᶠ[nhds t] fun u : ℝ => fderiv ℝ f (x + u • s) s :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds ht, hd⟩
    rw [he.deriv_eq]
    have hF : ContDiffOn ℝ 1 (fderiv ℝ f) S := hf.fderiv_of_isOpen hS (by norm_num)
    have h := (DifferentiableAt.hasDerivAt_comp_add_smul
      ((hF.contDiffAt (hS.mem_nhds ht)).differentiableAt (by norm_num))).clm_apply
        (hasDerivAt_const t s)
    simpa using h.deriv
  have hne : (0 : ℝ) ≠ 1 := zero_ne_one
  have hsub' : uIcc (0 : ℝ) 1 ⊆ U := by simpa [uIcc_of_le zero_le_one] using hsub
  obtain ⟨t, ht, he⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul
    (f := g) (n := 1) hne (by exact hg.mono hsub')
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    exact Ioo_subset_Icc_self (by simpa only [uIoo_of_le zero_le_one] using ht)
  rw [taylorWithinEval_eq_sum_of_contDiffAt hne
    ((hg.contDiffAt (hU.mem_nhds (hsub (left_mem_Icc.2 zero_le_one)))).of_le (by norm_num)),
    hdd t (hsub ht')] at he
  refine ⟨t, ht', ?_⟩
  have hd0 := hd 0 (hsub (left_mem_Icc.2 zero_le_one))
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at he
  rw [hd0] at he
  simp only [g, zero_smul, one_smul, add_zero] at he
  linarith

/-- **Theorem 3.1.3 (integral mean value theorem).** The integral of the derivative along
a segment recovers the increment of a vector-valued function. -/
theorem theorem_3_1_3 [CompleteSpace F] {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : ContDiffOn ℝ 1 f S) {x s : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S) :
    f (x + s) = f x + ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • s) s := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => f (x + u • s)) (fderiv ℝ f (x + t • s) s) t :=
    fun t ht => DifferentiableAt.hasDerivAt_comp_add_smul
      ((hf.contDiffAt (hS.mem_nhds (hseg t ht))).differentiableAt (by norm_num))
  have hc : ContinuousOn (fderiv ℝ f) S :=
    hf.continuousOn_fderiv_of_isOpen hS (by norm_num)
  have hi : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (x + t • s) s) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le zero_le_one]
      exact (hc.comp (by fun_prop) hseg).clm_apply continuousOn_const)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => f (x + u • s)) (by rwa [uIcc_of_le zero_le_one]) hi
  rw [he]
  simp [add_comm (f x)]

/-- **Theorem 3.1.4.** A derivative that is Lipschitz relative to the expansion point
gives a quadratic remainder for a real-valued function. The derivative is measured in
the dual norm of the step norm. -/
theorem theorem_3_1_4 {S : Set E} (hS : IsOpen S) {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f S) {x s : E} {γ : ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ γ * ‖z - x‖) :
    |f (x + s) - (f x + fderiv ℝ f x s)| ≤ (1 / 2 : ℝ) * γ * ‖s‖ ^ 2 := by
  simpa only [Real.norm_eq_abs] using norm_sub_firstOrder_le_of_lipschitzAt_segment hS hf hseg hlip

/-- **Theorem 3.1.5.** A Hessian that is Lipschitz relative to the expansion point
gives a cubic remainder for the second-order Taylor model. -/
theorem theorem_3_1_5 {S : Set E} (hS : IsOpen S) {f : E → ℝ}
    (hf : ContDiffOn ℝ 2 f S) {x s : E} {γ : ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) x‖ ≤ γ * ‖z - x‖) :
    |f (x + s) - (f x + fderiv ℝ f x s + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x s s)| ≤
      (1 / 6 : ℝ) * γ * ‖s‖ ^ 3 :=
  abs_sub_secondOrder_le_of_lipschitzAt_segment hS hf hseg hlip

/-- **Theorem 3.1.6.** A Jacobian that is Lipschitz relative to the expansion point
gives a quadratic remainder for a vector-valued function. -/
theorem theorem_3_1_6 {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : ContDiffOn ℝ 1 f S) {x s : E} {γ : ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ γ * ‖z - x‖) :
    ‖f (x + s) - (f x + fderiv ℝ f x s)‖ ≤ (1 / 2 : ℝ) * γ * ‖s‖ ^ 2 :=
  norm_sub_firstOrder_le_of_lipschitzAt_segment hS hf hseg hlip

open Optimization ConvexAnalysis in
/-- Equation (3.1.4). The Clarke directional derivative is the maximum of the
pairing with a Clarke subgradient. Local Lipschitz continuity ensures the
support identity and compactness supplies attainment in finite dimension. -/
theorem clarkeDerivative_isGreatest {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {f : V → ℝ} {x : V}
    {U : Set V} {L : NNReal} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d : V) :
    IsGreatest ((fun g : V ↦ inner ℝ g d) '' Optimization.clarkeSubgradient f x)
      (Optimization.clarkeDerivative f x d) := by
  have hs := hasClarkeSupport_of_lipschitzOnWith hU hL
  have hc := isCompact_clarkeSubgradient hU hL
  have hcont : Continuous (fun g : V ↦ inner ℝ g d) :=
    continuous_id.inner continuous_const
  obtain ⟨g, hg, hm⟩ := hc.exists_isMaxOn hs.nonempty hcont.continuousOn
  have hu (z : V) (hz : z ∈ clarkeSubgradient f x) :
      inner ℝ z d ≤ clarkeDerivative f x d := hz d
  have hmax : clarkeDerivative f x d ≤ inner ℝ g d := by
    apply EReal.coe_le_coe_iff.mp
    rw [← hs d]
    apply supportFn_le_coe_iff.mpr
    intro z hz
    simpa only [innerₗ_apply_apply] using isMaxOn_iff.mp hm z hz
  refine ⟨⟨g, hg, le_antisymm (hu g hg) hmax⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hu z hz

section Moreau

open scoped RealInnerProductSpace
open ConvexAnalysis Optimization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Moreau's normal–tangent decomposition (3.1.7), with orthogonality
of the two projection components. -/
theorem moreau_normal_tangent (C : Set V) (x v : V) :
    let n := bestApprox (normalDirections C x) v
    let t := bestApprox (tangentDirections C x) v
    v = t + n ∧ ⟪t, n⟫ = 0 := by
  let N := normalDirections C x
  let T := tangentDirections C x
  let n := bestApprox N v
  let d := v - n
  have hN : N = polarCone (innerₗ V) ((fun y ↦ y - x) '' C) := by
    ext u
    change u ∈ normalDirections C x ↔ _
    rw [mem_normalDirections, mem_polarCone]
    simp only [Set.forall_mem_image, innerₗ_apply_apply, real_inner_comm]
  have hn₀ : (0 : V) ∈ N := hN ▸ zero_mem_polarCone _ _
  have hn := (bestApprox_eq_iff ⟨0, hn₀⟩ (hN ▸ isClosed_polarCone)
    (hN ▸ convex_polarCone _ _)).1 (rfl : bestApprox N v = n)
  have hadd {u w : V} (hu : u ∈ N) (hw : w ∈ N) : u + w ∈ N := by
    apply mem_normalDirections.mpr
    intro y hy
    rw [inner_add_left]
    exact add_nonpos (mem_normalDirections.mp hu y hy) (mem_normalDirections.mp hw y hy)
  have hd₀ := hn.2 0 hn₀
  have hd₂ := hn.2 (n + n) (hadd hn.1 hn.1)
  have horth : ⟪d, n⟫ = 0 := by
    change ⟪d, 0 - n⟫ ≤ 0 at hd₀
    change ⟪d, n + n - n⟫ ≤ 0 at hd₂
    simp only [zero_sub, inner_neg_right, add_sub_cancel_right] at hd₀ hd₂
    linarith
  have hd : d ∈ T := by
    apply mem_polarCone.mpr
    intro u hu
    have h := hn.2 (n + u) (hadd hn.1 hu)
    change ⟪d, n + u - n⟫ ≤ 0 at h
    simpa only [add_sub_cancel_left, innerₗ_apply_apply, real_inner_comm] using h
  have ht : bestApprox T v = d := by
    apply (bestApprox_eq_iff (polarCone_nonempty _ _) isClosed_polarCone
      (convex_polarCone _ _)).mpr
    refine ⟨hd, fun u hu ↦ ?_⟩
    have hp := (mem_polarCone.mp hu) n hn.1
    have he : v - d = n := by simp [d]
    have horth' : ⟪n, d⟫ = 0 := (real_inner_comm _ _).trans horth
    rw [he, inner_sub_right, horth', sub_zero]
    exact hp
  change v = bestApprox T v + n ∧ ⟪bestApprox T v, n⟫ = 0
  exact ⟨by rw [ht]; simp [d], ht.symm ▸ horth⟩

end Moreau

end ConnGouldToint.Chapter03
