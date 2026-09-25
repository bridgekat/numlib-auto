import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Numlib.Analysis.Calculus.HermiteInterpolation
import Numlib.Analysis.Calculus.RootMultiplicity

/-!
# The Hermite–Genocchi bound for divided differences

For `f` smooth on a convex set of `𝕜 = ℝ` or `ℂ`, the divided difference of `f` at `r + 1` nodes of
the set, repeated or not, is bounded by `M / r!`, where `M` bounds `‖f⁽ʳ⁾‖` on the set
([golub2013matrix] (9.2.1)). Over `ℝ` this is also a consequence of the mean value form
`f[x₀, …, x_r] = f⁽ʳ⁾(ξ)/r!`; over `ℂ` there is no mean value theorem, and the bound comes from
the Hermite–Genocchi formula `f[x₀, …, x_r] = ∫_{Σ_r} f⁽ʳ⁾(∑ tᵢ xᵢ) dt` over the standard simplex,
whose volume is `1/r!`.

## Main results

* `Hermite.divDiff_cons_eq_of_eventuallyEq`: if `f z = f a + (z - a) g z` near the nodes, then
  `f[a, s] = g[s]` — removing one node divides by `z - a`.
* `iteratedDeriv_integral_deriv_comp_segment`: the segment average
  `g z = ∫₀¹ f'(a + t(z - a)) dt`, which satisfies `f z = f a + (z - a) g z`, has
  `g⁽ᵏ⁾(z) = ∫₀¹ tᵏ f⁽ᵏ⁺¹⁾(a + t(z - a)) dt` on an open convex set where `f` is smooth.
* `Hermite.norm_divDiff_le_of_contDiffOn`: the bound for `f` smooth on an open convex set `U`,
  with `M` bounding `‖f⁽ʳ⁾‖` on a convex `Ω ⊆ U` holding the nodes.
* `Hermite.norm_divDiff_le`: the bound for `f` analytic on a neighbourhood of a convex set.

## Implementation notes

The simplex integral is never written down. The proof is by induction on the number of nodes: the
first two results give `f[a, s] = g[s]` and `‖g⁽ʳ⁻¹⁾‖ ≤ M / r` on `Ω`, which is the Hermite–Genocchi
formula unrolled one simplex coordinate at a time. The segment average needs `U` convex; an
analytic `f` is smooth on an open convex neighbourhood of the (compact) convex hull of the nodes,
a thickening of it.
-/

open Polynomial Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff Interval

namespace Hermite

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The remainder of `c + (X - a) p` modulo the nodal polynomial of `a :: s` has, in degree
`card s`, the coefficient that the remainder of `p` modulo the nodal polynomial of `s` has in
degree `card s - 1`. -/
theorem coeff_C_add_X_sub_C_mul_modByMonic (c a : 𝕜) (p : 𝕜[X]) {s : Multiset 𝕜} (hs : s ≠ 0) :
    ((C c + (X - C a) * p) %ₘ nodalMultiset (a ::ₘ s)).coeff (Multiset.card s)
      = (p %ₘ nodalMultiset s).coeff (Multiset.card s - 1) := by
  set N := nodalMultiset s
  set k := Multiset.card s
  set p₀ := p %ₘ N
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
    have := Multiset.card_pos.mpr hs
    omega⟩
  have hp₀ : p₀.degree < k := by
    rw [← degree_nodalMultiset s]
    exact degree_modByMonic_lt _ (monic_nodalMultiset s)
  have hcoeff : ∀ m, k ≤ m → p₀.coeff m = 0 := fun m hm =>
    coeff_eq_zero_of_degree_lt (hp₀.trans_le (by exact_mod_cast hm))
  have hq : ∀ m, (C c + (X - C a) * p₀).coeff (m + 1) = p₀.coeff m - a * p₀.coeff (m + 1) := by
    intro m
    rw [sub_mul, coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C, ite_eq_right (by omega),
      zero_add]
  have hrem : (C c + (X - C a) * p) %ₘ nodalMultiset (a ::ₘ s) = C c + (X - C a) * p₀ := by
    have hdvd : nodalMultiset (a ::ₘ s) ∣ C c + (X - C a) * p - (C c + (X - C a) * p₀) := by
      refine ⟨p /ₘ N, ?_⟩
      have h := modByMonic_add_div p N
      rw [nodalMultiset_cons]
      linear_combination -(X - C a) * h
    rw [modByMonic_eq_of_dvd_sub (monic_nodalMultiset _) hdvd,
      (modByMonic_eq_self_iff (monic_nodalMultiset _)).mpr]
    rw [degree_nodalMultiset, Multiset.card_cons]
    refine (degree_lt_iff_coeff_zero _ _).mpr fun m hm => ?_
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hq, hcoeff m (by omega), hcoeff (m + 1) (by omega), mul_zero, sub_zero]
  rw [hrem, hk', hq, hcoeff (k' + 1) hk'.le, mul_zero, sub_zero, Nat.add_sub_cancel]

variable [DecidableEq 𝕜] [CharZero 𝕜]

/-- **Removing a node divides by `z - a`**: if `f z = f a + (z - a) g z` near each node of
`a :: s`, with `g` smooth enough there, then `f[a, s] = g[s]`. -/
theorem divDiff_cons_eq_of_eventuallyEq {f g : 𝕜 → 𝕜} {a : 𝕜} {s : Multiset 𝕜} (hs : s ≠ 0)
    (hg : ∀ x ∈ a ::ₘ s, ContDiffAt 𝕜 (Multiset.card s) g x)
    (hfg : ∀ x ∈ a ::ₘ s, f =ᶠ[𝓝 x] fun z => f a + (z - a) * g z) :
    divDiff f (a ::ₘ s) = divDiff g s := by
  set p := interpolateJet (a ::ₘ s) (taylorJet g)
  have hp : IsJetInterpolant (a ::ₘ s) (taylorJet g) p := isJetInterpolant_interpolateJet _ _
  have hq : IsJetInterpolant (a ::ₘ s) (taylorJet f) (C (f a) + (X - C a) * p) := by
    refine (isJetInterpolant_congr fun x hx j hj => ?_).mp
      ((isJetInterpolant_taylorJet_polynomial (a ::ₘ s) (C (f a))).add
        ((isJetInterpolant_taylorJet_polynomial (a ::ₘ s) (X - C a)).mul hp))
    have hjs : j ≤ Multiset.card s := by
      have := (Multiset.count_le_card x (a ::ₘ s)).trans_lt' hj
      rw [Multiset.card_cons] at this
      omega
    have hgx : ContDiffAt 𝕜 j g x := (hg x hx).of_le (by exact_mod_cast hjs)
    have hlin : ContDiffAt 𝕜 j (fun z => z - a) x := contDiffAt_id.sub contDiffAt_const
    have hf : taylorJet f x j = taylorJet ((fun _ => f a) + (fun z => z - a) * g) x j := by
      rw [taylorJet, taylorJet, (hfg x hx).iteratedDeriv_eq]
      rfl
    simp only [Pi.add_apply, eval_C, eval_sub, eval_X]
    rw [hf, taylorJet_add (f := fun _ => f a) (g := (fun z => z - a) * g) contDiffAt_const
      (hlin.mul hgx), taylorJet_mul hlin hgx]
  rw [hq.divDiff_eq_coeff, (hp.of_le (Multiset.le_cons_self s a)).divDiff_eq_coeff,
    Multiset.card_cons, Nat.add_sub_cancel, coeff_C_add_X_sub_C_mul_modByMonic _ _ _ hs]

end Hermite

section Segment

variable {𝕜 : Type*} [RCLike 𝕜] {U : Set 𝕜} {a z : 𝕜}

private theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

/-- A function continuous on a convex set is continuous along the segments in it. -/
theorem ContinuousOn.comp_segment {φ : 𝕜 → 𝕜} (hφ : ContinuousOn φ U) (hU : Convex ℝ U)
    (ha : a ∈ U) (hz : z ∈ U) (k : ℕ) :
    ContinuousOn (fun t : ℝ => t ^ k • φ (a + t • (z - a))) (Icc 0 1) :=
  (continuous_pow k).continuousOn.smul
    (hφ.comp (by fun_prop) fun _ ht => hU.add_smul_sub_mem ha hz ht)

/-- **Differentiation under the integral along segments.** If `φ` has derivative `φ'` on an open
convex set `U`, with `φ'` continuous there, then `w ↦ ∫₀¹ tᵏ φ(a + t(w - a)) dt` has derivative
`∫₀¹ tᵏ⁺¹ φ'(a + t(z - a)) dt` at every `z ∈ U`. -/
theorem hasDerivAt_integral_pow_smul_comp_segment {φ φ' : 𝕜 → 𝕜} (hU : IsOpen U)
    (hUc : Convex ℝ U) (hφ : ∀ w ∈ U, HasDerivAt φ (φ' w) w) (hφ' : ContinuousOn φ' U)
    (ha : a ∈ U) (hz : z ∈ U) (k : ℕ) :
    HasDerivAt (fun w => ∫ t in (0 : ℝ)..1, t ^ k • φ (a + t • (w - a)))
      (∫ t in (0 : ℝ)..1, t ^ (k + 1) • φ' (a + t • (z - a))) z := by
  have hφc : ContinuousOn φ U := fun w hw => (hφ w hw).continuousAt.continuousWithinAt
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
  have hδU : Metric.closedBall z (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  set K := (fun p : ℝ × 𝕜 => a + p.1 • (p.2 - a)) '' (Icc 0 1 ×ˢ Metric.closedBall z (ε / 2))
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_closedBall z _)).image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    exact hUc.add_smul_sub_mem ha (hδU hw) ht
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hφ'.mono hKU)
  have h01 : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hmeas : ∀ {ψ : 𝕜 → 𝕜}, ContinuousOn ψ U → ∀ w ∈ U, ∀ n : ℕ,
      AEStronglyMeasurable (fun t : ℝ => t ^ n • ψ (a + t • (w - a))) (volume.restrict (Ι 0 1)) :=
    fun hψ w hw n => by
      rw [h01]
      exact ((hψ.comp_segment hUc ha hw n).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F := fun w t => t ^ k • φ (a + t • (w - a)))
    (F' := fun w t => t ^ (k + 1) • φ' (a + t • (w - a)))
    (Metric.ball_mem_nhds z (half_pos hε))
    (eventually_of_mem (hU.mem_nhds hz) fun w hw => hmeas hφc w hw k)
    ((hφc.comp_segment hUc ha hz k).intervalIntegrable_of_Icc zero_le_one)
    (hmeas hφ' z hz (k + 1)) (ae_of_all _ fun t ht w hw => ?_) intervalIntegrable_const
    (ae_of_all _ fun t ht w hw => ?_)).2
  · rw [h01] at ht
    have hpt : a + t • (w - a) ∈ K :=
      ⟨(t, w), ⟨Ioc_subset_Icc_self ht, Metric.ball_subset_closedBall hw⟩, rfl⟩
    rw [norm_smul, norm_pow, Real.norm_of_nonneg ht.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.1.le ht.2)).trans (hC _ hpt)
  · rw [h01] at ht
    have hpt : a + t • (w - a) ∈ U :=
      hKU ⟨(t, w), ⟨Ioc_subset_Icc_self ht, Metric.ball_subset_closedBall hw⟩, rfl⟩
    have hin : HasDerivAt (fun w => a + t • (w - a)) (t • (1 : 𝕜)) w :=
      (((hasDerivAt_id w).sub_const a).const_smul t).const_add a
    refine (((hφ _ hpt).comp w hin).const_smul
      (t ^ k)).congr_deriv ?_
    rw [mul_smul_comm, mul_one, smul_smul, pow_succ]

/-- **The segment average**: if `f` has derivative `f'` on a convex set `U`, with `f'`
continuous there, then `f z = f a + (z - a) ∫₀¹ f'(a + t(z - a)) dt` for `a, z ∈ U`. -/
theorem eq_add_mul_integral_comp_segment {f f' : 𝕜 → 𝕜} (hU : Convex ℝ U)
    (hf : ∀ w ∈ U, HasDerivAt f (f' w) w) (hf' : ContinuousOn f' U) (ha : a ∈ U) (hz : z ∈ U) :
    f z = f a + (z - a) * ∫ t in (0 : ℝ)..1, f' (a + t • (z - a)) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => f (a + t • (z - a))) ((z - a) * f' (a + t • (z - a))) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact ((hf _ (hU.add_smul_sub_mem ha hz ht)).scomp t
      (((hasDerivAt_id t).smul_const (z - a)).const_add a)).congr_deriv (by simp [smul_eq_mul])
  have hint : IntervalIntegrable (fun t : ℝ => (z - a) * f' (a + t • (z - a))) volume 0 1 :=
    (((hf'.comp_segment hU ha hz 0).const_smul (z - a)).intervalIntegrable_of_Icc
      zero_le_one).congr fun t _ => by simp [smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul, integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- The derivatives `f⁽ᵏ⁺¹⁾` of a function smooth on an open convex set `U` make the segment
averages `w ↦ ∫₀¹ tᵏ f⁽ᵏ⁺¹⁾(a + t(w - a)) dt` a chain, each the derivative of the previous. -/
theorem hasDerivAt_integral_pow_smul_iteratedDeriv_comp_segment {f : 𝕜 → 𝕜} (hU : IsOpen U)
    (hUc : Convex ℝ U) (hf : ContDiffOn 𝕜 ∞ f U) (ha : a ∈ U) (hz : z ∈ U) (k : ℕ) :
    HasDerivAt (fun w => ∫ t in (0 : ℝ)..1, t ^ k • iteratedDeriv (k + 1) f (a + t • (w - a)))
      (∫ t in (0 : ℝ)..1, t ^ (k + 1) • iteratedDeriv (k + 2) f (a + t • (z - a))) z := by
  have hfN : ContDiffOn 𝕜 (k + 2 : ℕ) f U := hf.of_le (natCast_le_infty _)
  exact hasDerivAt_integral_pow_smul_comp_segment hU hUc
    (fun w hw => hfN.hasDerivAt_iteratedDeriv_of_isOpen hU (j := k + 1) (by omega) hw)
    (hfN.continuousOn_iteratedDeriv_of_isOpen hU le_rfl) ha hz k

/-- **The derivatives of the segment average**: if `f` is smooth on an open convex set `U`, then
`g z = ∫₀¹ f'(a + t(z - a)) dt` has `g⁽ᵏ⁾(z) = ∫₀¹ tᵏ f⁽ᵏ⁺¹⁾(a + t(z - a)) dt` on `U`. -/
theorem iteratedDeriv_integral_deriv_comp_segment {f : 𝕜 → 𝕜} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ContDiffOn 𝕜 ∞ f U) (ha : a ∈ U) (k : ℕ) :
    EqOn (iteratedDeriv k fun w => ∫ t in (0 : ℝ)..1, deriv f (a + t • (w - a)))
      (fun w => ∫ t in (0 : ℝ)..1, t ^ k • iteratedDeriv (k + 1) f (a + t • (w - a))) U := by
  induction k with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    rw [iteratedDeriv_succ, (ih.eventuallyEq_of_mem (hU.mem_nhds hw)).deriv_eq,
      (hasDerivAt_integral_pow_smul_iteratedDeriv_comp_segment hU hUc hf ha hw k).deriv]

/-- The segment average of a function smooth on an open convex set is smooth there. -/
theorem contDiffOn_integral_deriv_comp_segment {f : 𝕜 → 𝕜} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ContDiffOn 𝕜 ∞ f U) (ha : a ∈ U) :
    ContDiffOn 𝕜 ∞ (fun w => ∫ t in (0 : ℝ)..1, deriv f (a + t • (w - a))) U := by
  refine contDiffOn_of_differentiableOn_deriv fun k _ => ?_
  refine DifferentiableOn.congr (fun w hw => ?_) (iteratedDerivWithin_of_isOpen hU)
  exact ((hasDerivAt_integral_pow_smul_iteratedDeriv_comp_segment hU hUc hf ha hw k
    ).differentiableAt.congr_of_eventuallyEq
      ((iteratedDeriv_integral_deriv_comp_segment hU hUc hf ha k).eventuallyEq_of_mem
        (hU.mem_nhds hw))).differentiableWithinAt

/-- The weighted segment average of `φ` is bounded by `M / (k + 1)` when `‖φ‖ ≤ M` on the
segment. -/
theorem norm_integral_pow_smul_comp_segment_le {φ : 𝕜 → 𝕜} {M : ℝ} (k : ℕ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ (a + t • (z - a))‖ ≤ M) :
    ‖∫ t in (0 : ℝ)..1, t ^ k • φ (a + t • (z - a))‖ ≤ M / (k + 1) := by
  calc ‖∫ t in (0 : ℝ)..1, t ^ k • φ (a + t • (z - a))‖
      ≤ ∫ t in (0 : ℝ)..1, t ^ k * M := by
        refine norm_integral_le_of_norm_le zero_le_one (ae_of_all _ fun t ht => ?_)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        rw [norm_smul, norm_pow, Real.norm_of_nonneg ht.1.le]
        exact mul_le_mul_of_nonneg_left (hM t (Ioc_subset_Icc_self ht)) (pow_nonneg ht.1.le _)
    _ = M / (k + 1) := by
        rw [intervalIntegral.integral_mul_const, integral_pow, one_pow,
          zero_pow (Nat.succ_ne_zero k), sub_zero]
        ring

end Segment

namespace Hermite

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq 𝕜]

/-- **The Hermite–Genocchi bound**, for a function smooth on an open convex set `U`: at `r + 1`
nodes in a convex `Ω ⊆ U`, `‖f[s]‖ ≤ M / r!` when `‖f⁽ʳ⁾‖ ≤ M` on `Ω`. -/
theorem norm_divDiff_le_of_contDiffOn {U Ω : Set 𝕜} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hΩ : Convex ℝ Ω) (hΩU : Ω ⊆ U) {f : 𝕜 → 𝕜} (hf : ContDiffOn 𝕜 ∞ f U) {r : ℕ}
    {s : Multiset 𝕜} (hs : Multiset.card s = r + 1) (hsΩ : ∀ x ∈ s, x ∈ Ω) {M : ℝ}
    (hM : ∀ z ∈ Ω, ‖iteratedDeriv r f z‖ ≤ M) :
    ‖divDiff f s‖ ≤ M / r.factorial := by
  induction r generalizing f s M with
  | zero =>
    obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hs
    simpa using hM x (hsΩ x (Multiset.mem_singleton_self x))
  | succ r ih =>
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card s)
    obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.card_cons, Nat.add_right_cancel_iff] at hs
    have haU : a ∈ U := hΩU (hsΩ a ha)
    obtain ⟨g, hgdef⟩ : ∃ g : 𝕜 → 𝕜, g = fun w => ∫ t in (0 : ℝ)..1, deriv f (a + t • (w - a)) :=
      ⟨_, rfl⟩
    have hg : ContDiffOn 𝕜 ∞ g U := by
      rw [hgdef]
      exact contDiffOn_integral_deriv_comp_segment hU hUc hf haU
    have hf1 : ContDiffOn 𝕜 (1 : ℕ) f U := hf.of_le (natCast_le_infty _)
    have hf' : ∀ w ∈ U, HasDerivAt f (deriv f w) w := fun w hw => by
      simpa using hf1.hasDerivAt_iteratedDeriv_of_isOpen hU (j := 0) one_pos hw
    have hf'c : ContinuousOn (deriv f) U := by
      simpa using hf1.continuousOn_iteratedDeriv_of_isOpen hU le_rfl
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
    have hfg : divDiff f (a ::ₘ s) = divDiff g s :=
      divDiff_cons_eq_of_eventuallyEq hs0
        (fun x hx => (hg.contDiffAt (hU.mem_nhds (hΩU (hsΩ x hx)))).of_le
          (by exact_mod_cast le_top))
        (fun x hx => eventually_of_mem (hU.mem_nhds (hΩU (hsΩ x hx))) fun w hw => by
          rw [hgdef]
          exact eq_add_mul_integral_comp_segment hUc hf' hf'c haU hw)
    have hbound : ∀ z ∈ Ω, ‖iteratedDeriv r g z‖ ≤ M / (r + 1) := fun z hz => by
      rw [hgdef, iteratedDeriv_integral_deriv_comp_segment hU hUc hf haU r (hΩU hz)]
      exact norm_integral_pow_smul_comp_segment_le r fun t ht =>
        hM _ (hΩ.add_smul_sub_mem (hsΩ a ha) hz ht)
    rw [hfg]
    refine (ih hg hs (fun x hx => hsΩ x (Multiset.mem_cons_of_mem hx)) hbound).trans_eq ?_
    rw [Nat.factorial_succ, Nat.cast_mul, div_div]
    push_cast
    ring

/-- **The Hermite–Genocchi bound** ([golub2013matrix] (9.2.1)): if `f` is analytic on a
neighbourhood of a convex set `Ω` and `‖f⁽ʳ⁾‖ ≤ M` on `Ω`, then the divided difference of `f` at
`r + 1` nodes of `Ω`, repeated or not, satisfies `‖f[s]‖ ≤ M / r!`. -/
theorem norm_divDiff_le {Ω : Set 𝕜} (hΩ : Convex ℝ Ω) {f : 𝕜 → 𝕜} (hf : AnalyticOnNhd 𝕜 f Ω)
    {r : ℕ} {s : Multiset 𝕜} (hs : Multiset.card s = r + 1) (hsΩ : ∀ x ∈ s, x ∈ Ω) {M : ℝ}
    (hM : ∀ z ∈ Ω, ‖iteratedDeriv r f z‖ ≤ M) :
    ‖divDiff f s‖ ≤ M / r.factorial := by
  obtain ⟨K, hK, hKc, hKΩ, hsK⟩ :
      ∃ K : Set 𝕜, IsCompact K ∧ Convex ℝ K ∧ K ⊆ Ω ∧ ∀ x ∈ s, x ∈ K :=
    ⟨convexHull ℝ {x | x ∈ s}, (Multiset.finite_toSet s).isCompact_convexHull ℝ,
      convex_convexHull ℝ _, convexHull_min (fun x hx => hsΩ x hx) hΩ,
      fun x hx => subset_convexHull ℝ {x | x ∈ s} hx⟩
  have hfK : AnalyticOnNhd 𝕜 f K := fun z hz => hf z (hKΩ hz)
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open (isOpen_analyticAt 𝕜 f) hfK
  have hUo : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
  have hUc : Convex ℝ (Metric.thickening δ K) := hKc.thickening δ
  have hKU : K ⊆ Metric.thickening δ K := Metric.self_subset_thickening hδ K
  have hfU : AnalyticOnNhd 𝕜 f (Metric.thickening δ K) := fun z hz => hδU hz
  have hfU' : ContDiffOn 𝕜 ∞ f (Metric.thickening δ K) := hfU.contDiffOn_of_completeSpace
  exact norm_divDiff_le_of_contDiffOn hUo hUc hKc hKU hfU' hs hsK fun z hz => hM z (hKΩ hz)

end Hermite
