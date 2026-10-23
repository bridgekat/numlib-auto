import Numlib.Optimization.Constrained.Equality
import Mathlib.Tactic

/-!
# Optimality for nonnegative inequality constraints

Active-gradient LICQ gives nonnegative KKT multipliers. On the multiplier critical
cone the implicit-function theorem supplies curves whose active constraints evolve
linearly; positive-multiplier constraints remain zero along these curves. A stationary
Lagrangian's Peano expansion proves second-order necessity. Strict sufficiency follows
by taking a limiting normalized direction of any violating feasible sequence; its
critical-cone membership is derived from feasibility, descent and complementarity.
Vector adapters use the actual Jacobian and Hessian of `f − ⟪y,c⟫`, with local `C²` data.
-/

open Set Filter Topology
namespace Constrained
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
/-- Nonnegative-constraint KKT multipliers under active-gradient LICQ. -/
theorem exists_inequality_multiplier
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {a : ι → E → ℝ}
    {a' : ι → E → E →L[ℝ] ℝ} {x : E}
    (hx : ∀ i, 0 ≤ a i x)
    (hreg : LinearIndependent ℝ (fun i : activeSet a x => a' i x))
    (hmin : IsLocalMinOn f {z | ∀ i, 0 ≤ a i z} x)
    (hf : HasFDerivAt f (f' x) x)
    (ha : ∀ i, HasStrictFDerivAt (a i) (a' i x) x) :
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, μ i * a i x = 0) ∧
      f' x + ∑ i, (-μ i) • a' i x = 0 := by
  classical
  let h : Empty → E → ℝ := fun i => nomatch i
  let h' : Empty → E → E →L[ℝ] ℝ := fun i => nomatch i
  let g : ι → E → ℝ := fun i z => -a i z
  let g' : ι → E → E →L[ℝ] ℝ := fun i z => -a' i z
  have hneg : LinearIndependent ℝ (fun j : activeSet g x => g' j x) := by
    let e : activeSet g x → activeSet a x := fun j => ⟨j.val,neg_eq_zero.mp j.prop⟩
    have he : Function.Injective e := fun i j hij =>
      Subtype.ext (congrArg (fun q : activeSet a x => q.val) hij)
    exact hreg.neg.comp e he
  have hlicq : IsRegularPointIneq h h' g g' x := by
    refine ⟨(fun i => nomatch i),(fun i => neg_nonpos.mpr (hx i)),?_⟩
    exact linearIndependent_empty_type.sum_type hneg (by
      rw [Set.range_eq_empty,Submodule.span_empty]
      exact disjoint_bot_left)
  have hset : feasible h g = {z | ∀ i, 0 ≤ a i z} := by
    ext z
    simp [feasible,h,g]
  obtain ⟨l,μ,hkkt⟩ := exists_kkt_of_isLocalMinOn hlicq (by rw [hset]; exact hmin)
    hf (fun i => nomatch i) (fun i => (ha i).neg)
  refine ⟨μ,hkkt.nonneg,?_,?_⟩
  · intro i
    have hc := hkkt.complementary i
    simpa [g] using hc
  · have heq : (∑ i, (-μ i) • a' i x) = ∑ i, μ i • g' i x := by
      apply Finset.sum_congr rfl
      intro i _
      exact (neg_smul (μ i) (a' i x)).trans (smul_neg (μ i) (a' i x)).symm
    rw [heq]
    simpa using hkkt.stationary
end Constrained


open Set Filter Topology
namespace Constrained
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι]

/-- Second-order necessity on the multiplier critical cone for nonnegative inequalities. -/
theorem inequality_lagrangian_hessian_nonneg
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {a : ι → E → ℝ}
    {a' : ι → E → E →L[ℝ] ℝ} {μ : ι → ℝ} {x v : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hx : ∀ i, 0 ≤ a i x) (hμ : ∀ i, 0 ≤ μ i) (hcomp : ∀ i, μ i * a i x = 0)
    (hmin : IsLocalMinOn f {z | ∀ i, 0 ≤ a i z} x)
    (hreg : LinearIndependent ℝ (fun i : activeSet a x => a' i x))
    (hf : ∀ᶠ z in 𝓝 x, HasFDerivAt f (f' z) z)
    (ha : ∀ i, ∀ᶠ z in 𝓝 x, HasFDerivAt (a i) (a' i z) z)
    (hastrict : ∀ i, HasStrictFDerivAt (a i) (a' i x) x)
    (hH : HasFDerivAt (fun z => f' z + ∑ i, (-μ i) • a' i z) H x)
    (hstat : f' x + ∑ i, (-μ i) • a' i x = 0)
    (hv : ∀ i, a i x = 0 → (0 < μ i → a' i x v = 0) ∧
      (μ i = 0 → 0 ≤ a' i x v)) : 0 ≤ H v v := by
  classical
  let A := activeSet a x
  let cf : E → (A → ℝ) := fun z i => a i z
  let cf' : E →L[ℝ] (A → ℝ) := ContinuousLinearMap.pi (fun i => a' i x)
  have hcf : HasStrictFDerivAt cf cf' x := hasStrictFDerivAt_pi.mpr (fun i => hastrict i)
  have hcf_range : cf'.range = ⊤ := hreg.range_pi_eq_top
  obtain ⟨γ,hγ0,hγ,hγc⟩ :=
    exists_hasDerivAt_of_hasStrictFDerivAt_of_range_eq_top hcf hcf_range v
  have hγlim : Tendsto γ (𝓝 0) (𝓝 x) := by simpa [hγ0] using hγ.continuousAt.tendsto
  have hactive : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, a i x = 0 →
      a i (γ t) = t * a' i x v := by
    filter_upwards [hγc] with t ht i hi
    have heq := congrFun ht (⟨i,hi⟩ : A)
    simpa [cf,cf',ContinuousLinearMap.pi_apply,hi] using heq
  have hinactive : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, a i x ≠ 0 → 0 < a i (γ t) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : a i x = 0
    · exact Eventually.of_forall (fun _ h => False.elim (h hi))
    · have hpos : 0 < a i x := lt_of_le_of_ne (hx i) (Ne.symm hi)
      exact (((hastrict i).continuousAt.tendsto.comp hγlim).eventually (lt_mem_nhds hpos)).mono
        (fun _ ht _ => ht)
  have hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, 0 ≤ a i (γ t) := by
    filter_upwards [hactive.filter_mono nhdsWithin_le_nhds,
      hinactive.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hi htpos i
    by_cases hai : a i x = 0
    · rw [ht i hai]
      apply mul_nonneg (le_of_lt htpos)
      rcases eq_or_lt_of_le (hμ i) with h0 | hpos
      · exact (hv i hai).2 h0.symm
      · exact ((hv i hai).1 hpos).ge
    · exact (hi i hai).le
  let L : E → ℝ := fun z => lagrangian f a z (fun i => -μ i)
  let L' : E → E →L[ℝ] ℝ := fun z => f' z + ∑ i, (-μ i) • a' i z
  have hLnear : ∀ᶠ z in 𝓝 x, HasFDerivAt L (L' z) z := by
    filter_upwards [hf,eventually_all.mpr ha] with z hzf hza
    exact lagrangian_hasFDerivAt hzf hza (fun i => -μ i)
  have hLx : L x = f x := by
    simp only [L,lagrangian,neg_mul,hcomp,neg_zero,Finset.sum_const_zero,add_zero]
  have hLag : ∀ᶠ t in 𝓝 (0 : ℝ), L (γ t) = f (γ t) := by
    filter_upwards [hactive] with t ht
    have hzero : ∀ i, μ i * a i (γ t) = 0 := by
      intro i
      by_cases hai : a i x = 0
      · rcases eq_or_lt_of_le (hμ i) with h0 | hpos
        · simp [h0.symm]
        · rw [ht i hai,(hv i hai).1 hpos,mul_zero,mul_zero]
      · have hμ0 : μ i = 0 := (mul_eq_zero.mp (hcomp i)).resolve_right hai
        simp [hμ0]
    simp only [L,lagrangian,neg_mul,hzero,neg_zero,Finset.sum_const_zero,add_zero]
  have hm : ∀ᶠ z in 𝓝 x, (∀ i, 0 ≤ a i z) → f x ≤ f z :=
    eventually_nhdsWithin_iff.mp hmin
  have hcurve : ∀ᶠ t in 𝓝[>] (0 : ℝ), L x ≤ L (γ t) := by
    filter_upwards [hfeas,hLag.filter_mono nhdsWithin_le_nhds,
      (hγlim.eventually hm).filter_mono nhdsWithin_le_nhds] with t ht hLt hmt
    rw [hLx,hLt]
    exact hmt ht
  exact Descent.hessian_nonneg_of_stationary_curve hLnear hH hstat hγ0 hγ hcurve
end Constrained


open Set Filter Topology
namespace Constrained
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- Strict second-order sufficiency for inequality constraints in the nonnegative convention. -/
theorem strict_local_min_of_inequality_lagrangian
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {a : ι → E → ℝ}
    {a' : ι → E → E →L[ℝ] ℝ} {μ : ι → ℝ} {x : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hcomp : ∀ i, μ i * a i x = 0)
    (hf : ∀ᶠ w in 𝓝 x, HasFDerivAt f (f' w) w)
    (ha : ∀ i, ∀ᶠ w in 𝓝 x, HasFDerivAt (a i) (a' i w) w)
    (hH : HasFDerivAt (fun w => f' w + ∑ i, (-μ i) • a' i w) H x)
    (hstat : f' x + ∑ i, (-μ i) • a' i x = 0)
    (hpos : ∀ v, v ≠ 0 → (∀ i, a i x = 0 →
      (0 < μ i → a' i x v = 0) ∧ (μ i = 0 → 0 ≤ a' i x v)) → 0 < H v v) :
    ∃ δ > 0, ∀ w, (∀ i, 0 ≤ a i w) → dist w x < δ → w ≠ x → f x < f w := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ y, y ∈ {z | ∀ i, 0 ≤ a i z} ∧ dist y x < 1 / ((n : ℝ) + 1) ∧ y ≠ x ∧
      f y ≤ f x := by
    intro n
    obtain ⟨y, hyS, hyd, hyne, hyf⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨y, hyS, hyd, hyne, hyf⟩
  choose y hyS hyd hyne hyf using hseq
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hyd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hwne : ∀ n, y n - x ≠ 0 := fun n => sub_ne_zero.2 (hyne n)
  set u : ℕ → E := fun n => ‖y n - x‖⁻¹ • (y n - x) with hu
  have hunorm : ∀ n, ‖u n‖ = 1 := fun n => by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hwne n))]
  obtain ⟨z, hz, φ, hφ, hulim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    fun n => mem_sphere_zero_iff_norm.2 (hunorm n)
  have hz0 : z ≠ 0 := by
    intro h0
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hz
    exact zero_ne_one hz
  have hyφ : Tendsto (y ∘ φ) atTop (𝓝 x) := hylim.comp hφ.tendsto_atTop
  -- The normalized limiting direction lies in the critical cone.
  let V : Set E := {w | (∀ i, 0 ≤ a i w) ∧ f w ≤ f x}
  have hzcone : z ∈ posTangentConeAt V x := by
    have hd0 : Tendsto (fun n => y (φ n) - x) atTop (𝓝 0) := by
      simpa using hyφ.sub_const x
    apply mem_tangentConeAt_of_seq atTop
      (fun n => Real.toNNReal (‖y (φ n) - x‖⁻¹)) (fun n => y (φ n) - x) hd0
    · exact Eventually.of_forall fun n => by
        simpa [V] using And.intro (hyS (φ n)) (hyf (φ n))
    · convert hulim using 1
      ext n
      simp [u, NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr (norm_nonneg _))]
  have ha_nonneg : ∀ i, a i x = 0 → 0 ≤ a' i x z := by
    intro i hai
    have hamin : IsMinOn (a i) V x := by
      intro w hw
      change a i x ≤ a i w
      rw [hai]
      exact hw.1 i
    exact hamin.isLocalMinOn.hasFDerivWithinAt_nonneg
      ((ha i).self_of_nhds.hasFDerivWithinAt) hzcone
  have hf_nonpos : f' x z ≤ 0 := by
    have hfmax : IsMaxOn f V x := by
      intro w hw
      exact hw.2
    exact hfmax.isLocalMaxOn.hasFDerivWithinAt_nonpos
      (hf.self_of_nhds.hasFDerivWithinAt) hzcone
  have hterm_nonneg : ∀ i, 0 ≤ μ i * a' i x z := by
    intro i
    by_cases hi : a i x = 0
    · exact mul_nonneg (hμ i) (ha_nonneg i hi)
    · have hμ0 : μ i = 0 := (mul_eq_zero.mp (hcomp i)).resolve_right hi
      simp [hμ0]
  have hsum0 : ∑ i, μ i * a' i x z = 0 := by
    have hst := congrArg (fun q : E →L[ℝ] ℝ => q z) hstat
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, neg_mul,
      Finset.sum_neg_distrib, zero_apply] at hst
    have hsum_nonneg := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hterm_nonneg i)
    linarith
  have hcritical : ∀ i, a i x = 0 →
      (0 < μ i → a' i x z = 0) ∧ (μ i = 0 → 0 ≤ a' i x z) := by
    intro i hi
    refine ⟨?_, fun _ => ha_nonneg i hi⟩
    intro hμi
    have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => hterm_nonneg j)).mp hsum0 i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hterm0).resolve_left hμi.ne'
  -- the second-order expansion of the Lagrangian along the sequence
  set L : E → ℝ := fun y => lagrangian f a y (fun i => -μ i) with hLdef
  set L' : E → E →L[ℝ] ℝ := fun y => f' y + ∑ i, (-μ i) • a' i y with hL'def
  have hL : ∀ᶠ y in 𝓝 x, HasFDerivAt L (L' y) y := by
    filter_upwards [hf, eventually_all.2 ha] with y hfy hhy
    exact lagrangian_hasFDerivAt hfy hhy (fun i => -μ i)
  have hpeano := isLittleO_taylor_two hL hH
  have hL'x : L' x = 0 := hstat
  have hr := (hpeano.tendsto_div_nhds_zero).comp hyφ
  have hkey : ∀ n, H (u (φ n)) (u (φ n)) / 2
      ≤ -((L (y (φ n)) - L x - L' x (y (φ n) - x) - H (y (φ n) - x) (y (φ n) - x) / 2)
          / ‖y (φ n) - x‖ ^ 2) := by
    intro n
    have hLy : L (y (φ n)) ≤ f (y (φ n)) := by
      change f (y (φ n)) + ∑ i, (-μ i) * a i (y (φ n)) ≤ f (y (φ n))
      have hs : ∑ i, (-μ i) * a i (y (φ n)) ≤ 0 :=
        Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (hμ i)) (hyS (φ n) i)
      linarith
    have hLx : L x = f x := by
      change f x + ∑ i, (-μ i) * a i x = f x
      simp only [neg_mul, hcomp, neg_zero, Finset.sum_const_zero, add_zero]
    have hn : ‖y (φ n) - x‖ ≠ 0 := norm_ne_zero_iff.2 (hwne _)
    have hnpos : 0 < ‖y (φ n) - x‖ ^ 2 := pow_pos (norm_pos_iff.2 (hwne _)) 2
    have hHu : H (u (φ n)) (u (φ n)) = H (y (φ n) - x) (y (φ n) - x) / ‖y (φ n) - x‖ ^ 2 := by
      simp only [hu, map_smul, smul_apply, smul_eq_mul]
      field_simp
    rw [hHu, hL'x, zero_apply, sub_zero]
    have hd : (L (y (φ n)) - L x) / ‖y (φ n) - x‖ ^ 2 ≤ 0 :=
      div_nonpos_iff.2 (Or.inr ⟨by linarith [hyf (φ n)], hnpos.le⟩)
    have hsplit : -((L (y (φ n)) - L x - H (y (φ n) - x) (y (φ n) - x) / 2) / ‖y (φ n) - x‖ ^ 2)
        = H (y (φ n) - x) (y (φ n) - x) / ‖y (φ n) - x‖ ^ 2 / 2
          - (L (y (φ n)) - L x) / ‖y (φ n) - x‖ ^ 2 := by
      field_simp
      ring
    rw [hsplit]
    linarith
  have hlimL : Tendsto (fun n => H (u (φ n)) (u (φ n)) / 2) atTop (𝓝 (H z z / 2)) := by
    have hcont : Continuous fun v : E => H v v :=
      H.continuous₂.comp (continuous_id.prodMk continuous_id)
    exact ((hcont.tendsto z).comp hulim).div_const 2
  have hlimR : Tendsto (fun n => -((L (y (φ n)) - L x - L' x (y (φ n) - x)
      - H (y (φ n) - x) (y (φ n) - x) / 2) / ‖y (φ n) - x‖ ^ 2)) atTop (𝓝 (-0)) := by
    refine Tendsto.neg ?_
    refine hr.congr fun n => ?_
    simp only [Function.comp_apply]
  rw [neg_zero] at hlimR
  have hle := le_of_tendsto_of_tendsto' hlimL hlimR hkey
  have := hpos z hz0 hcritical
  linarith

end Constrained

namespace Constrained
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The active-coordinate form of LICQ for a Euclidean vector constraint. -/
def vectorInequalityLICQ {m : ℕ} (c : E → EuclideanSpace ℝ (Fin m)) (x : E) : Prop :=
  LinearIndependent ℝ (fun i : {i : Fin m | c x i = 0} =>
    (EuclideanSpace.proj i.val).comp (fderiv ℝ c x))

omit [FiniteDimensional ℝ E] in
/-- The active-gradient characterization of vector inequality LICQ. -/
theorem vectorInequalityLICQ_iff {m : ℕ} {c : E → EuclideanSpace ℝ (Fin m)} {x : E} :
    vectorInequalityLICQ c x ↔ LinearIndependent ℝ
      (fun i : {i : Fin m | c x i = 0} =>
        (EuclideanSpace.proj i.val).comp (fderiv ℝ c x)) := Iff.rfl

/-- The critical cone for nonnegative constraints and nonnegative multipliers. -/
def vectorCriticalCone {m : ℕ} (c : E → EuclideanSpace ℝ (Fin m))
    (x : E) (y : EuclideanSpace ℝ (Fin m)) : Set E :=
  {v | ∀ i, c x i = 0 →
    (0 < y i → (fderiv ℝ c x v) i = 0) ∧ (y i = 0 → 0 ≤ (fderiv ℝ c x v) i)}

omit [FiniteDimensional ℝ E] in
/-- Membership in the vector multiplier critical cone. -/
@[simp]
theorem mem_vectorCriticalCone {m : ℕ} {c : E → EuclideanSpace ℝ (Fin m)}
    {x v : E} {y : EuclideanSpace ℝ (Fin m)} :
    v ∈ vectorCriticalCone c x y ↔ ∀ i, c x i = 0 →
      (0 < y i → (fderiv ℝ c x v) i = 0) ∧ (y i = 0 → 0 ≤ (fderiv ℝ c x v) i) := Iff.rfl

/-- Vector KKT multipliers for nonnegative constraints, using `f − ⟪y,c⟫`. -/
theorem exists_vector_inequality_multiplier {m : ℕ} {f : E → ℝ}
    {c : E → EuclideanSpace ℝ (Fin m)} {x : E}
    (hx : ∀ i, 0 ≤ c x i) (hreg : vectorInequalityLICQ c x)
    (hmin : IsLocalMinOn f {z | ∀ i, 0 ≤ c z i} x)
    (hf : HasFDerivAt f (fderiv ℝ f x) x)
    (hc : HasStrictFDerivAt c (fderiv ℝ c x) x) :
    ∃ y : EuclideanSpace ℝ (Fin m), (∀ i, 0 ≤ y i) ∧
      (∀ i, y i * c x i = 0) ∧
      fderiv ℝ (fun z => f z - inner ℝ y (c z)) x = 0 := by
  let a : Fin m → E → ℝ := fun i z => c z i
  let a' : Fin m → E → E →L[ℝ] ℝ := fun i z =>
    (EuclideanSpace.proj i).comp (fderiv ℝ c z)
  have ha : ∀ i, HasStrictFDerivAt (a i) (a' i x) x := fun i =>
    (EuclideanSpace.proj i).hasStrictFDerivAt.comp x hc
  obtain ⟨μ,hμ,hcomp,hstat⟩ := exists_inequality_multiplier
    (a := a) (a' := a') hx hreg hmin hf ha
  let y : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 μ
  have hvalue (z : E) : lagrangian f a z (fun i => -μ i) = f z - inner ℝ y (c z) := by
    simp [lagrangian,a,y,PiLp.inner_apply,mul_comm,Finset.sum_neg_distrib,sub_eq_add_neg]
  have hd : HasFDerivAt (fun z => f z - inner ℝ y (c z))
      (fderiv ℝ f x + ∑ i, (-μ i) • a' i x) x :=
    (lagrangian_hasFDerivAt hf (fun i => (ha i).hasFDerivAt) (fun i => -μ i)).congr_of_eventuallyEq
      (Eventually.of_forall (fun z => (hvalue z).symm))
  exact ⟨y,hμ,hcomp,hd.fderiv.trans hstat⟩

omit [FiniteDimensional ℝ E] in
/-- Local derivative data for the vector Lagrangian, with its actual Hessian. -/
theorem vector_inequality_derivative_data {m : ℕ} {f : E → ℝ}
    {c : E → EuclideanSpace ℝ (Fin m)} {x : E} {y : EuclideanSpace ℝ (Fin m)}
    {S : Set E} (hS : IsOpen S) (hxS : x ∈ S)
    (hf : ContDiffOn ℝ 2 f S) (hc : ContDiffOn ℝ 2 c S) :
    let a' : Fin m → E → E →L[ℝ] ℝ := fun i z =>
      (EuclideanSpace.proj i).comp (fderiv ℝ c z)
    let L : E → ℝ := fun z => f z - inner ℝ y (c z)
    let L' : E → E →L[ℝ] ℝ := fun z => fderiv ℝ f z + ∑ i, (-y i) • a' i z
    (∀ᶠ z in 𝓝 x, HasFDerivAt f (fderiv ℝ f z) z) ∧
    (∀ i, ∀ᶠ z in 𝓝 x, HasFDerivAt (fun z => c z i) (a' i z) z) ∧
    HasFDerivAt L' (fderiv ℝ (fderiv ℝ L) x) x ∧ fderiv ℝ L x = L' x := by
  dsimp only
  let a : Fin m → E → ℝ := fun i z => c z i
  let a' : Fin m → E → E →L[ℝ] ℝ := fun i z =>
    (EuclideanSpace.proj i).comp (fderiv ℝ c z)
  let L : E → ℝ := fun z => f z - inner ℝ y (c z)
  let L' : E → E →L[ℝ] ℝ := fun z => fderiv ℝ f z + ∑ i, (-y i) • a' i z
  have hvalue (z : E) : lagrangian f a z (fun i => -y i) = L z := by
    simp [lagrangian,a,L,PiLp.inner_apply,mul_comm,Finset.sum_neg_distrib,sub_eq_add_neg]
  have hfnear : ∀ᶠ z in 𝓝 x, HasFDerivAt f (fderiv ℝ f z) z := by
    filter_upwards [hS.mem_nhds hxS] with z hz
    exact ((hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hcnear : ∀ᶠ z in 𝓝 x, HasFDerivAt c (fderiv ℝ c z) z := by
    filter_upwards [hS.mem_nhds hxS] with z hz
    exact ((hc.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hanear : ∀ i, ∀ᶠ z in 𝓝 x, HasFDerivAt (a i) (a' i z) z := by
    intro i
    filter_upwards [hcnear] with z hz
    exact (EuclideanSpace.proj i).hasFDerivAt.comp z hz
  have hLnear : ∀ᶠ z in 𝓝 x, HasFDerivAt L (L' z) z := by
    filter_upwards [hfnear,eventually_all.mpr hanear] with z hzf hza
    exact (lagrangian_hasFDerivAt hzf hza (fun i => -y i)).congr_of_eventuallyEq
      (Eventually.of_forall (fun z => (hvalue z).symm))
  have heq : (fun z => fderiv ℝ L z) =ᶠ[𝓝 x] L' := hLnear.mono (fun _ hz => hz.fderiv)
  have hLat : ContDiffAt ℝ 2 L x :=
    (hf.contDiffAt (hS.mem_nhds hxS)).sub
      ((innerSL ℝ y).contDiff.contDiffAt.comp x (hc.contDiffAt (hS.mem_nhds hxS)))
  have hH : HasFDerivAt L' (fderiv ℝ (fderiv ℝ L) x) x :=
    ((hLat.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      (by norm_num)).hasFDerivAt.congr_of_eventuallyEq heq.symm
  exact ⟨hfnear,hanear,hH,heq.self_of_nhds⟩

omit [FiniteDimensional ℝ E] in
/-- Second-order necessity on the exact multiplier critical cone for vector inequalities. -/
theorem vector_inequality_lagrangian_hessian_nonneg [CompleteSpace E] {m : ℕ} {f : E → ℝ}
    {c : E → EuclideanSpace ℝ (Fin m)} {x v : E} {y : EuclideanSpace ℝ (Fin m)}
    {S : Set E} (hS : IsOpen S) (hxS : x ∈ S)
    (hf : ContDiffOn ℝ 2 f S) (hc : ContDiffOn ℝ 2 c S)
    (hx : ∀ i, 0 ≤ c x i) (hμ : ∀ i, 0 ≤ y i) (hcomp : ∀ i, y i * c x i = 0)
    (hmin : IsLocalMinOn f {z | ∀ i, 0 ≤ c z i} x)
    (hreg : vectorInequalityLICQ c x)
    (hstat : fderiv ℝ (fun z => f z - inner ℝ y (c z)) x = 0)
    (hv : v ∈ vectorCriticalCone c x y) :
    0 ≤ fderiv ℝ (fderiv ℝ (fun z => f z - inner ℝ y (c z))) x v v := by
  obtain ⟨hfnear,hanear,hH,heq⟩ := vector_inequality_derivative_data (y := y) hS hxS hf hc
  have ha : ∀ i, HasStrictFDerivAt (fun z => c z i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ c x)) x := fun i =>
    (EuclideanSpace.proj i).hasStrictFDerivAt.comp x
      ((hc.contDiffAt (hS.mem_nhds hxS)).hasStrictFDerivAt (by norm_num))
  exact inequality_lagrangian_hessian_nonneg (f := f) (f' := fderiv ℝ f)
    (a := fun i z => c z i)
    (a' := fun i z => (EuclideanSpace.proj i).comp (fderiv ℝ c z))
    (μ := fun i => y i) (v := v) hx hμ hcomp hmin hreg hfnear hanear ha hH
    (heq.symm.trans hstat) hv

/-- Strict second-order sufficiency on the vector multiplier critical cone. -/
theorem strict_local_min_of_vector_inequality_lagrangian {m : ℕ} {f : E → ℝ}
    {c : E → EuclideanSpace ℝ (Fin m)} {x : E} {y : EuclideanSpace ℝ (Fin m)}
    {S : Set E} (hS : IsOpen S) (hxS : x ∈ S)
    (hf : ContDiffOn ℝ 2 f S) (hc : ContDiffOn ℝ 2 c S)
    (_hx : ∀ i, 0 ≤ c x i) (hμ : ∀ i, 0 ≤ y i) (hcomp : ∀ i, y i * c x i = 0)
    (hstat : fderiv ℝ (fun z => f z - inner ℝ y (c z)) x = 0)
    (hpos : ∀ v ≠ 0, v ∈ vectorCriticalCone c x y →
      0 < fderiv ℝ (fderiv ℝ (fun z => f z - inner ℝ y (c z))) x v v) :
    ∃ δ > 0, ∀ z, (∀ i, 0 ≤ c z i) → dist z x < δ → z ≠ x → f x < f z := by
  obtain ⟨hfnear,hanear,hH,heq⟩ := vector_inequality_derivative_data (y := y) hS hxS hf hc
  exact strict_local_min_of_inequality_lagrangian hμ hcomp hfnear hanear hH
    (heq.symm.trans hstat) hpos
end Constrained
namespace Constrained
/-- With nonnegative factors, inner-product complementarity is componentwise complementarity. -/
theorem vector_complementary_iff_inner_eq_zero {m : ℕ}
    {u y : EuclideanSpace ℝ (Fin m)} (hu : ∀ i, 0 ≤ u i) (hy : ∀ i, 0 ≤ y i) :
    (∀ i, y i * u i = 0) ↔ inner ℝ y u = 0 := by
  have heq : inner ℝ y u = ∑ i, y i * u i := by simp [PiLp.inner_apply,mul_comm]
  rw [heq]
  simpa using (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ) (fun i _ => mul_nonneg (hy i) (hu i))).symm
end Constrained
