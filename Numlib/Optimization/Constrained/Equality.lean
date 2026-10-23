import Numlib.Optimization.Constrained
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Vector equality-constrained Lagrangian optimality

Surjectivity of the actual constraint Jacobian is the equality LICQ. The multiplier
functional supplied by the geometric Lagrange multiplier theorem is normalized and
represented by a vector through Riesz duality, giving the minus inner-product convention.

For second-order necessity, the implicit-function theorem gives a feasible differentiable
curve with any prescribed Jacobian-kernel velocity. A stationary objective's second-order
Peano remainder along that curve yields the Hessian inequality; no second derivative of
the curve is assumed. The sufficient test specializes the existing componentwise theorem
and retains the exact Lagrangian Hessian and the full Jacobian kernel.
-/

open Set Filter Topology

namespace Descent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Along a differentiable curve through a stationary point, a one-sided local
minimum forces the Hessian to be nonnegative on the curve's velocity. -/
theorem hessian_nonneg_of_stationary_curve {L : E → ℝ} {L' : E → E →L[ℝ] ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ} {x v : E} {γ : ℝ → E}
    (hL : ∀ᶠ z in 𝓝 x, HasFDerivAt L (L' z) z)
    (hH : HasFDerivAt L' H x) (hstat : L' x = 0)
    (hγ0 : γ 0 = x) (hγ : HasDerivAt γ v 0)
    (hmin : ∀ᶠ t in 𝓝[>] (0 : ℝ), L x ≤ L (γ t)) : 0 ≤ H v v := by
  have hγlim : Tendsto γ (𝓝 0) (𝓝 x) := by simpa [hγ0] using hγ.continuousAt.tendsto
  let R : ℝ → ℝ := fun t => L (γ t) - L x - L' x (γ t - x) - H (γ t - x) (γ t - x) / 2
  have hrem := (isLittleO_taylor_two hL hH).comp_tendsto hγlim
  have hbound : (fun t : ℝ => ‖γ t - x‖ ^ 2) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
    simpa [hγ0] using hγ.isBigO_sub.norm_left.pow 2
  have hRlim : Tendsto (fun t : ℝ => R t / t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    exact (hrem.trans_isBigO hbound).tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (γ t - x)) (𝓝[>] 0) (𝓝 v) := by
    simpa [hγ0] using hγ.tendsto_slope_zero_right
  have hHcont : Continuous (fun z : E => H z z) :=
    H.continuous₂.comp (continuous_id.prodMk continuous_id)
  have hlim : Tendsto (fun t : ℝ => H (t⁻¹ • (γ t - x)) (t⁻¹ • (γ t - x)) / 2 + R t / t ^ 2)
      (𝓝[>] 0) (𝓝 (H v v / 2)) := by
    simpa using (((hHcont.tendsto v).comp hslope).div_const 2).add hRlim
  have hnonneg : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ H (t⁻¹ • (γ t - x)) (t⁻¹ • (γ t - x)) / 2 + R t / t ^ 2 := by
    filter_upwards [hmin, self_mem_nhdsWithin] with t ht htpos
    have ht0 : t ≠ 0 := ne_of_gt htpos
    have he : H (t⁻¹ • (γ t - x)) (t⁻¹ • (γ t - x)) / 2 + R t / t ^ 2 =
        (L (γ t) - L x) / t ^ 2 := by
      simp only [R, hstat, zero_apply, sub_zero, map_smul,
        smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [he]
    exact div_nonneg (sub_nonneg.mpr ht) (sq_nonneg t)
  have h := ge_of_tendsto hlim hnonneg
  linarith
end Descent

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The Hessian of a stationary auxiliary objective agreeing with the objective
on the equality-constrained feasible set is nonnegative along the Jacobian kernel. -/
theorem hessian_nonneg_on_kernel {f L : E → ℝ} {L' : E → E →L[ℝ] ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ} {c : E → F} {c' : E →L[ℝ] F} {x v : E}
    (hx : c x = 0) (hmin : IsLocalMinOn f {z | c z = 0} x)
    (hc : HasStrictFDerivAt c c' x) (hsurj : c'.range = ⊤)
    (hagree : ∀ z, c z = 0 → L z = f z)
    (hL : ∀ᶠ z in 𝓝 x, HasFDerivAt L (L' z) z)
    (hH : HasFDerivAt L' H x) (hstat : L' x = 0) (hv : c' v = 0) : 0 ≤ H v v := by
  obtain ⟨γ,hγ0,hγ,hγc⟩ :=
    exists_hasDerivAt_of_hasStrictFDerivAt_of_range_eq_top hc hsurj v
  have hγlim : Tendsto γ (𝓝 0) (𝓝 x) := by simpa [hγ0] using hγ.continuousAt.tendsto
  have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), c (γ t) = 0 := by
    simpa [hx,hv] using hγc
  have hm : ∀ᶠ z in 𝓝 x, c z = 0 → f x ≤ f z :=
    eventually_nhdsWithin_iff.mp hmin
  have hcurve : ∀ᶠ t in 𝓝[>] (0 : ℝ), L x ≤ L (γ t) := by
    filter_upwards [hfeas.filter_mono nhdsWithin_le_nhds,
      (hγlim.eventually hm).filter_mono nhdsWithin_le_nhds] with t ht htm
    rw [hagree x hx,hagree (γ t) ht]
    exact htm ht
  exact Descent.hessian_nonneg_of_stationary_curve hL hH hstat hγ0 hγ hcurve

end Constrained


namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Vector-valued Lagrange multipliers for equality constraints with surjective derivative,
using the minus inner-product convention. -/
theorem exists_vector_multiplier {f : E → ℝ} {c : E → F} {x : E}
    (hx : c x = 0) (hmin : IsLocalMinOn f {z | c z = 0} x)
    (hf : HasStrictFDerivAt f (fderiv ℝ f x) x)
    (hc : HasStrictFDerivAt c (fderiv ℝ c x) x)
    (hsurj : (fderiv ℝ c x).range = ⊤) :
    ∃ y : F, fderiv ℝ (fun z => f z - inner ℝ y (c z)) x = 0 := by
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hext : IsLocalExtrOn f {z | c z = c x} x := by
    rw [hx]
    exact IsMinFilter.isExtrFilter hmin
  obtain ⟨Λ,Λ₀,hne,hsum⟩ := hext.exists_linear_map_of_hasStrictFDerivAt hc hf
  have hΛ0 : Λ₀ ≠ 0 := by
    intro hz
    have hΛ : Λ = 0 := by
      apply LinearMap.ext
      intro z
      obtain ⟨v,rfl⟩ := LinearMap.range_eq_top.mp hsurj z
      simpa [hz] using hsum v
    exact hne (Prod.ext hΛ hz)
  let price : F →ₗ[ℝ] ℝ := (-Λ₀⁻¹) • Λ
  let priceCLM : F →L[ℝ] ℝ := price.toContinuousLinearMap
  let y : F := (InnerProductSpace.toDual ℝ F).symm priceCLM
  have hprice (z : F) : inner ℝ y z = price z := by simp [y,priceCLM]
  have hval (v : E) : fderiv ℝ f x v = inner ℝ y (fderiv ℝ c x v) := by
    rw [hprice]
    simp only [price, LinearMap.smul_apply, smul_eq_mul]
    have h := hsum v
    simp only [smul_eq_mul] at h
    field_simp
    linarith
  have hd : HasFDerivAt (fun z => f z - inner ℝ y (c z))
      (fderiv ℝ f x - (innerSL ℝ y).comp (fderiv ℝ c x)) x :=
    hf.hasFDerivAt.sub ((innerSL ℝ y).hasFDerivAt.comp x hc.hasFDerivAt)
  refine ⟨y, hd.fderiv.trans ?_⟩
  ext v
  simp [hval]
end Constrained


namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A stationary equality-constrained Lagrangian has nonnegative Hessian on the
Jacobian kernel at a regular local minimum. -/
theorem vector_lagrangian_hessian_nonneg {f : E → ℝ} {c : E → F} {x v : E}
    {y : F} {S : Set E} (hS : IsOpen S) (hxS : x ∈ S)
    (hf : ContDiffOn ℝ 2 f S) (hc : ContDiffOn ℝ 2 c S) (hx : c x = 0)
    (hmin : IsLocalMinOn f {z | c z = 0} x) (hsurj : (fderiv ℝ c x).range = ⊤)
    (hstat : fderiv ℝ (fun z => f z - inner ℝ y (c z)) x = 0)
    (hv : fderiv ℝ c x v = 0) :
    0 ≤ fderiv ℝ (fderiv ℝ (fun z => f z - inner ℝ y (c z))) x v v := by
  let L : E → ℝ := fun z => f z - inner ℝ y (c z)
  have hLOn : ContDiffOn ℝ 2 L S := hf.sub ((innerSL ℝ y).contDiff.comp_contDiffOn hc)
  have hLat := hLOn.contDiffAt (hS.mem_nhds hxS)
  have hLnear : ∀ᶠ z in 𝓝 x, HasFDerivAt L (fderiv ℝ L z) z := by
    filter_upwards [hS.mem_nhds hxS] with z hz
    exact ((hLOn.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hH : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) x) x :=
    ((hLat.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      (by norm_num)).hasFDerivAt
  exact hessian_nonneg_on_kernel hx hmin
    ((hc.contDiffAt (hS.mem_nhds hxS)).hasStrictFDerivAt (by norm_num)) hsurj
    (fun z hz => by simp [L,hz]) hLnear hH hstat hv
end Constrained


namespace Constrained
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The positive Lagrangian Hessian test on the kernel of vector equality constraints. -/
theorem strict_local_min_of_vector_lagrangian {m : ℕ}
    {f : E → ℝ} {c : E → EuclideanSpace ℝ (Fin m)} {x : E}
    {y : EuclideanSpace ℝ (Fin m)} {S : Set E}
    (hS : IsOpen S) (hxS : x ∈ S) (hf : ContDiffOn ℝ 2 f S) (hc : ContDiffOn ℝ 2 c S)
    (hx : c x = 0)
    (hstat : fderiv ℝ (fun z => f z - inner ℝ y (c z)) x = 0)
    (hpos : ∀ v ≠ 0, fderiv ℝ c x v = 0 →
      0 < fderiv ℝ (fderiv ℝ (fun z => f z - inner ℝ y (c z))) x v v) :
    ∃ δ > 0, ∀ z, c z = 0 → dist z x < δ → z ≠ x → f x < f z := by
  let h : Fin m → E → ℝ := fun i z => c z i
  let h' : Fin m → E → E →L[ℝ] ℝ := fun i z =>
    (EuclideanSpace.proj i).comp (fderiv ℝ c z)
  let l : Fin m → ℝ := fun i => -y i
  let L : E → ℝ := fun z => f z - inner ℝ y (c z)
  let L' : E → E →L[ℝ] ℝ := fun z => fderiv ℝ f z + ∑ i, l i • h' i z
  have hvalue (z : E) : lagrangian f h z l = L z := by
    simp [lagrangian,h,l,L,PiLp.inner_apply,mul_comm,Finset.sum_neg_distrib,sub_eq_add_neg]
  have hset : feasibleEq h = {z | c z = 0} := by
    ext z
    change (∀ i, c z i = 0) ↔ c z = 0
    constructor
    · intro hz; ext i; exact hz i
    · intro hz i; simp [hz]
  have hfnear : ∀ᶠ z in 𝓝 x, HasFDerivAt f (fderiv ℝ f z) z := by
    filter_upwards [hS.mem_nhds hxS] with z hz
    exact ((hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hcnear : ∀ᶠ z in 𝓝 x, HasFDerivAt c (fderiv ℝ c z) z := by
    filter_upwards [hS.mem_nhds hxS] with z hz
    exact ((hc.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hhnear : ∀ i, ∀ᶠ z in 𝓝 x, HasFDerivAt (h i) (h' i z) z := by
    intro i
    filter_upwards [hcnear] with z hz
    exact (EuclideanSpace.proj i).hasFDerivAt.comp z hz
  have hLnear : ∀ᶠ z in 𝓝 x, HasFDerivAt L (L' z) z := by
    filter_upwards [hfnear,eventually_all.mpr hhnear] with z hzf hzh
    exact (lagrangian_hasFDerivAt hzf hzh l).congr_of_eventuallyEq
      (Eventually.of_forall (fun z => (hvalue z).symm))
  have hderivEq : (fun z => fderiv ℝ L z) =ᶠ[𝓝 x] L' := by
    filter_upwards [hLnear] with z hz
    exact hz.fderiv
  have hLat : ContDiffAt ℝ 2 L x := by
    have hfAt := hf.contDiffAt (hS.mem_nhds hxS)
    have hcAt := hc.contDiffAt (hS.mem_nhds hxS)
    exact hfAt.sub ((innerSL ℝ y).contDiff.contDiffAt.comp x hcAt)
  have hH : HasFDerivAt L' (fderiv ℝ (fderiv ℝ L) x) x :=
    ((hLat.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      (by norm_num)).hasFDerivAt.congr_of_eventuallyEq hderivEq.symm
  have hstationary : L' x = 0 := by
    rw [← hderivEq.self_of_nhds]
    exact hstat
  have hpositive : ∀ v, v ≠ 0 → (∀ i, h' i x v = 0) →
      0 < fderiv ℝ (fderiv ℝ L) x v v := by
    intro v hv0 hv
    apply hpos v hv0
    ext i
    exact hv i
  obtain ⟨δ,hδ,hbound⟩ := isLocalMin_of_lagrangian_second_order
    (h := h) (h' := h') (l := l) (f' := fderiv ℝ f) (H := fderiv ℝ (fderiv ℝ L) x)
    (by rw [hset]; exact hx) hfnear hhnear hH hstationary hpositive
  refine ⟨δ,hδ,?_⟩
  intro z hz hdist hne
  exact hbound z (by rw [hset]; exact hz) hdist hne
end Constrained
