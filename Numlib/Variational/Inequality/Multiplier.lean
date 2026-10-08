import Mathlib.Analysis.Normed.Module.HahnBanach
import Numlib.MeasureTheory.Function.LpSpace.Duality

/-!
# The Lagrange multiplier of a variational inequality with an `L¹` functional

For a real vector space `V`, a linear map `T : V → L^p(μ)` (`1 ≤ p`, `μ` finite), linear
functionals `A` and `ℓ` on `V` and `g > 0`, consider the variational inequality of the second
kind with the functional `j(v) = g ∫ |T v| dμ`:

  `ℓ(v − u) ≤ A(v − u) + j(v) − j(u)`  for every `v ∈ V`.

It holds exactly when there is a *Lagrange multiplier* `λ ∈ L^∞(μ)` with `|λ| ≤ 1` a.e.,

  `A v + g ∫ λ T v dμ = ℓ v`  for every `v`,  and  `λ T u = |T u|`  a.e.

(`forall_le_add_integral_abs_iff_exists_multiplier`). The model is the simplified friction problem
of elasticity, with `T` the trace `H¹(Ω) → L²(∂Ω)`, `A = a(u, ·)` and `ℓ` the load.

The multiplier comes from `exists_multiplier_of_forall_abs_le`: a linear functional `F` on `V`
with `|F w| ≤ g ‖T w‖_{L¹}` depends on `T w` only, as a functional bounded in the `L¹(μ)` norm on
the range of `T`; the Hahn–Banach theorem (`exists_extension_norm_eq`) extends it to `L¹(μ)` with
norm at most `g`, and the Riesz representation `(L¹)' = L^∞`
(`MeasureTheory.Lp.toDual_surjective`) makes it `h ↦ ∫ λ̄ h dμ` with `‖λ̄‖_∞ ≤ g`.

## References

[han2009theoretical], Theorem 11.4.5 (with no fractional trace space: the functional is extended
from the range of `T` in `L¹`, not from `H^{1/2}(Γ)`).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An element of `L^∞(μ)` of norm at most `g` is bounded by `g` almost everywhere. -/
theorem ae_abs_le_of_norm_le {k : Lp ℝ ⊤ μ} {g : ℝ} (hk : ‖k‖ ≤ g) :
    ∀ᵐ x ∂μ, |k x| ≤ g := by
  have h1 : eLpNormEssSup k μ ≠ ⊤ := by
    have := Lp.eLpNorm_ne_top k
    rwa [eLpNorm_exponent_top (Lp.aestronglyMeasurable k)] at this
  have h2 : (eLpNormEssSup k μ).toReal ≤ g := by
    rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable k)] at hk
    exact hk
  filter_upwards [ae_le_eLpNormEssSup (f := k) (μ := μ)] with x hx
  rw [← Real.norm_eq_abs]
  refine le_trans ?_ h2
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal h1).1 hx

end MeasureTheory.Lp

section Multiplier

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {α : Type*} [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inclusion `L^p(μ) → L¹(μ)` of a finite measure, as a linear map whose function is the
function of its argument. -/
private def toL1 : Lp ℝ p μ →ₗ[ℝ] Lp ℝ 1 μ where
  toFun k := ⟨(k : α →ₘ[μ] ℝ), Lp.antitone (Fact.out : 1 ≤ p) k.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coeFn_toL1 (k : Lp ℝ p μ) : ((toL1 k : Lp ℝ 1 μ) : α → ℝ) = k := rfl

/-- `∫ |k| dμ` is the `L¹` norm of `k ∈ L^p(μ)`. -/
private theorem integral_abs_eq_norm_toL1 (k : Lp ℝ p μ) :
    ∫ x, |k x| ∂μ = ‖toL1 k‖ := by
  rw [L1.norm_eq_integral_norm, coeFn_toL1]
  simp only [Real.norm_eq_abs]

/-- **The Lagrange multiplier by Hahn–Banach and `(L¹)' = L^∞`**: a linear functional `F` on `V`
with `|F w| ≤ g ∫ |T w| dμ` is `F w = ∫ λ̄ T w dμ` for some `λ̄ ∈ L^∞(μ)` with `‖λ̄‖_∞ ≤ g`. The
functional is transported to the range of `T` in `L¹(μ)` through the quotient by `ker T`
(`LinearMap.quotKerEquivRange`), extended to `L¹(μ)` by Hahn–Banach (`exists_extension_norm_eq`)
and represented by the Riesz representation `(L¹)' = L^∞` (`MeasureTheory.Lp.toDual_surjective`).
-/
theorem exists_multiplier_of_forall_abs_le {g : ℝ} (hg : 0 ≤ g) (T : V →ₗ[ℝ] Lp ℝ p μ)
    (F : V →ₗ[ℝ] ℝ) (hF : ∀ w, |F w| ≤ g * ∫ x, |T w x| ∂μ) :
    ∃ l : Lp ℝ ⊤ μ, ‖l‖ ≤ g ∧ ∀ w, F w = ∫ x, l x * T w x ∂μ := by
  let S : V →ₗ[ℝ] Lp ℝ 1 μ := toL1 ∘ₗ T
  have hSnorm : ∀ w, ‖S w‖ = ∫ x, |T w x| ∂μ := fun w ↦ (integral_abs_eq_norm_toL1 (T w)).symm
  -- `F` vanishes on the kernel of `S`
  have hker : LinearMap.ker S ≤ LinearMap.ker F := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have h := hF w
    rw [← hSnorm, hw, norm_zero, mul_zero] at h
    exact abs_nonpos_iff.1 h
  -- the functional on the range of `S`
  let Fq := (LinearMap.ker S).liftQ F hker
  let F' : LinearMap.range S →ₗ[ℝ] ℝ := Fq ∘ₗ S.quotKerEquivRange.symm.toLinearMap
  have hF' : ∀ w, F' ⟨S w, LinearMap.mem_range_self S w⟩ = F w := fun w ↦ by
    simp only [F', LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Fq]
    rfl
  have hbound : ∀ s : LinearMap.range S, ‖F' s‖ ≤ g * ‖s‖ := by
    rintro ⟨_, w, rfl⟩
    rw [hF' w, Real.norm_eq_abs]
    change |F w| ≤ g * ‖S w‖
    rw [hSnorm]
    exact hF w
  let F'' : LinearMap.range S →L[ℝ] ℝ := F'.mkContinuous g hbound
  have hF''norm : ‖F''‖ ≤ g := LinearMap.mkContinuous_norm_le _ hg _
  -- Hahn–Banach
  obtain ⟨G, hGext, hGnorm⟩ := exists_extension_norm_eq (LinearMap.range S) F''
  -- Riesz: `G = ∫ l ·` with `l ∈ L^∞`
  obtain ⟨l, hl⟩ := Lp.toDual_surjective (𝕜 := ℝ) (p := 1) (q := ⊤) (μ := μ)
    ENNReal.one_ne_top G
  refine ⟨l, ?_, fun w ↦ ?_⟩
  · rw [← (Lp.toDual ℝ 1 ⊤ μ).norm_map l, hl, hGnorm]
    exact hF''norm
  · have h1 := hGext ⟨S w, LinearMap.mem_range_self S w⟩
    rw [← hl, Lp.toDual_apply] at h1
    have h2 : F'' ⟨S w, LinearMap.mem_range_self S w⟩ = F w := by
      rw [LinearMap.mkContinuous_apply, hF']
    exact h2.symm.trans h1.symm

/-- **The Lagrange multiplier of a variational inequality with an `L¹` functional**
([han2009theoretical] Theorem 11.4.5, for the simplified friction problem): for `g > 0`, `u`
satisfies `ℓ(v − u) ≤ A(v − u) + g ∫ |T v| dμ − g ∫ |T u| dμ` for every `v` if and only if there
is `λ ∈ L^∞(μ)` with `|λ| ≤ 1` a.e., `A v + g ∫ λ T v dμ = ℓ v` for every `v` and `λ T u = |T u|`
a.e.

From the inequality: `v = 0` and `v = 2u` give `A u + j(u) = ℓ(u)`, and `v = u ± w` with the
subadditivity and evenness of `j` give `|ℓ(w) − A(w)| ≤ j(w)`, so `ℓ − A` is represented on the
range of `T` by an `L^∞(μ)` function of norm at most `g` (`exists_multiplier_of_forall_abs_le`),
`λ` is its quotient by `g`, and `λ T u = |T u|` follows at `v = u`, the integrand
`|T u| − λ T u` being nonnegative with zero integral. Conversely the multiplier identity at
`v − u`, with `λ T v ≤ |T v|` and `λ T u = |T u|`, is the inequality. -/
theorem forall_le_add_integral_abs_iff_exists_multiplier {g : ℝ} (hg : 0 < g)
    (T : V →ₗ[ℝ] Lp ℝ p μ) (A ℓ : V →ₗ[ℝ] ℝ) (u : V) :
    (∀ v, ℓ (v - u) ≤ A (v - u) + g * ∫ x, |T v x| ∂μ - g * ∫ x, |T u x| ∂μ) ↔
      ∃ l : Lp ℝ ⊤ μ, (∀ᵐ x ∂μ, |l x| ≤ 1) ∧ (∀ v, A v + g * ∫ x, l x * T v x ∂μ = ℓ v) ∧
        ∀ᵐ x ∂μ, l x * T u x = |T u x| := by
  have hI : ∀ k : Lp ℝ p μ, Integrable (fun x ↦ |k x|) μ := fun k ↦
    ((Lp.memLp k).integrable Fact.out).abs
  have hIl : ∀ (l : Lp ℝ ⊤ μ) (k : Lp ℝ p μ), Integrable (fun x ↦ l x * k x) μ :=
    fun l k ↦ (Lp.memLp l).integrable_mul ((Lp.memLp k).mono_exponent (Fact.out : 1 ≤ p))
  -- the functional `v ↦ ∫ |T v|` through the `L¹` norm
  have hj : ∀ v, ∫ x, |T v x| ∂μ = ‖toL1 (T v)‖ := fun v ↦ integral_abs_eq_norm_toL1 (T v)
  constructor
  · intro hu
    -- `A u + j(u) = ℓ(u)` and `ℓ(w) ≤ A(w) + j(w)`
    have hj0 : ∫ x, |T 0 x| ∂μ = 0 := by rw [hj, map_zero, map_zero, norm_zero]
    have hj2 : ∫ x, |T ((2 : ℝ) • u) x| ∂μ = 2 * ∫ x, |T u x| ∂μ := by
      rw [hj, hj, map_smul, map_smul, norm_smul, Real.norm_two]
    have e2 : (2 : ℝ) • u - u = u := by rw [two_smul, add_sub_cancel_right]
    have h0 := hu 0
    have h2 := hu ((2 : ℝ) • u)
    rw [hj0, zero_sub, map_neg, map_neg] at h0
    rw [hj2, e2] at h2
    have h23 : A u + g * ∫ x, |T u x| ∂μ = ℓ u := by linarith
    have h24 : ∀ w, ℓ w ≤ A w + g * ∫ x, |T w x| ∂μ := by
      intro w
      have h5 := hu (u + w)
      rw [add_sub_cancel_left] at h5
      have h6 : ∫ x, |T (u + w) x| ∂μ ≤ ∫ x, |T u x| ∂μ + ∫ x, |T w x| ∂μ := by
        rw [hj, hj, hj, map_add, map_add]
        exact norm_add_le _ _
      nlinarith
    -- the functional `F(w) = ℓ(w) − A(w)` is bounded by `j(w)`
    have hF : ∀ w, |(ℓ - A) w| ≤ g * ∫ x, |T w x| ∂μ := by
      intro w
      have h1 := h24 w
      have h2 := h24 (-w)
      rw [map_neg, map_neg, hj (-w), map_neg, map_neg, norm_neg, ← hj w] at h2
      rw [LinearMap.sub_apply, abs_le]
      constructor <;> linarith
    obtain ⟨l, hl, hFl⟩ := exists_multiplier_of_forall_abs_le hg.le T (ℓ - A) hF
    have hlg := Lp.ae_abs_le_of_norm_le hl
    refine ⟨g⁻¹ • l, ?_, fun v ↦ ?_, ?_⟩
    · filter_upwards [hlg, Lp.coeFn_smul g⁻¹ l] with x hx hx'
      rw [hx', Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hg)]
      calc g⁻¹ * |l x| ≤ g⁻¹ * g := by gcongr
        _ = 1 := inv_mul_cancel₀ hg.ne'
    · have e : ∫ x, (g⁻¹ • l : Lp ℝ ⊤ μ) x * T v x ∂μ = g⁻¹ * ∫ x, l x * T v x ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul g⁻¹ l] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [e, ← mul_assoc, mul_inv_cancel₀ hg.ne', one_mul, ← hFl, LinearMap.sub_apply]
      ring
    · have h21 := hFl u
      rw [LinearMap.sub_apply] at h21
      have hgu : ∫ x, l x * T u x ∂μ = g * ∫ x, |T u x| ∂μ := by linarith
      have hnn : 0 ≤ᵐ[μ] fun x ↦ g * |T u x| - l x * T u x := by
        filter_upwards [hlg] with x hx
        have : l x * T u x ≤ g * |T u x| :=
          calc l x * T u x ≤ |l x * T u x| := le_abs_self _
            _ = |l x| * |T u x| := abs_mul _ _
            _ ≤ g * |T u x| := by gcongr
        simp only [Pi.zero_apply]
        linarith
      have hzero : ∫ x, (g * |T u x| - l x * T u x) ∂μ = 0 := by
        rw [integral_sub ((hI _).const_mul g) (hIl l _), integral_const_mul, hgu, sub_self]
      have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
        (((hI _).const_mul g).sub (hIl l _))).1 hzero
      filter_upwards [hae, Lp.coeFn_smul g⁻¹ l] with x hx hx'
      simp only [Pi.zero_apply] at hx
      rw [hx', Pi.smul_apply, smul_eq_mul, mul_assoc]
      have : l x * T u x = g * |T u x| := by linarith
      rw [this, ← mul_assoc, inv_mul_cancel₀ hg.ne', one_mul]
  · rintro ⟨l, hl1, h21, h22⟩ v
    have hv := h21 v
    have hu := h21 u
    have hjv : g * ∫ x, l x * T v x ∂μ ≤ g * ∫ x, |T v x| ∂μ := by
      refine mul_le_mul_of_nonneg_left (integral_mono_ae (hIl l _) (hI _) ?_) hg.le
      filter_upwards [hl1] with x hx
      calc l x * T v x ≤ |l x * T v x| := le_abs_self _
        _ = |l x| * |T v x| := abs_mul _ _
        _ ≤ 1 * |T v x| := by gcongr
        _ = _ := one_mul _
    have hju : ∫ x, l x * T u x ∂μ = ∫ x, |T u x| ∂μ := integral_congr_ae h22
    rw [map_sub, map_sub]
    rw [hju] at hu
    linarith

end Multiplier
