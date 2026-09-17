import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Numlib.Analysis.ODE.PicardLindelof

/-!
# The Cauchy problem on a normed space

The Cauchy problem `y' = f(t, y)`, `y(t₀) = y₀` for a time-dependent field `f : ℝ → E → E` on a
real normed space `E`, as the numerical-analysis books state it ([quarteroni2000numerical] §11.1
and §11.9, [kress1998numerical] §10.1): a *solution on a set of times* `I` (`ODE.IsSolutionOn`,
with the derivative taken within `I`, so that on `Icc a b` the endpoints carry one-sided
derivatives and no case split is needed), the equivalent *integral equation*
`y t = y₀ + ∫_{t₀}^t f(τ, y τ) dτ` for a continuous field (`isSolutionOn_iff_integral`), the
*Liapunov stability* of the problem under simultaneous perturbations of the datum and of the
source (`IsLiapunovStable`, `IsAsymptoticallyStable`), the estimate
`‖y t - z t‖ ≤ (1 + (t - t₀)) ε e^{L (t - t₀)}` for a field `L`-Lipschitz in the state
(`norm_sub_le_of_lipschitz`) with the stability it implies, and *existence and uniqueness*: global,
on a whole compact interval, for a field continuous on `Icc a b × E` and uniformly Lipschitz in
the state (`exists_isSolutionOn_of_lipschitz`, `existsUnique_isSolutionOn_of_lipschitz`); local,
in the books' constants, for a field Lipschitz on a box (`exists_isSolutionOn_of_lipschitzOnWith`).

**What Mathlib has.** `ODE.picard`, `ODE.hasDerivWithinAt_picard_Icc` and
`ODE.picard_eq_of_hasDerivAt` (`Mathlib/Analysis/ODE/PicardLindelof.lean`) are the two halves of
the integral characterization. `IsPicardLindelof` with `Numlib/Analysis/ODE/PicardLindelof`'s
`IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt` is local existence and
uniqueness on a ball. `norm_le_gronwallBound_of_norm_deriv_right_le`
(`Mathlib/Analysis/ODE/Gronwall.lean`) is the differential Gronwall inequality behind the stability
estimate; the books derive the same
estimate from the integral form of Gronwall's lemma (`Gronwall.le_mul_exp_of_le_add_integral` in
`Numlib/Analysis/ODE/Gronwall`), which needs the integral equation and hence continuity of the
field — the differential route needs neither, so it is the one used.

**What it lacks.** Global existence for a globally Lipschitz field: `IsPicardLindelof` bounds the
length of the time interval by `a / L` with `L` a bound of the field on a ball of radius `a`, and a
globally Lipschitz field grows linearly on large balls, so the constraint caps the interval at
`1 / K` — the artefact the books also carry (`r₀ < 1/L` in [quarteroni2000numerical] §11.1). The
route here is the classical one: the Picard operator `α ↦ (t ↦ y₀ + ∫_{t₀}^t f(τ, α τ) dτ)` on the
complete space `C(Icc a b, E)` has `n`-th iterate Lipschitz with constant `(K (b - a))^n / n!`
(`dist_iterate_picardMap_le`, the estimate Mathlib proves for its `FunSpace` on the short
interval), so some iterate is a contraction and the fixed point solves the problem.

## Conventions

Time sets are `Icc a b` with `t₀ ∈ Icc a b` where the argument is two-sided (the integral
characterization, existence) and `Icc t₀ (t₀ + T)` where it runs forward in time (the stability
estimate, which is a right-derivative Gronwall argument); the books' `[t₀, t₀ + T]` is the latter.
Lipschitz constants are `ℝ≥0` as in Mathlib's `LipschitzWith`. Joint continuity of the field is
`ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ)`.
-/

open Set Filter Topology Metric Function
open scoped NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E → E} {t₀ a b T : ℝ} {y₀ : E} {I : Set ℝ} {y z : ℝ → E} {K : ℝ≥0}

/-! ### Solutions of the Cauchy problem -/

/-- `y` is a **solution of the Cauchy problem** `y' = f(t, y)`, `y(t₀) = y₀`
([quarteroni2000numerical] (11.1), (11.78)) on the set of times `I`: `y t₀ = y₀`, and at every
`t ∈ I` the derivative of `y` *within* `I` is `f t (y t)` (one-sided at the endpoints of an
interval). The point `t₀` is not required to lie in `I`. -/
def IsSolutionOn (f : ℝ → E → E) (t₀ : ℝ) (y₀ : E) (I : Set ℝ) (y : ℝ → E) : Prop :=
  y t₀ = y₀ ∧ ∀ t ∈ I, HasDerivWithinAt y (f t (y t)) I t

/-- A solution takes the initial value at `t₀`. -/
theorem IsSolutionOn.apply_eq (h : IsSolutionOn f t₀ y₀ I y) : y t₀ = y₀ := h.1

/-- A solution satisfies the equation within `I`. -/
theorem IsSolutionOn.hasDerivWithinAt (h : IsSolutionOn f t₀ y₀ I y) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt y (f t (y t)) I t :=
  h.2 t ht

/-- A solution is continuous on `I`. -/
theorem IsSolutionOn.continuousOn (h : IsSolutionOn f t₀ y₀ I y) : ContinuousOn y I :=
  HasDerivWithinAt.continuousOn h.2

/-- A solution on `I` is a solution on every subset of `I`. -/
theorem IsSolutionOn.mono (h : IsSolutionOn f t₀ y₀ I y) {J : Set ℝ} (hJ : J ⊆ I) :
    IsSolutionOn f t₀ y₀ J y :=
  ⟨h.1, fun t ht => (h.2 t (hJ ht)).mono hJ⟩

/-- Being a solution on `I` only depends on the values on `I` (and at `t₀`). -/
theorem IsSolutionOn.congr (h : IsSolutionOn f t₀ y₀ I y) (hz : EqOn z y I) (hz₀ : z t₀ = y₀) :
    IsSolutionOn f t₀ y₀ I z :=
  ⟨hz₀, fun t ht => by rw [hz ht]; exact (h.2 t ht).congr hz (hz ht)⟩

/-- Along a solution of a field continuous on `I × E`, the derivative `t ↦ f t (y t)` is continuous
on `I`: the books' `y ∈ C¹(I)`. -/
theorem IsSolutionOn.continuousOn_deriv (h : IsSolutionOn f t₀ y₀ I y)
    (hf : ContinuousOn (uncurry f) (I ×ˢ univ)) : ContinuousOn (fun t => f t (y t)) I :=
  continuousOn_comp hf h.continuousOn (mapsTo_univ _ _)

/-- **The integral form of the Cauchy problem** ([quarteroni2000numerical] (11.2)): for a field
continuous on `Icc a b × E`, `t₀ ∈ Icc a b`, and a curve `y` continuous on `Icc a b`, `y` solves
the Cauchy problem on `Icc a b` iff `y t = y₀ + ∫_{t₀}^t f(τ, y τ) dτ` for every `t ∈ Icc a b`.
The forward direction is the fundamental theorem of calculus (`ODE.picard_eq_of_hasDerivAt`), the
reverse one the differentiation of the primitive (`ODE.hasDerivWithinAt_picard_Icc`); continuity
of `y` only enters through the integrability of `τ ↦ f τ (y τ)`, and the forward direction
provides it. -/
theorem isSolutionOn_iff_integral [CompleteSpace E] (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (hy : ContinuousOn y (Icc a b)) :
    IsSolutionOn f t₀ y₀ (Icc a b) y ↔ ∀ t ∈ Icc a b, y t = y₀ + ∫ τ in t₀..t, f τ (y τ) := by
  constructor
  · intro h t ht
    have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ ht
    have := picard_eq_of_hasDerivAt (f := f) (u := univ) (hf.mono (prod_mono hsub subset_rfl))
      (fun t' ht' => (h.2 t' (hsub ht')).mono hsub) (mapsTo_univ _ _)
    rw [picard_apply, h.1] at this
    exact this.symm
  · intro h
    refine ⟨?_, fun t ht => ?_⟩
    · rw [h t₀ ht₀, intervalIntegral.integral_same, add_zero]
    · exact (hasDerivWithinAt_picard_Icc (f := f) (u := univ) ht₀ hf hy (fun _ _ => mem_univ _)
        y₀ ht).congr (fun t' ht' => h t' ht') (h t ht)

/-! ### Liapunov stability -/

/-- **Liapunov stability** of the Cauchy problem `y' = f(t, y)`, `y(t₀) = y₀` on the set of
times `I` ([quarteroni2000numerical] Definition 11.1): there is a constant `C > 0`, independent
of `ε`, such that for every `ε > 0` and every perturbation `(δ₀, δ)` of the datum and of the
source with `‖δ₀‖ < ε`, `δ` continuous on `I` and `‖δ t‖ < ε` on `I`, every solution `y` of the
problem and every solution `z` of the perturbed problem `z' = f(t, z) + δ(t)`, `z(t₀) = y₀ + δ₀`
((11.4)) satisfy `‖y t - z t‖ < C ε` on `I` ((11.5)). The book restricts to `ε` small enough
for the perturbed solution to exist; quantifying over the solutions that exist makes that
clause vacuous when none does. -/
def IsLiapunovStable (f : ℝ → E → E) (t₀ : ℝ) (y₀ : E) (I : Set ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ (δ₀ : E) (δ : ℝ → E), ‖δ₀‖ < ε → ContinuousOn δ I →
    (∀ t ∈ I, ‖δ t‖ < ε) → ∀ y z : ℝ → E, IsSolutionOn f t₀ y₀ I y →
      IsSolutionOn (fun t v => f t v + δ t) t₀ (y₀ + δ₀) I z → ∀ t ∈ I, ‖y t - z t‖ < C * ε

/-- **Asymptotic stability** ([quarteroni2000numerical] (11.6)): the problem is Liapunov stable
on every bounded interval `Icc t₀ (t₀ + T)`, and for every sufficiently small perturbation —
`‖δ₀‖ < ε` and `‖δ t‖ < ε` on `Ici t₀` for some `ε > 0` fixed by the problem, `δ` continuous —
the solutions `y` of the problem and `z` of the perturbed problem on `Ici t₀` satisfy
`‖y t - z t‖ → 0` as `t → +∞`. -/
def IsAsymptoticallyStable (f : ℝ → E → E) (t₀ : ℝ) (y₀ : E) : Prop :=
  (∀ T : ℝ, 0 < T → IsLiapunovStable f t₀ y₀ (Icc t₀ (t₀ + T))) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ₀ : E) (δ : ℝ → E), ‖δ₀‖ < ε → ContinuousOn δ (Ici t₀) →
      (∀ t ∈ Ici t₀, ‖δ t‖ < ε) → ∀ y z : ℝ → E, IsSolutionOn f t₀ y₀ (Ici t₀) y →
        IsSolutionOn (fun t v => f t v + δ t) t₀ (y₀ + δ₀) (Ici t₀) z →
          Tendsto (fun t => ‖y t - z t‖) atTop (𝓝 0)

/-- The Gronwall bound with `δ = ε` is dominated by the books' closed form:
`gronwallBound ε K ε s ≤ (1 + s) ε e^{K s}` for `K, ε ≥ 0` and every `s`. For `K > 0` this is
`(e^{Ks} - 1) / K ≤ s e^{Ks}`, i.e. `1 - Ks ≤ e^{-Ks}`. -/
theorem gronwallBound_le_mul_exp {K ε s : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound ε K ε s ≤ (1 + s) * ε * Real.exp (K * s) := by
  rcases eq_or_lt_of_le hK with rfl | hK
  · rw [gronwallBound_K0, zero_mul, Real.exp_zero]
    nlinarith
  · rw [gronwallBound_of_K_ne_0 hK.ne']
    have h1 : (1 - K * s) * Real.exp (K * s) ≤ 1 := by
      calc (1 - K * s) * Real.exp (K * s) ≤ Real.exp (-(K * s)) * Real.exp (K * s) := by
            gcongr
            linarith [Real.add_one_le_exp (-(K * s))]
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h2 : ε / K * (Real.exp (K * s) - 1) ≤ s * ε * Real.exp (K * s) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK]
      have : Real.exp (K * s) - 1 ≤ K * s * Real.exp (K * s) := by nlinarith
      calc ε * (Real.exp (K * s) - 1) ≤ ε * (K * s * Real.exp (K * s)) := by gcongr
        _ = s * ε * Real.exp (K * s) * K := by ring
    nlinarith

/-- **The stability estimate of [quarteroni2000numerical] §11.1**: if `f t` is `L`-Lipschitz for
every `t ∈ [t₀, t₀ + T]`, `‖δ₀‖ ≤ ε`, `‖δ t‖ ≤ ε` on the interval, `y` solves the Cauchy problem
and `z` the perturbed problem `z' = f(t, z) + δ(t)`, `z(t₀) = y₀ + δ₀`, then
`‖y t - z t‖ ≤ (1 + (t - t₀)) ε e^{L (t - t₀)}` for `t ∈ [t₀, t₀ + T]`.

Proof: `w = z - y` has right derivative `f(t, z) + δ - f(t, y)` of norm `≤ L ‖w‖ + ε`, so
Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le` bounds `‖w t‖` by
`gronwallBound ε L ε (t - t₀)`, which `gronwallBound_le_mul_exp` bounds by the closed form. The
book applies its integral Gronwall lemma (Lemma 11.1, `Gronwall.le_mul_exp_of_le_add_integral`)
to `‖w t‖ ≤ (1 + (t - t₀)) ε + L ∫_{t₀}^t ‖w‖` instead, which needs the integral equation and hence
continuity of `f`; no continuity of `f` or `δ` is needed here. -/
theorem norm_sub_le_of_lipschitz {L : ℝ≥0} (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t))
    {δ₀ : E} {δ : ℝ → E} {ε : ℝ} (hδ₀ : ‖δ₀‖ ≤ ε) (hδ : ∀ t ∈ Icc t₀ (t₀ + T), ‖δ t‖ ≤ ε)
    (hy : IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hz : IsSolutionOn (fun t v => f t v + δ t) t₀ (y₀ + δ₀) (Icc t₀ (t₀ + T)) z) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + T)) :
    ‖y t - z t‖ ≤ (1 + (t - t₀)) * ε * Real.exp (L * (t - t₀)) := by
  have hwc : ContinuousOn (fun s => z s - y s) (Icc t₀ (t₀ + T)) :=
    hz.continuousOn.sub hy.continuousOn
  have hw' : ∀ s ∈ Ico t₀ (t₀ + T),
      HasDerivWithinAt (fun s => z s - y s) (f s (z s) + δ s - f s (y s)) (Ici s) s := fun s hs =>
    ((hz.hasDerivWithinAt (Ico_subset_Icc_self hs)).sub
      (hy.hasDerivWithinAt (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hw0 : ‖z t₀ - y t₀‖ ≤ ε := by rw [hz.1, hy.1, add_sub_cancel_left]; exact hδ₀
  have bound : ∀ s ∈ Ico t₀ (t₀ + T),
      ‖f s (z s) + δ s - f s (y s)‖ ≤ L * ‖z s - y s‖ + ε := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    calc ‖f s (z s) + δ s - f s (y s)‖ = ‖(f s (z s) - f s (y s)) + δ s‖ := by congr 1; abel
      _ ≤ ‖f s (z s) - f s (y s)‖ + ‖δ s‖ := norm_add_le _ _
      _ ≤ L * ‖z s - y s‖ + ε := add_le_add ((hf s hs').norm_sub_le _ _) (hδ s hs')
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hwc hw' hw0 bound t ht
  rw [norm_sub_rev]
  exact key.trans (gronwallBound_le_mul_exp L.coe_nonneg ((norm_nonneg _).trans hδ₀))

/-- **A Lipschitz field gives a Liapunov stable Cauchy problem** ([quarteroni2000numerical]
§11.1): if `f t` is `L`-Lipschitz for `t ∈ [t₀, t₀ + T]`, the problem is Liapunov stable on
`[t₀, t₀ + T]` for every datum, with the book's constant `C = (1 + K_I) e^{L K_I}`, `K_I = T`.
The strict inequality comes from `norm_sub_le_of_lipschitz` applied with the maximum of `‖δ₀‖`
and of `‖δ‖` on the compact interval, which is `< ε`. -/
theorem isLiapunovStable_of_lipschitz (hT : 0 ≤ T) {L : ℝ≥0}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t)) (y₀ : E) :
    IsLiapunovStable f t₀ y₀ (Icc t₀ (t₀ + T)) := by
  refine ⟨(1 + T) * Real.exp (L * T), by positivity,
    fun ε hε δ₀ δ hδ₀ hδc hδ y z hy hz t ht => ?_⟩
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith))
    (continuous_norm.comp_continuousOn hδc)
  have hε' : max ‖δ₀‖ ‖δ s‖ < ε := max_lt hδ₀ (hδ s hs)
  have h1 : ‖δ₀‖ ≤ max ‖δ₀‖ ‖δ s‖ := le_max_left _ _
  have h2 : ∀ t ∈ Icc t₀ (t₀ + T), ‖δ t‖ ≤ max ‖δ₀‖ ‖δ s‖ := fun t ht =>
    (hmax ht : ‖δ t‖ ≤ ‖δ s‖).trans (le_max_right _ _)
  have hε'0 : 0 ≤ max ‖δ₀‖ ‖δ s‖ := (norm_nonneg _).trans h1
  have hs0 : 0 ≤ t - t₀ := sub_nonneg.2 ht.1
  have hsT : t - t₀ ≤ T := by linarith [ht.2]
  calc ‖y t - z t‖ ≤ (1 + (t - t₀)) * max ‖δ₀‖ ‖δ s‖ * Real.exp (L * (t - t₀)) :=
        norm_sub_le_of_lipschitz hf h1 h2 hy hz ht
    _ ≤ (1 + T) * max ‖δ₀‖ ‖δ s‖ * Real.exp (L * T) := by gcongr
    _ = (1 + T) * Real.exp (L * T) * max ‖δ₀‖ ‖δ s‖ := by ring
    _ < (1 + T) * Real.exp (L * T) * ε := by gcongr

/-- **Uniqueness for a Lipschitz field**: two solutions of the Cauchy problem on `[t₀, t₀ + T]`
agree there. The stability estimate with `ε = 0`. -/
theorem isSolutionOn_unique_of_lipschitz (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith K (f t))
    (hy : IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hz : IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + T)) z) : EqOn y z (Icc t₀ (t₀ + T)) := by
  intro t ht
  have hz' : IsSolutionOn (fun t v => f t v + (0 : ℝ → E) t) t₀ (y₀ + 0) (Icc t₀ (t₀ + T)) z := by
    simpa using hz
  have := norm_sub_le_of_lipschitz hf (δ₀ := 0) (ε := 0) (by simp) (fun _ _ => by simp) hy hz' ht
  rw [mul_zero, zero_mul] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-! ### Global existence: the Picard operator on `C(Icc a b, E)` -/

section Existence

/-- The integrand `τ ↦ f τ (α τ)` of the Picard operator, for `α : C(Icc a b, E)` extended to `ℝ`
by `Set.IccExtend`, is continuous on `Icc a b`. -/
theorem continuousOn_comp_iccExtend (hab : a ≤ b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (α : C(Icc a b, E)) :
    ContinuousOn (fun τ => f τ (IccExtend hab α τ)) (Icc a b) :=
  continuousOn_comp hf α.continuous.Icc_extend'.continuousOn (mapsTo_univ _ _)

/-- The integrand of the Picard operator is interval integrable between `t₀` and any `t` in the
interval. -/
theorem intervalIntegrable_comp_iccExtend (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (α : C(Icc a b, E)) (t : Icc a b) :
    IntervalIntegrable (fun τ => f τ (IccExtend hab α τ)) MeasureTheory.volume t₀ t :=
  ((continuousOn_comp_iccExtend hab hf α).mono (uIcc_subset_Icc ht₀ t.2)).intervalIntegrable

/-- **The Picard operator** on `C(Icc a b, E)`: `α ↦ (t ↦ y₀ + ∫_{t₀}^t f(τ, α τ) dτ)`, the
right-hand side of the integral equation (11.2) of [quarteroni2000numerical], with `α` extended
to `ℝ` by `Set.IccExtend`. Its fixed points are the solutions of the Cauchy problem on `Icc a b`
(`isSolutionOn_iff_integral`). -/
noncomputable def picardMap (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E) (α : C(Icc a b, E)) :
    C(Icc a b, E) where
  toFun t := y₀ + ∫ τ in t₀..t, f τ (IccExtend hab α τ)
  continuous_toFun := by
    have h : ContinuousOn (fun t : ℝ => y₀ + ∫ τ in t₀..t, f τ (IccExtend hab α τ)) (Icc a b) := by
      refine continuousOn_const.add ?_
      have := intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume)
        (f := fun τ => f τ (IccExtend hab α τ)) (b₁ := a) (b₂ := b)
        ((continuousOn_comp_iccExtend hab hf α).mono
          (uIcc_subset_Icc (left_mem_Icc.2 hab) (right_mem_Icc.2 hab))).intervalIntegrable
        (by rwa [uIcc_of_le hab])
      rwa [uIcc_of_le hab] at this
    exact h.comp_continuous continuous_subtype_val fun t => t.2

/-- The defining formula of the Picard operator. -/
theorem picardMap_apply (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E) (α : C(Icc a b, E))
    (t : Icc a b) :
    picardMap hab ht₀ hf y₀ α t = y₀ + ∫ τ in t₀..t, f τ (IccExtend hab α τ) :=
  rfl

/-- **The factorial estimate for the Picard iterates**, pointwise: if `f t` is `K`-Lipschitz for
`t ∈ Icc a b`, then `dist (P^n α t) (P^n β t) ≤ (K |t - t₀|)^n / n! · dist α β`, by induction on
`n` with `∫_{t₀}^t |τ - t₀|^n dτ = |t - t₀|^{n+1} / (n + 1)`. This is the estimate of Mathlib's
`ODE.FunSpace.dist_iterate_next_apply_le` for the Picard operator on the whole of `C(Icc a b, E)`,
where the Lipschitz condition holds everywhere and no ball is needed. -/
theorem dist_iterate_picardMap_apply_le (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E)
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t)) (α β : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist ((picardMap hab ht₀ hf y₀)^[n] α t) ((picardMap hab ht₀ hf y₀)^[n] β t) ≤
      (K * |(t : ℝ) - t₀|) ^ n / n.factorial * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dist_eq_norm, picardMap_apply,
      picardMap_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (intervalIntegrable_comp_iccExtend hab ht₀ hf _ t)
        (intervalIntegrable_comp_iccExtend hab ht₀ hf _ t)]
    calc
      _ ≤ ∫ τ in uIoc t₀ (t : ℝ), (K : ℝ) ^ (n + 1) * |τ - t₀| ^ n / n.factorial * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply (MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono
        intro τ hτ
        have hτ' : τ ∈ Icc a b := (uIcc_subset_Icc ht₀ t.2) (uIoc_subset_uIcc hτ)
        rw [← dist_eq_norm, IccExtend_of_mem _ _ hτ', IccExtend_of_mem _ _ hτ']
        calc dist (f τ ((picardMap hab ht₀ hf y₀)^[n] α ⟨τ, hτ'⟩))
              (f τ ((picardMap hab ht₀ hf y₀)^[n] β ⟨τ, hτ'⟩))
            ≤ K * dist ((picardMap hab ht₀ hf y₀)^[n] α ⟨τ, hτ'⟩)
                ((picardMap hab ht₀ hf y₀)^[n] β ⟨τ, hτ'⟩) := (hlip τ hτ').dist_le_mul _ _
          _ ≤ K * ((K * |τ - t₀|) ^ n / n.factorial * dist α β) := by
              gcongr
              exact ih ⟨τ, hτ'⟩
          _ = (K : ℝ) ^ (n + 1) * |τ - t₀| ^ n / n.factorial * dist α β := by
              rw [mul_pow, pow_succ]; ring
      _ ≤ (K * |(t : ℝ) - t₀|) ^ (n + 1) / (n + 1).factorial * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

/-- **The factorial estimate for the Picard iterates** in the supremum metric of
`C(Icc a b, E)`: the `n`-th iterate of the Picard operator is Lipschitz with constant
`(K (b - a))^n / n!`. -/
theorem dist_iterate_picardMap_le (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E)
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t)) (α β : C(Icc a b, E)) (n : ℕ) :
    dist ((picardMap hab ht₀ hf y₀)^[n] α) ((picardMap hab ht₀ hf y₀)^[n] β) ≤
      (K * (b - a)) ^ n / n.factorial * dist α β := by
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  rw [ContinuousMap.dist_le (by positivity)]
  intro t
  refine (dist_iterate_picardMap_apply_le hab ht₀ hf y₀ hlip α β n t).trans ?_
  have habs : |(t : ℝ) - t₀| ≤ b - a := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [t.2.1, t.2.2, ht₀.1, ht₀.2]
  gcongr

/-- Some iterate of the Picard operator is a contraction, whatever the Lipschitz constant and the
length of the interval: `(K (b - a))^n / n! → 0`. -/
theorem exists_contractingWith_iterate_picardMap (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (y₀ : E)
    (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t)) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (picardMap hab ht₀ hf y₀)^[n] := by
  obtain ⟨n, hn⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * (b - a))).eventually
    (gt_mem_nhds zero_lt_one)).exists
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have h0 : (0 : ℝ) ≤ ((K : ℝ) * (b - a)) ^ n / n.factorial := by positivity
  exact ⟨n, ⟨_, h0⟩, hn, LipschitzWith.of_dist_le_mul fun α β =>
    dist_iterate_picardMap_le hab ht₀ hf y₀ hlip α β n⟩

variable [CompleteSpace E]

/-- **Global existence** ([quarteroni2000numerical] §11.1 item 2, Property 11.5): if `f` is
continuous on `Icc a b × E` and `f t` is `K`-Lipschitz for every `t ∈ Icc a b`, then for every
`t₀ ∈ Icc a b` and every datum `y₀` the Cauchy problem has a solution on the whole of `Icc a b`.
The solution is the fixed point of the Picard operator on `C(Icc a b, E)`, some iterate of which
is a contraction (`exists_contractingWith_iterate_picardMap`); it solves the problem by
`isSolutionOn_iff_integral`. -/
theorem exists_isSolutionOn_of_lipschitz (ht₀ : t₀ ∈ Icc a b)
    (hf : ContinuousOn (uncurry f) (Icc a b ×ˢ univ)) (hlip : ∀ t ∈ Icc a b, LipschitzWith K (f t))
    (y₀ : E) : ∃ y : ℝ → E, IsSolutionOn f t₀ y₀ (Icc a b) y := by
  have hab : a ≤ b := ht₀.1.trans ht₀.2
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_picardMap hab ht₀ hf y₀ hlip
  obtain ⟨α, hα⟩ : ∃ α, IsFixedPt (picardMap hab ht₀ hf y₀) α :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  refine ⟨IccExtend hab α, ?_⟩
  rw [isSolutionOn_iff_integral ht₀ hf α.continuous.Icc_extend'.continuousOn]
  intro t ht
  rw [IccExtend_of_mem _ _ ht]
  calc α ⟨t, ht⟩ = picardMap hab ht₀ hf y₀ α ⟨t, ht⟩ := by rw [hα]
    _ = y₀ + ∫ τ in t₀..t, f τ (IccExtend hab α τ) := rfl

/-- **Global existence and uniqueness** ([quarteroni2000numerical] §11.1 item 2, Property 11.5):
for `f` continuous on `[t₀, t₀ + T] × E` and `K`-Lipschitz in the state there, and every datum
`y₀`, there is exactly one `y : ℝ → E` solving the Cauchy problem on `[t₀, t₀ + T]` and equal to
`y₀` off the interval (the values off the interval are pinned so that uniqueness of a function on
`ℝ` makes sense). `IsSolutionOn.continuousOn_deriv` adds that `t ↦ f t (y t)` is continuous on the
interval, i.e. `y ∈ C¹`. -/
theorem existsUnique_isSolutionOn_of_lipschitz (hT : 0 ≤ T)
    (hf : ContinuousOn (uncurry f) (Icc t₀ (t₀ + T) ×ˢ univ))
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith K (f t)) (y₀ : E) :
    ∃! y : ℝ → E, IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + T)) y ∧ ∀ t ∉ Icc t₀ (t₀ + T), y t = y₀ := by
  classical
  have ht₀ : t₀ ∈ Icc t₀ (t₀ + T) := left_mem_Icc.2 (by linarith)
  obtain ⟨y, hy⟩ := exists_isSolutionOn_of_lipschitz ht₀ hf hlip y₀
  refine ⟨fun t => if t ∈ Icc t₀ (t₀ + T) then y t else y₀,
    ⟨hy.congr (fun t ht => ite_eq_left ht) (by simp [ht₀, hy.1]), fun t ht => ite_eq_right ht⟩, ?_⟩
  rintro z ⟨hz, hz'⟩
  funext t
  by_cases ht : t ∈ Icc t₀ (t₀ + T)
  · rw [ite_eq_left ht]
    exact isSolutionOn_unique_of_lipschitz hlip hz hy ht
  · rw [ite_eq_right ht, hz' t ht]

/-- **Local existence and uniqueness** ([quarteroni2000numerical] §11.1 item 1) in the book's
constants: let `f` be continuous on the box `J × Σ`, `J = [t₀ - r_J, t₀ + r_J]`,
`Σ = closedBall y₀ r_Σ`, `K`-Lipschitz in the state on `Σ` for every time in `J`, and bounded by
`M` on the box. Then for every `0 < r₀ ≤ r_J` with `M r₀ ≤ r_Σ` (the book's `r₀ < r_Σ / M`) the
Cauchy problem has exactly one solution on `[t₀ - r₀, t₀ + r₀]` with values in `Σ`. This is
Mathlib's Picard–Lindelöf theorem in the form
`IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt`; the book's third bound
`r₀ < 1 / L` is an artefact of the sup-norm contraction proof and is not needed. -/
theorem exists_isSolutionOn_of_lipschitzOnWith {rJ rS r₀ M : ℝ}
    (hf : ContinuousOn (uncurry f) (Icc (t₀ - rJ) (t₀ + rJ) ×ˢ closedBall y₀ rS))
    (hlip : ∀ t ∈ Icc (t₀ - rJ) (t₀ + rJ), LipschitzOnWith K (f t) (closedBall y₀ rS))
    (hM : ∀ t ∈ Icc (t₀ - rJ) (t₀ + rJ), ∀ v ∈ closedBall y₀ rS, ‖f t v‖ ≤ M)
    (hr₀ : 0 < r₀) (hrJ : r₀ ≤ rJ) (hrS : 0 ≤ rS) (hMr : M * r₀ ≤ rS) :
    ∃ y : ℝ → E, IsSolutionOn f t₀ y₀ (Icc (t₀ - r₀) (t₀ + r₀)) y ∧
      (∀ t ∈ Icc (t₀ - r₀) (t₀ + r₀), y t ∈ closedBall y₀ rS) ∧
      ∀ z : ℝ → E, IsSolutionOn f t₀ y₀ (Icc (t₀ - r₀) (t₀ + r₀)) z →
        (∀ t ∈ Icc (t₀ - r₀) (t₀ + r₀), z t ∈ closedBall y₀ rS) →
        EqOn y z (Icc (t₀ - r₀) (t₀ + r₀)) := by
  have hsub : Icc (t₀ - r₀) (t₀ + r₀) ⊆ Icc (t₀ - rJ) (t₀ + rJ) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have ht₀J : t₀ ∈ Icc (t₀ - rJ) (t₀ + rJ) := ⟨by linarith, by linarith⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ht₀J y₀ (mem_closedBall_self hrS))
  have hPL : IsPicardLindelof f (⟨t₀, by constructor <;> linarith⟩ : Icc (t₀ - r₀) (t₀ + r₀)) y₀
      ⟨rS, hrS⟩ 0 ⟨M, hM0⟩ K :=
    { lipschitzOnWith := fun t ht => hlip t (hsub ht)
      continuousOn := fun v hv =>
        hf.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨hsub ht, hv⟩
      norm_le := fun t ht v hv => hM t (hsub ht) v hv
      mul_max_le := by
        change M * max (t₀ + r₀ - t₀) (t₀ - (t₀ - r₀)) ≤ rS - 0
        rw [add_sub_cancel_left, sub_sub_cancel, max_self, sub_zero]
        exact hMr }
  obtain ⟨α, hα₀, hmem, hα, huniq⟩ := hPL.exists_unique_mem_closedBall_hasDerivWithinAt
    (x := y₀) (by simp) ⟨by linarith, by linarith⟩
  exact ⟨α, ⟨hα₀, hα⟩, hmem, fun z hz hzmem => huniq z hz.1 hzmem hz.2⟩

/-! ### The half-line: Cauchy–Lipschitz–Picard

[brezis2011functional] Theorem 7.3: for a field Lipschitz in the state on all of `[t₀, ∞)`, the
Cauchy problem has exactly one solution on the whole half-line. The book runs the contraction in
the weighted space `{u ∈ C([0, ∞); E) : sup e^{-kt} ‖u(t)‖ < ∞}` with `k > L`; here the solutions
on the compact intervals `[t₀, t₀ + n]` of `exists_isSolutionOn_of_lipschitz` are glued instead,
since they agree on overlaps by `isSolutionOn_unique_of_lipschitz`. -/

/-- **Global existence on the half-line** ([brezis2011functional] Theorem 7.3, Cauchy–Lipschitz–
Picard, existence): for a field continuous on `[t₀, ∞) × E` and `K`-Lipschitz in the state at
every time `t ≥ t₀`, and every datum `y₀`, the Cauchy problem has a solution on `Ici t₀`. The
book's autonomous field `F : E → E` is `f t v := F v`. The solution is glued from the solutions on
the intervals `[t₀, t₀ + n]`: at `t` it is the value of the solution on `[t₀, t₀ + ⌈t - t₀⌉₊ + 1]`,
with which it agrees on that whole interval, a neighbourhood of `t` within `Ici t₀`. -/
theorem exists_isSolutionOn_Ici_of_lipschitz (hf : ContinuousOn (uncurry f) (Ici t₀ ×ˢ univ))
    (hlip : ∀ t ∈ Ici t₀, LipschitzWith K (f t)) (y₀ : E) :
    ∃ y : ℝ → E, IsSolutionOn f t₀ y₀ (Ici t₀) y := by
  -- the solutions on the compact intervals `[t₀, t₀ + n]`
  have hsol : ∀ n : ℕ, ∃ y : ℝ → E, IsSolutionOn f t₀ y₀ (Icc t₀ (t₀ + n)) y := fun n =>
    exists_isSolutionOn_of_lipschitz ⟨le_rfl, by linarith [n.cast_nonneg (α := ℝ)]⟩
      (hf.mono (prod_mono Icc_subset_Ici_self subset_rfl)) (fun t ht => hlip t ht.1) y₀
  choose Y hY using hsol
  -- they agree on their common interval
  have hagree : ∀ m n : ℕ, EqOn (Y m) (Y n) (Icc t₀ (t₀ + (min m n : ℕ))) := fun m n =>
    isSolutionOn_unique_of_lipschitz (T := (min m n : ℕ)) (fun t ht => hlip t ht.1)
      ((hY m).mono (Icc_subset_Icc_right (by gcongr; exact min_le_left m n)))
      ((hY n).mono (Icc_subset_Icc_right (by gcongr; exact min_le_right m n)))
  -- the index of the interval used at time `t`, and the glued function
  set N : ℝ → ℕ := fun t => ⌈t - t₀⌉₊ + 1 with hN
  have hlt : ∀ t, t < t₀ + (N t : ℕ) := fun t => by
    simp only [hN, Nat.cast_add, Nat.cast_one]
    linarith [Nat.le_ceil (t - t₀)]
  refine ⟨fun t => Y (N t) t, ?_, fun t ht => ?_⟩
  · exact (hY (N t₀)).1
  -- on `[t₀, t₀ + N t]` the glued function is the solution `Y (N t)`
  have hcongr : ∀ s ∈ Icc t₀ (t₀ + (N t : ℕ)), Y (N s) s = Y (N t) s := fun s hs =>
    hagree (N s) (N t) ⟨hs.1, by
      rcases min_choice (N s) (N t) with h | h <;> rw [h]
      · exact (hlt s).le
      · exact hs.2⟩
  have hmem : Icc t₀ (t₀ + (N t : ℕ)) ∈ 𝓝[Ici t₀] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (hlt t)))
  have ht' : t ∈ Icc t₀ (t₀ + (N t : ℕ)) := ⟨ht, (hlt t).le⟩
  refine HasDerivWithinAt.mono_of_mem_nhdsWithin ?_ hmem
  exact ((hY (N t)).2 t ht').congr hcongr (hcongr t ht')

omit [CompleteSpace E] in
/-- **Uniqueness on the half-line** ([brezis2011functional] Theorem 7.3, uniqueness): two solutions
of the Cauchy problem on `Ici t₀` for a field `K`-Lipschitz in the state at every `t ≥ t₀` agree
on `Ici t₀`: restrict both to `[t₀, t]` and apply `isSolutionOn_unique_of_lipschitz`. -/
theorem isSolutionOn_unique_of_lipschitz_Ici (hlip : ∀ t ∈ Ici t₀, LipschitzWith K (f t))
    (hy : IsSolutionOn f t₀ y₀ (Ici t₀) y) (hz : IsSolutionOn f t₀ y₀ (Ici t₀) z) :
    EqOn y z (Ici t₀) := fun t ht =>
  isSolutionOn_unique_of_lipschitz (T := t - t₀) (fun s hs => hlip s hs.1)
    (hy.mono Icc_subset_Ici_self) (hz.mono Icc_subset_Ici_self) ⟨ht, by linarith⟩

/-- **Cauchy–Lipschitz–Picard** ([brezis2011functional] Theorem 7.3): for a field continuous on
`[t₀, ∞) × E` and `K`-Lipschitz in the state at every `t ≥ t₀`, and every datum `y₀`, there is
exactly one `y : ℝ → E` solving the Cauchy problem on `Ici t₀` and equal to `y₀` before `t₀`
(the values before `t₀` are pinned so that uniqueness of a function on `ℝ` makes sense, as in
`existsUnique_isSolutionOn_of_lipschitz`). The book's `u ∈ C¹([0, ∞); E)` is
`IsSolutionOn.continuousOn_deriv`. -/
theorem existsUnique_isSolutionOn_Ici_of_lipschitz
    (hf : ContinuousOn (uncurry f) (Ici t₀ ×ˢ univ))
    (hlip : ∀ t ∈ Ici t₀, LipschitzWith K (f t)) (y₀ : E) :
    ∃! y : ℝ → E, IsSolutionOn f t₀ y₀ (Ici t₀) y ∧ ∀ t < t₀, y t = y₀ := by
  classical
  obtain ⟨y, hy⟩ := exists_isSolutionOn_Ici_of_lipschitz hf hlip y₀
  refine ⟨fun t => if t ∈ Ici t₀ then y t else y₀,
    ⟨hy.congr (fun t ht => ite_eq_left ht) (by simp [hy.1]),
      fun t ht => ite_eq_right (not_le.2 ht)⟩, ?_⟩
  rintro z ⟨hz, hz'⟩
  funext t
  by_cases ht : t ∈ Ici t₀
  · rw [ite_eq_left ht]
    exact isSolutionOn_unique_of_lipschitz_Ici hlip hz hy ht
  · rw [ite_eq_right ht, hz' t (not_le.1 ht)]

end Existence

end ODE
