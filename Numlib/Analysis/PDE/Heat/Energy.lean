import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Numlib.Analysis.ODE.Gronwall
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# The energy estimate for the heat equation on an interval

The classical solution of the heat equation `u_t - ν u_xx = f` on `[0, 1] × [0, T]` with
homogeneous Dirichlet conditions ([quarteroni2000numerical] (13.1)–(13.4)) and its a priori
energy estimate ([quarteroni2000numerical] (13.7)): with `E(t) = ∫₀¹ u(x, t)² dx` and
`F(t) = ∫₀¹ f(x, t)² dx`,

`E(t) ≤ e^{-2ν t} E(0) + ∫₀ᵗ e^{2ν(s-t)} F(s)/(2ν) ds`,

the rate `2ν = ν / C_P²` coming from Poincaré's inequality on `(0, 1)`.

## Main definitions

* `Heat.IsClassicalSolutionIccWith ν T f u₀ u ut ux uxx`: `u` is a classical solution with the
  partial derivatives `ut`, `ux`, `uxx` named, taken one-sidedly within the rectangle's edges and
  continuous on the closed rectangle; `Heat.IsClassicalSolutionIcc` quantifies them away.
* `Heat.energy u t`: the energy `∫₀¹ u(x, t)² dx`.

## Main results

* `Heat.IsClassicalSolutionIccWith.continuousOn`: a classical solution is jointly continuous on
  the rectangle — the mean value inequality on each coordinate line, the partial derivatives being
  bounded on the compact rectangle.
* `Heat.IsClassicalSolutionIccWith.energy_sub_eq`: `E(t) - E(0) = ∫₀ᵗ 2 ∫₀¹ u u_t`, the
  "interchange of differentiation and integration" done in integrated form by Fubini, since a
  derivative under the integral sign would have to be two-sided at `t = 0`.
* `Heat.IsClassicalSolutionIccWith.two_mul_integral_mul_le`: the differential inequality
  `2 ∫₀¹ u u_t ≤ -2ν E + F/(2ν)` — integration by parts, Poincaré, Cauchy–Schwarz and Young.
* `Heat.IsClassicalSolutionIcc.energy_le`: the estimate, by the differential Gronwall lemma
  `Gronwall.le_exp_neg_mul_add_integral_of_hasDerivWithinAt_le`.

The interval is `[0, 1]`, as in the source; the general interval changes only the Poincaré
constant. The pointwise side of the classical theory (the maximum principle) is
`Numlib/Analysis/PDE/Heat/Classical`; the semigroup solution on a domain of `ℝᴺ` is
`Numlib/Analysis/PDE/Heat`.
-/

open Set Filter Topology intervalIntegral

namespace Heat

/-- **A classical solution of the heat equation on `[0, 1] × [0, T]`, with its derivatives
named** ([quarteroni2000numerical] (13.1)–(13.4)): `u` solves `u_t - ν u_xx = f` with diffusivity
`ν`, source `f`, homogeneous Dirichlet conditions `u(0, t) = u(1, t) = 0` and initial datum `u₀`,
the three partial derivatives being `ut = ∂u/∂t`, `ux = ∂u/∂x`, `uxx = ∂²u/∂x²`. The derivatives
are taken *within* the rectangle's edges, one-sided at the boundary, and are required continuous
on the closed rectangle, which is what the energy computation uses. -/
def IsClassicalSolutionIccWith (ν T : ℝ) (f : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u ut ux uxx : ℝ → ℝ → ℝ) :
    Prop :=
  (∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t ∧
        HasDerivWithinAt (fun y => u y t) (ux x t) (Icc 0 1) x ∧
        HasDerivWithinAt (fun y => ux y t) (uxx x t) (Icc 0 1) x ∧
        ut x t - ν * uxx x t = f x t) ∧
    ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T) ∧
    ContinuousOn (fun p : ℝ × ℝ => ux p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T) ∧
    ContinuousOn (fun p : ℝ × ℝ => uxx p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T) ∧
    (∀ t ∈ Icc (0 : ℝ) T, u 0 t = 0 ∧ u 1 t = 0) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, u x 0 = u₀ x)

/-- **The classical Dirichlet problem for the heat equation** ([quarteroni2000numerical]
(13.1)–(13.4)): `u` solves `u_t - ν u_xx = f` on `[0, 1] × [0, T]` with `u(0, t) = u(1, t) = 0`
and `u(x, 0) = u₀(x)`, in the classical sense of `Heat.IsClassicalSolutionIccWith` for some choice
of the partial derivatives. -/
def IsClassicalSolutionIcc (ν T : ℝ) (f : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ut ux uxx, IsClassicalSolutionIccWith ν T f u₀ u ut ux uxx

/-! ### The energy -/

/-- The energy `E(t) = ∫₀¹ u(x, t)² dx` of [quarteroni2000numerical] §13.1. The source energy
`F(t) = ∫₀¹ f(x, t)² dx` of the same section is `Heat.energy f t`. -/
noncomputable def energy (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, u x t ^ 2

/-! ### The a priori energy estimate -/

section Energy

open MeasureTheory

variable {ν T : ℝ} {f : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {u ut ux uxx : ℝ → ℝ → ℝ}

/-- **A classical solution is jointly continuous on the rectangle**.
`Heat.IsClassicalSolutionIccWith` asks only for the *partial* derivative data and the continuity
of `u_t`, `u_x`, `u_xx`; joint continuity of
`u` itself follows, because the two partial derivatives are bounded on the compact rectangle
(`IsCompact.exists_bound_of_continuousOn`), so the mean value inequality on each coordinate line
(`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) makes `u` Lipschitz there. Everything the
energy argument does with `u` — Fubini, the continuity of the parametric integrals — needs this. -/
theorem IsClassicalSolutionIccWith.continuousOn (hT : 0 ≤ T)
    (h : IsClassicalSolutionIccWith ν T f u₀ u ut ux uxx) :
    ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T) := by
  obtain ⟨hd, hct, hcx, -, -, -⟩ := h
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) T) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Cx, hCx⟩ := hK.exists_bound_of_continuousOn hcx
  obtain ⟨Ct, hCt⟩ := hK.exists_bound_of_continuousOn hct
  have hCx0 : 0 ≤ Cx := le_trans (norm_nonneg _) (hCx (0, 0) ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hT⟩⟩)
  have hCt0 : 0 ≤ Ct := le_trans (norm_nonneg _) (hCt (0, 0) ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hT⟩⟩)
  have hLx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |u y t - u x t| ≤ Cx * |y - x| := by
    intro t ht x hx y hy
    have hderiv : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun w => u w t) (ux z t) (Icc 0 1) z :=
      fun z hz => (hd z hz t ht).2.1
    have hbound : ∀ z ∈ Icc (0 : ℝ) 1, ‖ux z t‖ ≤ Cx := fun z hz => hCx (z, t) ⟨hz, ht⟩
    have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hx hy
    simpa [Real.norm_eq_abs] using this
  have hLt : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T,
      |u x s - u x t| ≤ Ct * |s - t| := by
    intro x hx t ht s hs
    have hderiv : ∀ r ∈ Icc (0 : ℝ) T, HasDerivWithinAt (u x) (ut x r) (Icc 0 T) r :=
      fun r hr => (hd x hx r hr).1
    have hbound : ∀ r ∈ Icc (0 : ℝ) T, ‖ut x r‖ ≤ Ct := fun r hr => hCt (x, r) ⟨hx, hr⟩
    have := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound ht hs
    simpa [Real.norm_eq_abs] using this
  have hlip : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) T, ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) T,
      dist (u p.1 p.2) (u q.1 q.2) ≤ (Cx + Ct) * dist p q := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩ ⟨y, s⟩ ⟨hy, hs⟩
    have h1 : |u x t - u y t| ≤ Cx * |x - y| := hLx t ht y hy x hx
    have h2 : |u y t - u y s| ≤ Ct * |t - s| := hLt y hy s hs t ht
    have hd1 : |x - y| ≤ dist (x, t) (y, s) := by
      rw [Prod.dist_eq]
      exact le_max_of_le_left (le_of_eq (Real.dist_eq x y).symm)
    have hd2 : |t - s| ≤ dist (x, t) (y, s) := by
      rw [Prod.dist_eq]
      exact le_max_of_le_right (le_of_eq (Real.dist_eq t s).symm)
    have h3 : |u x t - u y s| ≤ Cx * |x - y| + Ct * |t - s| := by
      have := abs_sub_le (u x t) (u y t) (u y s)
      linarith
    rw [Real.dist_eq]
    nlinarith [h3, hd1, hd2, hCx0, hCt0, abs_nonneg (x - y), abs_nonneg (t - s)]
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (Cx + Ct)) ?_).continuousOn
  intro p hp q hq
  have := hlip p hp q hq
  have hK0 : (Real.toNNReal (Cx + Ct) : ℝ) = Cx + Ct :=
    Real.coe_toNNReal _ (by linarith)
  rw [hK0]
  exact this

/-- **Integration by parts in `x`** for a classical solution, the step `∫₀¹ u_xx u = -∫₀¹ (u_x)²`
of [quarteroni2000numerical] §13.1: `(u_x u)' = u_xx u + (u_x)²` and the boundary term vanishes
by the Dirichlet conditions. -/
theorem IsClassicalSolutionIccWith.integral_mul_eq_neg_integral_sq
    (h : IsClassicalSolutionIccWith ν T f u₀ u ut ux uxx)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x in (0 : ℝ)..1, uxx x t * u x t) = -∫ x in (0 : ℝ)..1, ux x t ^ 2 := by
  obtain ⟨hd, -, hcx, hcxx, hbc, -⟩ := h
  have hmap : ContinuousOn (fun x : ℝ => (x, t)) (Icc (0 : ℝ) 1) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hmaps : MapsTo (fun x : ℝ => (x, t)) (Icc (0 : ℝ) 1) (Icc 0 1 ×ˢ Icc 0 T) :=
    fun x hx => ⟨hx, ht⟩
  have hcxs : ContinuousOn (fun x => ux x t) (Icc (0 : ℝ) 1) := hcx.comp hmap hmaps
  have hcxxs : ContinuousOn (fun x => uxx x t) (Icc (0 : ℝ) 1) := hcxx.comp hmap hmaps
  have hcus : ContinuousOn (fun x => u x t) (Icc (0 : ℝ) 1) := fun x hx =>
    ((hd x hx t ht).2.1).continuousWithinAt
  have hF : ContinuousOn (fun x => ux x t * u x t) (Icc (0 : ℝ) 1) := hcxs.mul hcus
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y => ux y t * u y t) (uxx x t * u x t + ux x t ^ 2) x := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
    have hmem : Icc (0 : ℝ) 1 ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have h1 : HasDerivAt (fun y => ux y t) (uxx x t) x := ((hd x hx' t ht).2.2.1).hasDerivAt hmem
    have h2 : HasDerivAt (fun y => u y t) (ux x t) x := ((hd x hx' t ht).2.1).hasDerivAt hmem
    have he : uxx x t * u x t + ux x t ^ 2 = uxx x t * u x t + ux x t * ux x t := by ring
    rw [he]
    exact h1.mul h2
  have hint : IntervalIntegrable (fun x => uxx x t * u x t + ux x t ^ 2) volume 0 1 :=
    ((hcxxs.mul hcus).add (hcxs.pow 2)).intervalIntegrable_of_Icc zero_le_one
  have hfun := integral_eq_sub_of_hasDerivAt_of_le zero_le_one hF hderiv hint
  rw [(hbc t ht).1, (hbc t ht).2, mul_zero, mul_zero, sub_zero] at hfun
  have hsplit : (∫ x in (0 : ℝ)..1, (uxx x t * u x t + ux x t ^ 2))
      = (∫ x in (0 : ℝ)..1, uxx x t * u x t) + ∫ x in (0 : ℝ)..1, ux x t ^ 2 :=
    integral_add ((hcxxs.mul hcus).intervalIntegrable_of_Icc zero_le_one)
      ((hcxs.pow 2).intervalIntegrable_of_Icc zero_le_one)
  rw [hsplit] at hfun
  linarith

/-- **The clamped surrogate** of a function of space and time: `clampRect T w` is `w` composed with
the retraction of the plane onto the rectangle `[0, 1] × [0, T]`. It is *globally* continuous as
soon as `w` is continuous on the rectangle, which is what Mathlib's Fubini theorem and its
parametric-continuity lemma for interval integrals both ask for, neither of them having a
`ContinuousOn` form. -/
private noncomputable def clampRect (T : ℝ) (w : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  w (max 0 (min 1 p.1)) (max 0 (min T p.2))

/-- The clamped surrogate agrees with the function on the rectangle. -/
private theorem clampRect_eq (w : ℝ → ℝ → ℝ) {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) T) : clampRect T w (x, s) = w x s := by
  rw [clampRect, min_eq_right hx.2, max_eq_right hx.1, min_eq_right hs.2, max_eq_right hs.1]

/-- The clamped surrogate of a function continuous on the rectangle is continuous on the plane. -/
private theorem continuous_clampRect (hT : 0 ≤ T) {w : ℝ → ℝ → ℝ}
    (hw : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T)) :
    Continuous (clampRect T w) := by
  have hcl : Continuous fun p : ℝ × ℝ => ((max 0 (min 1 p.1), max 0 (min T p.2)) : ℝ × ℝ) := by
    fun_prop
  have hmem : ∀ p : ℝ × ℝ, ((max 0 (min 1 p.1), max 0 (min T p.2)) : ℝ × ℝ)
      ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) T := fun p =>
    ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩,
      ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩⟩
  exact hw.comp_continuous hcl hmem

/-- **The energy is the primitive of `2 ∫₀¹ u u_t`**:
`E(t) - E(0) = ∫₀ᵗ (2 ∫₀¹ u u_t dx) ds`. This is the book's "interchanged differentiation and
integration", done in the integrated form: the fundamental theorem of calculus in `t` at each fixed
`x` gives `u(x, t)² - u(x, 0)² = ∫₀ᵗ 2 u u_t ds`, and Fubini on the rectangle
(`MeasureTheory.integral_integral_swap`, over the clamped surrogate, which is globally continuous
and hence integrable there) exchanges the two integrals. It replaces differentiating `E` under the
integral sign, which Mathlib can only do two-sidedly and so not at `t = 0`. -/
theorem IsClassicalSolutionIccWith.energy_sub_eq (hT : 0 ≤ T)
    (h : IsClassicalSolutionIccWith ν T f u₀ u ut ux uxx)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    energy u t - energy u 0
      = ∫ s in (0 : ℝ)..t, 2 * ∫ x in (0 : ℝ)..1, u x s * ut x s := by
  have hd := h.1
  set G : ℝ × ℝ → ℝ := clampRect T (fun y r => u y r * ut y r) with hG
  have hcont : Continuous G :=
    continuous_clampRect hT ((h.continuousOn hT).mul h.2.1)
  have hGeq : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) T, G (x, s) = u x s * ut x s :=
    fun x hx s hs => clampRect_eq _ hx hs
  have hsliceF' : ∀ x : ℝ, Continuous fun s => G (x, s) := fun x => hcont.comp (by fun_prop)
  -- the inner fundamental theorem of calculus
  have hinner : ∀ x ∈ Icc (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..t, 2 * G (x, s)) = u x t ^ 2 - u x 0 ^ 2 := by
    intro x hx
    have hcu : ContinuousOn (fun s => u x s ^ 2) (Icc (0 : ℝ) t) := by
      refine ContinuousOn.pow ?_ 2
      intro s hs
      exact ((hd x hx s ⟨hs.1, hs.2.trans ht.2⟩).1).continuousWithinAt.mono
        (Icc_subset_Icc le_rfl ht.2)
    have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
        HasDerivAt (fun r => u x r ^ 2) (2 * G (x, s)) s := by
      intro s hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, (hs.2.le).trans ht.2⟩
      have hmem : Icc (0 : ℝ) T ∈ 𝓝 s := Icc_mem_nhds hs.1 (lt_of_lt_of_le hs.2 ht.2)
      have h1 : HasDerivAt (u x) (ut x s) s := ((hd x hx s hsT).1).hasDerivAt hmem
      have h2 := h1.pow 2
      rw [hGeq x hx s hsT]
      have he : 2 * (u x s * ut x s) = (2 : ℕ) * u x s ^ (2 - 1) * ut x s := by
        push_cast
        ring
      rw [he]
      exact h2
    have hint : IntervalIntegrable (fun s => 2 * G (x, s)) volume 0 t :=
      ((hsliceF' x).const_mul 2).intervalIntegrable _ _
    rw [integral_eq_sub_of_hasDerivAt_of_le ht.1 hcu hderiv hint]
  -- the energy difference as a single integral in `x`
  have hslice : ∀ s ∈ Icc (0 : ℝ) T, ContinuousOn (fun x => u x s) (Icc (0 : ℝ) 1) :=
    fun s hs x hx => ((hd x hx s hs).2.1).continuousWithinAt
  have i1 : IntervalIntegrable (fun x => u x t ^ 2) volume 0 1 :=
    ((hslice t ht).pow 2).intervalIntegrable_of_Icc zero_le_one
  have i2 : IntervalIntegrable (fun x => u x 0 ^ 2) volume 0 1 :=
    ((hslice 0 ⟨le_rfl, hT⟩).pow 2).intervalIntegrable_of_Icc zero_le_one
  have hEsub : energy u t - energy u 0 = ∫ x in (0 : ℝ)..1, (u x t ^ 2 - u x 0 ^ 2) := by
    rw [energy, energy, ← integral_sub i1 i2]
  have hcongr : (∫ x in (0 : ℝ)..1, (u x t ^ 2 - u x 0 ^ 2))
      = ∫ x in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, 2 * G (x, s) :=
    integral_congr fun x hx => (hinner x (by rwa [uIcc_of_le zero_le_one] at hx)).symm
  have hswap : (∫ x in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, 2 * G (x, s))
      = ∫ s in (0 : ℝ)..t, ∫ x in (0 : ℝ)..1, 2 * G (x, s) := by
    have hi : Integrable (Function.uncurry fun x s => 2 * G (x, s))
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) t))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact ((hcont.const_mul 2).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    have hfub := MeasureTheory.integral_integral_swap hi
    rw [integral_of_le zero_le_one, integral_of_le ht.1,
      show (fun x : ℝ => ∫ s in (0 : ℝ)..t, 2 * G (x, s))
          = fun x : ℝ => ∫ s in Ioc (0 : ℝ) t, 2 * G (x, s) from
        funext fun x => integral_of_le ht.1,
      show (fun s : ℝ => ∫ x in (0 : ℝ)..1, 2 * G (x, s))
          = fun s : ℝ => ∫ x in Ioc (0 : ℝ) 1, 2 * G (x, s) from
        funext fun s => integral_of_le zero_le_one]
    exact hfub
  rw [hEsub, hcongr, hswap]
  refine integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  rw [← intervalIntegral.integral_const_mul]
  refine integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  rw [hGeq x hx s hsT]

/-- The source `f` of a classical solution is continuous on the rectangle, being `u_t - ν u_xx`
there. -/
theorem IsClassicalSolutionIccWith.continuousOn_source
    (h : IsClassicalSolutionIccWith ν T f u₀ u ut ux uxx) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2 - ν * uxx p.1 p.2)
      (Icc 0 1 ×ˢ Icc 0 T) := h.2.1.sub (continuousOn_const.mul h.2.2.2.1)
  refine hc.congr ?_
  rintro ⟨x, s⟩ ⟨hx, hs⟩
  exact (h.1 x hx s hs).2.2.2.symm

/-- **The differential inequality behind the energy estimate** ([quarteroni2000numerical] §13.1):
`2 ∫₀¹ u u_t ≤ -2ν E(t) + F(t)/(2ν)`, with `γ = ν/C_P² = 2ν`. Writing `u_t = ν u_xx + f`,
integration by parts turns
`2ν ∫ u u_xx` into `-2ν ∫ (u_x)²`, Poincaré bounds that by `-4ν E`, and Cauchy–Schwarz followed by
Young's inequality ([quarteroni2000numerical] (12.40)) bounds `2 ∫ f u` by `2ν E + F/(2ν)`. -/
theorem IsClassicalSolutionIccWith.two_mul_integral_mul_le (hν : 0 < ν)
    (h : IsClassicalSolutionIccWith ν T f u₀ u ut ux uxx) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    (2 * ∫ x in (0 : ℝ)..1, u x s * ut x s)
      ≤ -(2 * ν) * energy u s + energy f s / (2 * ν) := by
  have hd := h.1
  have hmap : ContinuousOn (fun x : ℝ => (x, s)) (Icc (0 : ℝ) 1) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hmaps : MapsTo (fun x : ℝ => (x, s)) (Icc (0 : ℝ) 1) (Icc 0 1 ×ˢ Icc 0 T) :=
    fun x hx => ⟨hx, hs⟩
  have hcu : ContinuousOn (fun x => u x s) (Icc (0 : ℝ) 1) := fun x hx =>
    ((hd x hx s hs).2.1).continuousWithinAt
  have hcx : ContinuousOn (fun x => ux x s) (Icc (0 : ℝ) 1) := h.2.2.1.comp hmap hmaps
  have hcxx : ContinuousOn (fun x => uxx x s) (Icc (0 : ℝ) 1) := h.2.2.2.1.comp hmap hmaps
  have hcf : ContinuousOn (fun x => f x s) (Icc (0 : ℝ) 1) :=
    (h.continuousOn_source).comp hmap hmaps
  -- split `u u_t = ν u u_xx + f u`
  have hsplit : (∫ x in (0 : ℝ)..1, u x s * ut x s)
      = ν * (∫ x in (0 : ℝ)..1, uxx x s * u x s) + ∫ x in (0 : ℝ)..1, f x s * u x s := by
    have hcongr : ∀ x ∈ uIcc (0 : ℝ) 1,
        u x s * ut x s = ν * (uxx x s * u x s) + f x s * u x s := by
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      rw [← (hd x hx s hs).2.2.2]
      ring
    have ia : IntervalIntegrable (fun x => ν * (uxx x s * u x s)) volume 0 1 :=
      ((continuousOn_const.mul (hcxx.mul hcu)).intervalIntegrable_of_Icc zero_le_one)
    have ib : IntervalIntegrable (fun x => f x s * u x s) volume 0 1 :=
      ((hcf.mul hcu).intervalIntegrable_of_Icc zero_le_one)
    rw [integral_congr hcongr, integral_add ia ib, intervalIntegral.integral_const_mul]
  -- integration by parts and Poincaré
  have hibp := h.integral_mul_eq_neg_integral_sq hs
  have hpoin : energy u s ≤ 1 / 2 * ∫ x in (0 : ℝ)..1, ux x s ^ 2 := by
    have := intervalIntegral.integral_sq_le_of_hasDerivAt_of_left_eq_zero zero_le_one hcu hcx
      (fun x hx => ((hd x (Ioo_subset_Icc_self hx) s hs).2.1).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      ((h.2.2.2.2.1 s hs).1)
    norm_num at this
    exact this
  -- Cauchy–Schwarz and Young
  have hcs : (∫ x in (0 : ℝ)..1, f x s * u x s) ^ 2 ≤ energy f s * energy u s :=
    intervalIntegral.sq_integral_mul_le_of_continuousOn zero_le_one hcf hcu
  have hFnn : 0 ≤ energy f s := integral_nonneg zero_le_one fun x _ => sq_nonneg _
  have hEnn : 0 ≤ energy u s := integral_nonneg zero_le_one fun x _ => sq_nonneg _
  have hyoung : 2 * (∫ x in (0 : ℝ)..1, f x s * u x s)
      ≤ 2 * ν * energy u s + energy f s / (2 * ν) := by
    have hS : 0 ≤ 2 * ν * energy u s + energy f s / (2 * ν) := by positivity
    have hid : (2 * ν * energy u s + energy f s / (2 * ν)) ^ 2
        = 4 * (energy f s * energy u s)
          + (2 * ν * energy u s - energy f s / (2 * ν)) ^ 2 := by
      field_simp
      ring
    have hsq : (2 * ∫ x in (0 : ℝ)..1, f x s * u x s) ^ 2
        ≤ (2 * ν * energy u s + energy f s / (2 * ν)) ^ 2 := by
      rw [hid]
      nlinarith [hcs, sq_nonneg (2 * ν * energy u s - energy f s / (2 * ν))]
    nlinarith [hsq, hS]
  have hgrad : 0 ≤ ∫ x in (0 : ℝ)..1, ux x s ^ 2 := integral_nonneg zero_le_one fun x _ =>
    sq_nonneg _
  rw [hsplit, hibp]
  nlinarith [hpoin, hyoung, hν, hgrad]

/-- **The a priori energy estimate** ([quarteroni2000numerical] (13.7)): for a classical
solution of the heat equation on `[0, 1] × [0, T]` with `ν > 0`,

`E(t) ≤ e^{-γ t} E(0) + (1/γ) ∫₀ᵗ e^{γ(s-t)} F(s) ds`, `γ = ν / C_P² = 2ν`,

with `E(t) = ∫₀¹ u(x, t)² dx` and `F(t) = ∫₀¹ f(x, t)² dx`; in particular, for `f ≡ 0` the energy
decays exponentially. The source multiplies the equation by `u`, integrates in `x`, integrates by
parts, and applies Cauchy–Schwarz, Poincaré ([quarteroni2000numerical] (12.16)), Young and the
differential Gronwall lemma;
the steps are `Heat.IsClassicalSolutionIccWith.integral_mul_eq_neg_integral_sq`,
`intervalIntegral.sq_integral_mul_le_of_continuousOn`,
`intervalIntegral.integral_sq_le_of_hasDerivAt_of_left_eq_zero`,
`Heat.IsClassicalSolutionIccWith.two_mul_integral_mul_le` and
`Gronwall.le_exp_neg_mul_add_integral_of_hasDerivWithinAt_le`. The one step that is *not* the
book's is "interchanging differentiation and integration": `E` is exhibited as a primitive
(`Heat.IsClassicalSolutionIccWith.energy_sub_eq`, by Fubini) rather than differentiated under the
integral sign, because the latter would need a two-sided derivative at `t = 0`. -/
theorem IsClassicalSolutionIcc.energy_le (hν : 0 < ν) (hT : 0 ≤ T)
    (hu : IsClassicalSolutionIcc ν T f u₀ u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    energy u t ≤ Real.exp (-(2 * ν) * t) * energy u 0
      + ∫ s in (0 : ℝ)..t, Real.exp (2 * ν * (s - t)) * (energy f s / (2 * ν)) := by
  obtain ⟨ut, ux, uxx, h⟩ := hu
  set p : ℝ → ℝ := fun s => 2 * ∫ x in (0 : ℝ)..1, u x s * ut x s with hp
  set g : ℝ → ℝ := fun s => energy f s / (2 * ν) with hg
  set Gu : ℝ × ℝ → ℝ := clampRect T (fun y r => u y r * ut y r) with hGu
  set Gf : ℝ × ℝ → ℝ := clampRect T (fun y r => f y r ^ 2) with hGf
  have hcont : Continuous Gu := continuous_clampRect hT ((h.continuousOn hT).mul h.2.1)
  have hcontf : Continuous Gf := continuous_clampRect hT ((h.continuousOn_source).pow 2)
  -- continuity of the two data
  have hpc : ContinuousOn p (Icc (0 : ℝ) T) := by
    have hglob : Continuous fun s : ℝ => 2 * ∫ x in (0 : ℝ)..1, Gu (x, s) := by
      refine Continuous.const_mul ?_ 2
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun s x => Gu (x, s)) (hcont.comp (continuous_snd.prodMk continuous_fst)) 0 1
    refine hglob.continuousOn.congr fun s hs => ?_
    change 2 * (∫ x in (0 : ℝ)..1, u x s * ut x s) = _
    refine congrArg (2 * ·) (integral_congr fun x hx => ?_).symm
    rw [uIcc_of_le zero_le_one] at hx
    exact clampRect_eq _ hx hs
  have hgc : ContinuousOn g (Icc (0 : ℝ) T) := by
    have hglob : Continuous fun s : ℝ => (∫ x in (0 : ℝ)..1, Gf (x, s)) / (2 * ν) := by
      refine Continuous.div_const ?_ _
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun s x => Gf (x, s)) (hcontf.comp (continuous_snd.prodMk continuous_fst)) 0 1
    refine hglob.continuousOn.congr fun s hs => ?_
    change energy f s / (2 * ν) = _
    rw [energy]
    refine congrArg (· / (2 * ν)) (integral_congr fun x hx => ?_).symm
    rw [uIcc_of_le zero_le_one] at hx
    exact clampRect_eq _ hx hs
  -- the energy as a primitive
  have hEeq : ∀ s ∈ Icc (0 : ℝ) T, energy u s = energy u 0 + ∫ r in (0 : ℝ)..s, p r := by
    intro s hs
    have := h.energy_sub_eq hT hs
    rw [hp]
    linarith [this]
  have hEc : ContinuousOn (energy u) (Icc (0 : ℝ) T) :=
    ((intervalIntegral.continuousOn_integral_Icc hpc).const_add (energy u 0)).congr fun s hs =>
      hEeq s hs
  have hE' : ∀ s ∈ Ico (0 : ℝ) T, HasDerivWithinAt (energy u) (p s) (Ici s) s := by
    intro s hs
    have h1 : HasDerivWithinAt (fun r => energy u 0 + ∫ r' in (0 : ℝ)..r, p r') (p s) (Ici s) s :=
      (intervalIntegral.hasDerivWithinAt_integral_Ici hpc hs).const_add _
    have h2 : HasDerivWithinAt (energy u) (p s) (Icc s T) s := by
      refine (h1.mono Icc_subset_Ici_self).congr (fun y hy => ?_) ?_
      · exact hEeq y ⟨le_trans hs.1 hy.1, hy.2⟩
      · exact hEeq s ⟨hs.1, hs.2.le⟩
    exact h2.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ⟨le_rfl, hs.2⟩)
  have hbound : ∀ s ∈ Ico (0 : ℝ) T, p s ≤ -(2 * ν) * energy u s + g s := fun s hs =>
    h.two_mul_integral_mul_le hν (Ico_subset_Icc_self hs)
  have hres := Gronwall.le_exp_neg_mul_add_integral_of_hasDerivWithinAt_le hEc hE' hgc hbound ht
  rw [sub_zero] at hres
  exact hres

end Energy

end Heat
