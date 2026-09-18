import Numlib.Analysis.Calculus.DerivativeTest
import Numlib.Variational.EllipticInterval.BoundaryConditions

/-!
# The maximum principle for the two-point boundary value problem

The maximum principle of [brezis2011functional] §8.5: Theorem 8.19 (the Dirichlet problem, by
Stampacchia's truncation method), Corollary 8.20, Proposition 8.21 (the Neumann problem),
Remarks 26–27 (the classical route through the second-derivative test at an interior or
endpoint maximum) and Remark 28 (the problem on `ℝ`).

## Main definitions

* `EllipticInterval.truncation`, Stampacchia's truncation `G(t) = (max t 0)²`: `C¹`, vanishing on
  `(−∞, 0]`, with `t G(t) ≥ 0` and `G(t) = 0 ↔ t ≤ 0`;
* `EllipticInterval.truncationElem hab u K`, the element `G(u − K)` of `H¹(a, b)` (the chain rule
  `SobolevIntervalLp.memSobolevIntervalLp_comp_of_bounded`), which lies in `H_0^1(a, b)` when
  `u ≤ K` at the endpoints (`truncationElem_mem_sobolevIntervalZero`).

## Main statements

* `EllipticInterval.integral_eq_zero_of_truncation` (the energy identity of Stampacchia's method,
  for an arbitrary measure): testing `∫ (α u' v' + γ u v) = ∫ f v` with `v = G(u − K)` and
  `f ≤ K γ` gives `∫ α u'² G'(u − K) = 0` and `∫ γ (u − K) G(u − K) = 0`.
* `EllipticInterval.rep_le_of_le_of_isWeakSolution` (**Theorem 8.19**, for the general operator
  `−(α u')' + γ u = f` with `α ≥ α₀ > 0`, `γ ≥ 0`): a weak solution with `u ≤ K` at the endpoints
  and `f ≤ K γ` almost everywhere satisfies `u ≤ K` on `[a, b]`; `rep_ge_of_ge_of_isWeakSolution`
  is the lower bound, and `abs_rep_le_of_isWeakSolution`, `rep_nonneg_of_isWeakSolution`,
  `abs_rep_le_max_of_isWeakSolution` are **Corollary 8.20**.
* `EllipticInterval.rep_le_of_le_of_isWeakSolution_neumann` (**Proposition 8.21**) and its lower
  bound, for the Neumann problem.
* `EllipticInterval.le_of_contDiffMapIcc_classical` (Remark 26) and
  `le_of_contDiffMapIcc_classical_neumann` (Remark 27): the classical maximum principle for `C²`
  solutions, through the second-derivative test `IsLocalMax.deriv_deriv_nonpos` and its one-sided
  endpoint form.
* `EllipticInterval.Line.rep_le_of_le`, `Line.le_rep_of_le` (Remark 28): the maximum principle on
  `ℝ`.

## Design

* The truncation is `G(t) = (max t 0)²`, `C¹` with `G'(t) = 2 max t 0`. The book allows any
  `C¹` function vanishing on `(−∞, 0]` and strictly increasing on `(0, ∞)`.
* The general form `γ ≥ 0` of Theorem 8.19 is proved from the vanishing of `∫ α u'² G'(u − K)`:
  then `G(u − K) ∈ H_0^1` has weak derivative `G'(u − K) u' = 0`, so it is constant (du
  Bois-Reymond), hence `0`. The book's argument at `γ = 1` uses instead the vanishing of
  `∫ (u − K) G(u − K)`, which is what the Neumann and the whole-line versions use, where no
  boundary condition is available.
* Remark 28 needs `0 ≤ K` for `G(u − K)` to lie in `H¹(ℝ)` (`G(−K) = 0`); this costs nothing,
  since `f ≤ K` almost everywhere with `f ∈ L²(ℝ)` forces `0 ≤ K` — but the hypothesis is stated.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace EllipticInterval

/-! ### Stampacchia's truncation -/

/-- **Stampacchia's truncation function** `G(t) = (max t 0)²`: of class `C¹`, vanishing for
`t ≤ 0` and strictly increasing on `[0, ∞)` — the function `G` of the proof of
[brezis2011functional] Theorem 8.19. -/
def truncation (t : ℝ) : ℝ := max t 0 ^ 2

/-- `G(t) = 0` for `t ≤ 0`. -/
theorem truncation_eq_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : truncation t = 0 := by
  rw [truncation, max_eq_right h]; ring

/-- `G(t) = t²` for `t ≥ 0`. -/
theorem truncation_of_nonneg {t : ℝ} (h : 0 ≤ t) : truncation t = t ^ 2 := by
  rw [truncation, max_eq_left h]

/-- `G(0) = 0`. -/
@[simp]
theorem truncation_zero : truncation 0 = 0 := truncation_eq_zero_of_nonpos le_rfl

/-- `G ≥ 0`. -/
theorem truncation_nonneg (t : ℝ) : 0 ≤ truncation t := sq_nonneg _

/-- `t G(t) ≥ 0`. -/
theorem mul_truncation_nonneg (t : ℝ) : 0 ≤ t * truncation t := by
  rcases le_or_gt t 0 with h | h
  · rw [truncation_eq_zero_of_nonpos h, mul_zero]
  · exact mul_nonneg h.le (truncation_nonneg t)

/-- `G(t) = 0` exactly when `t ≤ 0`. -/
theorem truncation_eq_zero_iff {t : ℝ} : truncation t = 0 ↔ t ≤ 0 := by
  refine ⟨fun h ↦ ?_, truncation_eq_zero_of_nonpos⟩
  by_contra ht
  rw [not_le] at ht
  rw [truncation_of_nonneg ht.le] at h
  exact ht.ne' (pow_eq_zero_iff two_ne_zero |>.1 h)

/-- `t G(t) = 0` exactly when `t ≤ 0`. -/
theorem mul_truncation_eq_zero_iff {t : ℝ} : t * truncation t = 0 ↔ t ≤ 0 := by
  rw [mul_eq_zero, truncation_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h.le
    · exact h
  · exact fun h ↦ Or.inr h

/-- `G` is differentiable with `G'(t) = 2 max t 0`; at `t = 0` by the squeeze `|G(h)| ≤ h²`. -/
theorem hasDerivAt_truncation (t : ℝ) : HasDerivAt truncation (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h : truncation =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      exact truncation_eq_zero_of_nonpos hy.le
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h
  · rw [max_self, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [truncation_zero, zero_add, smul_zero, sub_zero]
    refine Asymptotics.isLittleO_iff.2 fun c hc ↦ ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (truncation_nonneg h)]
    have h1 : max h 0 ≤ |h| := max_le (le_abs_self h) (abs_nonneg h)
    calc truncation h = max h 0 ^ 2 := rfl
      _ ≤ |h| ^ 2 := pow_le_pow_left₀ (le_max_right h 0) h1 2
      _ = |h| * |h| := sq _
      _ ≤ c * |h| := by gcongr
  · have h : truncation =ᶠ[𝓝 t] fun y ↦ y ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      rw [truncation, max_eq_left hy.le]
    rw [max_eq_left ht.le]
    have := (hasDerivAt_pow 2 t).congr_of_eventuallyEq h
    simpa using this

/-- The derivative of the truncation. -/
theorem deriv_truncation : _root_.deriv truncation = fun t ↦ 2 * max t 0 :=
  funext fun t ↦ (hasDerivAt_truncation t).deriv

/-- The derivative of the truncation is nonnegative. -/
theorem deriv_truncation_nonneg (t : ℝ) : 0 ≤ _root_.deriv truncation t := by
  rw [deriv_truncation]
  exact mul_nonneg two_pos.le (le_max_right t 0)

/-- `G` is of class `C¹`. -/
theorem contDiff_truncation : ContDiff ℝ 1 truncation :=
  contDiff_one_iff_deriv.2 ⟨fun t ↦ (hasDerivAt_truncation t).differentiableAt, by
    rw [deriv_truncation]; fun_prop⟩

/-- The shifted truncation `s ↦ G(s − K)` is `C¹`. -/
theorem contDiff_truncation_sub (K : ℝ) : ContDiff ℝ 1 fun s ↦ truncation (s - K) :=
  contDiff_truncation.comp (contDiff_id.sub contDiff_const)

/-- The derivative of the shifted truncation. -/
theorem deriv_truncation_sub (K s : ℝ) :
    _root_.deriv (fun s ↦ truncation (s - K)) s = 2 * max (s - K) 0 := by
  exact (hasDerivAt_truncation (s - K)).comp_sub_const.deriv

/-! ### Two continuity lemmas -/

/-- A function continuous on `[a, b]` and at most `K` almost everywhere on `(a, b)` is at most
`K` on `[a, b]`: `max g K` and the constant `K` are continuous and agree almost everywhere. -/
theorem le_on_Icc_of_ae_le {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    {K : ℝ} (h : ∀ᵐ x ∂(volume.restrict (Ioo a b)), g x ≤ K) : ∀ x ∈ Icc a b, g x ≤ K := by
  have hc : ContinuousOn (fun x ↦ max (g x) K) (Icc a b) :=
    continuous_max.comp_continuousOn (hg.prodMk continuousOn_const)
  have e := eqOn_Icc_of_ae_eq hab hc continuousOn_const
    (g₂ := fun _ ↦ K) (by filter_upwards [h] with x hx; exact max_eq_right hx)
  intro x hx
  have : max (g x) K = K := e hx
  rw [← this]
  exact le_max_left _ _

/-- A continuous function on `ℝ` that is at most `K` almost everywhere is at most `K`
everywhere. -/
theorem le_of_ae_le {g : ℝ → ℝ} (hg : Continuous g) {K : ℝ} (h : ∀ᵐ x, g x ≤ K) : ∀ x, g x ≤ K := by
  have e : (fun x ↦ max (g x) K) = fun _ ↦ K :=
    ((hg.max continuous_const).ae_eq_iff_eq (μ := volume) continuous_const).1
      (by filter_upwards [h] with x hx; exact max_eq_right hx)
  intro x
  have : max (g x) K = K := congrFun e x
  rw [← this]
  exact le_max_left _ _

/-! ### The energy identity of Stampacchia's method -/

/-- **The energy identity behind Stampacchia's truncation method**, for an arbitrary measure:
if `∫ (α u' v' + γ u v) = ∫ f v` with `v = G(u − K)`, `v' = G'(u − K) u'`, `α ≥ 0`, `γ ≥ 0` and
`f ≤ K γ` almost everywhere, then `∫ α u' v' = 0` and `∫ γ (u − K) v = 0`, both integrands being
nonnegative: subtracting `K ∫ γ v` from both sides,
`∫ α u'² G'(u − K) + ∫ γ (u − K) G(u − K) = ∫ (f − K γ) G(u − K) ≤ 0`. -/
theorem integral_eq_zero_of_truncation {μ : Measure ℝ} {α γ f u₀ u₁ v₀ v₁ : ℝ → ℝ} {K : ℝ}
    (hα : ∀ᵐ x ∂μ, 0 ≤ α x) (hγ : ∀ᵐ x ∂μ, 0 ≤ γ x) (hf : ∀ᵐ x ∂μ, f x ≤ K * γ x)
    (hv₀ : v₀ =ᵐ[μ] fun x ↦ truncation (u₀ x - K))
    (hv₁ : v₁ =ᵐ[μ] fun x ↦ 2 * max (u₀ x - K) 0 * u₁ x)
    (i1 : Integrable (fun x ↦ α x * u₁ x * v₁ x) μ) (i2 : Integrable (fun x ↦ γ x * u₀ x * v₀ x) μ)
    (i3 : Integrable (fun x ↦ f x * v₀ x) μ) (i4 : Integrable (fun x ↦ γ x * v₀ x) μ)
    (heq : ∫ x, (α x * u₁ x * v₁ x + γ x * u₀ x * v₀ x) ∂μ = ∫ x, f x * v₀ x ∂μ) :
    (∀ᵐ x ∂μ, α x * u₁ x * v₁ x = 0) ∧ ∀ᵐ x ∂μ, γ x * (u₀ x - K) * v₀ x = 0 := by
  -- the three integrals and their signs
  have hA : ∀ᵐ x ∂μ, 0 ≤ α x * u₁ x * v₁ x := by
    filter_upwards [hα, hv₁] with x h1 h2
    rw [h2, show α x * u₁ x * (2 * max (u₀ x - K) 0 * u₁ x)
      = α x * (2 * max (u₀ x - K) 0) * (u₁ x * u₁ x) by ring]
    exact mul_nonneg (mul_nonneg h1 (mul_nonneg two_pos.le (le_max_right _ _))) (mul_self_nonneg _)
  have hB : ∀ᵐ x ∂μ, 0 ≤ γ x * (u₀ x - K) * v₀ x := by
    filter_upwards [hγ, hv₀] with x h1 h2
    rw [h2, mul_assoc]
    exact mul_nonneg h1 (mul_truncation_nonneg _)
  have hC : ∀ᵐ x ∂μ, (f x - K * γ x) * v₀ x ≤ 0 := by
    filter_upwards [hf, hv₀] with x h1 h2
    rw [h2]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (truncation_nonneg _)
  have iB : Integrable (fun x ↦ γ x * (u₀ x - K) * v₀ x) μ :=
    (i2.sub (i4.const_mul K)).congr (Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply]; ring)
  have iC : Integrable (fun x ↦ (f x - K * γ x) * v₀ x) μ :=
    (i3.sub (i4.const_mul K)).congr (Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply]; ring)
  have eB : ∫ x, γ x * (u₀ x - K) * v₀ x ∂μ
      = (∫ x, γ x * u₀ x * v₀ x ∂μ) - K * ∫ x, γ x * v₀ x ∂μ := by
    rw [← integral_const_mul, ← integral_sub i2 (i4.const_mul K)]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  have eC : ∫ x, (f x - K * γ x) * v₀ x ∂μ
      = (∫ x, f x * v₀ x ∂μ) - K * ∫ x, γ x * v₀ x ∂μ := by
    rw [← integral_const_mul, ← integral_sub i3 (i4.const_mul K)]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
  rw [integral_add i1 i2] at heq
  have hA0 := integral_nonneg_of_ae hA
  have hB0 := integral_nonneg_of_ae hB
  have hC0 := integral_nonpos_of_ae hC
  have hAzero : ∫ x, α x * u₁ x * v₁ x ∂μ = 0 := by linarith
  have hBzero : ∫ x, γ x * (u₀ x - K) * v₀ x ∂μ = 0 := by linarith
  exact ⟨(integral_eq_zero_iff_of_nonneg_ae hA i1).1 hAzero,
    (integral_eq_zero_iff_of_nonneg_ae hB iB).1 hBzero⟩

/-! ### The truncated element `G(u − K)` of `H¹(a, b)` -/

variable {a b : ℝ}

/-- `G(ũ − K)` lies in `L²(a, b)`. -/
theorem memLp_truncation_rep (hab : a < b) (u : SobolevInterval 1 a b) (K : ℝ) :
    MemLp (fun t ↦ truncation (SobolevIntervalLp.rep u t - K)) 2 (volume.restrict (Ioo a b)) :=
  (memSobolevIntervalLp_one_iff.1 (SobolevIntervalLp.memSobolevIntervalLp_comp_of_bounded hab u
    (contDiff_truncation_sub K)).1).1

open SobolevInterval in
/-- `G'(ũ − K) u' = 2 max (ũ − K) 0 · u'` lies in `L²(a, b)`. -/
theorem memLp_deriv_truncation_rep_mul (u : SobolevInterval 1 a b) (K : ℝ) :
    MemLp (fun t ↦ 2 * max (SobolevIntervalLp.rep u t - K) 0 * deriv u 1 t) 2
      (volume.restrict (Ioo a b)) := by
  have := SobolevIntervalLp.memLp_deriv_comp (SobolevIntervalLp.ordConnected_coe_Ioo a b) u
    (contDiff_truncation_sub K)
  simp only [deriv_truncation_sub] at this
  exact this

open SobolevInterval in
/-- The chain rule for `G(ũ − K)`: its weak derivative is `2 max (ũ − K) 0 · u'`. -/
theorem hasWeakDerivOn_truncation_rep (hab : a < b) (u : SobolevInterval 1 a b) (K : ℝ) :
    HasWeakDerivOn (fun t ↦ truncation (SobolevIntervalLp.rep u t - K))
      (fun t ↦ 2 * max (SobolevIntervalLp.rep u t - K) 0 * deriv u 1 t) (Opens.Ioo a b) := by
  have := (SobolevIntervalLp.memSobolevIntervalLp_comp_of_bounded hab u
    (contDiff_truncation_sub K)).2
  simp only [deriv_truncation_sub] at this
  exact this

/-- **The truncation `G(u − K)` of `u ∈ H¹(a, b)`** as an element of `H¹(a, b)`, by the chain
rule (Corollary 8.11 on a bounded interval): its function is `G(ũ − K)` and its weak derivative
`G'(ũ − K) u' = 2 max (ũ − K) 0 · u'`. -/
def truncationElem (hab : a < b) (u : SobolevInterval 1 a b) (K : ℝ) : SobolevInterval 1 a b :=
  SobolevIntervalLp.mk
    ![(memLp_truncation_rep hab u K).toLp (fun t ↦ truncation (SobolevIntervalLp.rep u t - K)),
      (memLp_deriv_truncation_rep_mul u K).toLp
        (fun t ↦ 2 * max (SobolevIntervalLp.rep u t - K) 0 * SobolevIntervalLp.deriv u 1 t)]
    fun j ↦ by
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := Opens.Ioo a b) one_le_two)
    · exact (hasWeakDerivOn_truncation_rep hab u K).congr_ae
        (memLp_truncation_rep hab u K).coeFn_toLp.symm
        (memLp_deriv_truncation_rep_mul u K).coeFn_toLp.symm

open SobolevInterval in
/-- The function of the truncated element. -/
theorem fn_truncationElem (hab : a < b) (u : SobolevInterval 1 a b) (K : ℝ) :
    fn (truncationElem hab u K) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ truncation (SobolevIntervalLp.rep u t - K) :=
  (memLp_truncation_rep hab u K).coeFn_toLp

open SobolevInterval in
/-- The weak derivative of the truncated element. -/
theorem coeFn_deriv_truncationElem_one (hab : a < b) (u : SobolevInterval 1 a b) (K : ℝ) :
    ⇑(deriv (truncationElem hab u K) 1) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ 2 * max (SobolevIntervalLp.rep u t - K) 0 * deriv u 1 t :=
  (memLp_deriv_truncation_rep_mul u K).coeFn_toLp

open SobolevInterval in
/-- The continuous representative of the truncated element is `G(ũ − K)` on `[a, b]`. -/
theorem rep_truncationElem (hab : a < b) (u : SobolevInterval 1 a b) (K : ℝ) :
    EqOn (rep (truncationElem hab u K)) (fun t ↦ truncation (rep u t - K)) (Icc a b) := by
  refine rep_eq_of_continuousOn hab _
    ((contDiff_truncation_sub K).continuous.comp_continuousOn (continuousOn_rep hab.le u)) ?_
  filter_upwards [fn_truncationElem hab u K, ae_restrict_mem measurableSet_Ioo] with t h1 h2
  rw [h1, SobolevInterval.rep_eq_repLp hab u (Ioo_subset_Icc_self h2)]

open SobolevInterval in
/-- **The truncated element lies in `H_0^1(a, b)` when `u ≤ K` at the endpoints**
(`G(u(a) − K) = 0` and `G(u(b) − K) = 0`). -/
theorem truncationElem_mem_sobolevIntervalZero (hab : a < b) {u : SobolevInterval 1 a b} {K : ℝ}
    (hKa : rep u a ≤ K) (hKb : rep u b ≤ K) : truncationElem hab u K ∈ SobolevIntervalZero a b :=
  SobolevIntervalZero.mem_of_rep_eq_zero hab _
    (by rw [rep_truncationElem hab u K (left_mem_Icc.2 hab.le)]
        exact truncation_eq_zero_of_nonpos (by linarith))
    (by rw [rep_truncationElem hab u K (right_mem_Icc.2 hab.le)]
        exact truncation_eq_zero_of_nonpos (by linarith))

open SobolevInterval in
/-- The energy identity of Stampacchia's method on `(a, b)`, for the form `form a b α 0 γ` tested
with `v = G(u − K)`. -/
theorem integral_eq_zero_of_form_truncationElem (hab : a < b)
    (αL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ αL x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γL x)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {u : SobolevInterval 1 a b} {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), f x ≤ K * γL x)
    (hu : form a b αL 0 γL u (truncationElem hab u K) = load a b f (truncationElem hab u K)) :
    (∀ᵐ x ∂(volume.restrict (Ioo a b)),
        αL x * deriv u 1 x * deriv (truncationElem hab u K) 1 x = 0) ∧
      ∀ᵐ x ∂(volume.restrict (Ioo a b)),
        γL x * (deriv u 0 x - K) * deriv (truncationElem hab u K) 0 x = 0 := by
  set v := truncationElem hab u K with hvdef
  have hv₀ : (deriv v 0 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      fun x ↦ truncation (deriv u 0 x - K) := by
    rw [deriv_zero]
    filter_upwards [fn_truncationElem hab u K, SobolevInterval.fn_ae_eq_repLp u] with x h1 h2
    rw [h1, deriv_zero, h2]
  have hv₁ : (deriv v 1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      fun x ↦ 2 * max (deriv u 0 x - K) 0 * deriv u 1 x := by
    filter_upwards [coeFn_deriv_truncationElem_one hab u K, SobolevInterval.fn_ae_eq_repLp u]
      with x h1 h2
    rw [h1, deriv_zero, h2]
  have i4 : Integrable (fun x ↦ γL x * deriv v 0 x) (volume.restrict (Ioo a b)) :=
    ((Lp.memLp (mulL γL (deriv v 0))).integrable one_le_two).congr (coeFn_mulL γL (deriv v 0))
  have i3 : Integrable (fun x ↦ f x * deriv v 0 x) (volume.restrict (Ioo a b)) :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mul (r := 1)
      (hpqr := Line.holderTriple_two_two_one) (Lp.memLp (deriv v 0)))
  refine integral_eq_zero_of_truncation hα hγ hf hv₀ hv₁ (integrable_mul_mul αL _ _)
    (integrable_mul_mul γL _ _) i3 i4 ?_
  rw [form_apply, load_apply] at hu
  rw [← hu]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo a b))] with x hx
  rw [hx, Pi.zero_apply]
  ring

/-! ### Theorem 8.19: the maximum principle for the Dirichlet problem -/

open SobolevInterval in
/-- **Theorem 8.19 of [brezis2011functional] (the maximum principle)**, for the operator
`−(α u')' + γ u` with `α ≥ α₀ > 0` and `γ ≥ 0`: if `u ∈ H¹(a, b)` satisfies the weak equation
`∫ (α u' v' + γ u v) = ∫ f v` for every `v ∈ H_0^1(a, b)`, `u(a) ≤ K`, `u(b) ≤ K` and `f ≤ K γ`
almost everywhere, then `u ≤ K` on `[a, b]`. The book's problem `−u'' + u = f` is `α = γ = 1`,
where the hypothesis on `f` reads `f ≤ K` (so `K = max (α, β, ess sup f)` when that is finite).
Stampacchia's method: `v = G(u − K) ∈ H_0^1` in the weak equation gives
`∫ α u'² G'(u − K) = 0`, so `v' = G'(u − K) u' = 0` and `v` is constant (du Bois-Reymond), hence
`0` by its boundary values. -/
theorem rep_le_of_le_of_isWeakSolution (hab : a < b) (αL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    {α₀ : ℝ} (hα₀ : 0 < α₀) (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ αL x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γL x) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, form a b αL 0 γL u v = load a b f v) {K : ℝ}
    (hKa : rep u a ≤ K) (hKb : rep u b ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), f x ≤ K * γL x) :
    ∀ x ∈ Icc a b, rep u x ≤ K := by
  set v := truncationElem hab u K with hvdef
  have hvmem := truncationElem_mem_sobolevIntervalZero hab hKa hKb
  obtain ⟨hA, -⟩ := integral_eq_zero_of_form_truncationElem hab αL γL
    (hα.mono fun x hx ↦ hα₀.le.trans hx) hγ f hf (hu v hvmem)
  -- `v' = 0` almost everywhere
  have hv₁ : (deriv v 1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ 0 := by
    filter_upwards [hA, hα, coeFn_deriv_truncationElem_one hab u K] with x h1 h2 h3
    have hαx : 0 < αL x := hα₀.trans_le h2
    rw [h3] at h1
    rw [h3]
    change 2 * max (SobolevIntervalLp.rep u x - K) 0 * deriv u 1 x = 0
    rcases mul_eq_zero.1 h1 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hαx.ne'
      · rw [h', mul_zero]
    · exact h
  -- hence `v` is constant, and the constant is `v(a) = 0`
  obtain ⟨c, hc⟩ := HasWeakDerivOn.exists_ae_eq_const (SobolevIntervalLp.ordConnected_coe_Ioo a b)
    ((hasWeakDerivOn_fn v).congr_ae EventuallyEq.rfl hv₁)
  have hrep : EqOn (rep v) (fun _ ↦ c) (Icc a b) :=
    rep_eq_of_continuousOn hab v continuousOn_const hc
  have hc0 : c = 0 := by
    have h1 := hrep (left_mem_Icc.2 hab.le)
    rw [rep_truncationElem hab u K (left_mem_Icc.2 hab.le)] at h1
    simp only at h1
    rw [← h1]
    exact truncation_eq_zero_of_nonpos (by linarith)
  intro x hx
  have h := hrep hx
  rw [rep_truncationElem hab u K hx, hc0] at h
  simp only at h
  linarith [truncation_eq_zero_iff.1 h]

/-- The load of `−f` is `−load f`. -/
theorem load_neg (f : Lp ℝ 2 (volume.restrict (Ioo a b))) : load a b (-f) = -load a b f := by
  ext v
  rw [neg_apply, load_apply_inner, load_apply_inner, inner_neg_left]

/-- The continuous representative of `−u`. -/
theorem _root_.SobolevInterval.rep_neg (hab : a < b) (u : SobolevInterval 1 a b) :
    EqOn (SobolevInterval.rep (-u)) (-SobolevInterval.rep u) (Icc a b) := by
  have := SobolevInterval.rep_smul hab (-1) u
  rw [neg_one_smul] at this
  refine this.trans fun x _ ↦ ?_
  simp

open SobolevInterval in
/-- **Theorem 8.19, the lower bound**: under the weak equation, `K ≤ u(a)`, `K ≤ u(b)` and
`K γ ≤ f` almost everywhere imply `K ≤ u` on `[a, b]` — the upper bound applied to `−u`. -/
theorem rep_ge_of_ge_of_isWeakSolution (hab : a < b) (αL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    {α₀ : ℝ} (hα₀ : 0 < α₀) (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ αL x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γL x) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, form a b αL 0 γL u v = load a b f v) {K : ℝ}
    (hKa : K ≤ rep u a) (hKb : K ≤ rep u b)
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), K * γL x ≤ f x) :
    ∀ x ∈ Icc a b, K ≤ rep u x := by
  have hu' : ∀ v ∈ SobolevIntervalZero a b, form a b αL 0 γL (-u) v = load a b (-f) v :=
    fun v hv ↦ by rw [map_neg, neg_apply, hu v hv, load_neg, neg_apply]
  have h := rep_le_of_le_of_isWeakSolution hab αL γL hα₀ hα hγ (-f) hu' (K := -K)
    (by rw [SobolevInterval.rep_neg hab u (left_mem_Icc.2 hab.le)]
        simp only [Pi.neg_apply]; linarith)
    (by rw [SobolevInterval.rep_neg hab u (right_mem_Icc.2 hab.le)]
        simp only [Pi.neg_apply]; linarith)
    (by filter_upwards [hf, Lp.coeFn_neg f] with x h1 h2; rw [h2, Pi.neg_apply]; linarith)
  intro x hx
  have := h x hx
  rw [SobolevInterval.rep_neg hab u hx] at this
  simp only [Pi.neg_apply] at this
  linarith

/-! ### Corollary 8.20 -/

open SobolevInterval in
/-- **Corollary 8.20 (i) of [brezis2011functional]**: for the model problem `−u'' + u = f`, if
`u ≥ 0` at the endpoints and `f ≥ 0` almost everywhere, then `u ≥ 0` on `[a, b]`. -/
theorem rep_nonneg_of_isWeakSolution (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, modelForm a b u v = load a b f v)
    (hKa : 0 ≤ rep u a) (hKb : 0 ≤ rep u b) (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ f x) :
    ∀ x ∈ Icc a b, 0 ≤ rep u x :=
  rep_ge_of_ge_of_isWeakSolution hab (constLinf a b 1) (constLinf a b 1) one_pos
    (by filter_upwards [coeFn_constLinf a b 1] with x hx; rw [hx])
    (by filter_upwards [coeFn_constLinf a b 1] with x hx; rw [hx]; exact zero_le_one) f hu hKa hKb
    (by filter_upwards [hf] with x hx; rw [zero_mul]; exact hx)

open SobolevInterval in
/-- **Corollary 8.20 (ii) of [brezis2011functional]**: for the model problem `−u'' + u = f`, if
`u = 0` at the endpoints and `|f| ≤ M` almost everywhere, then `|u| ≤ M` on `[a, b]`, that is,
`‖u‖_∞ ≤ ‖f‖_∞`. -/
theorem abs_rep_le_of_isWeakSolution (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, modelForm a b u v = load a b f v)
    (hKa : rep u a = 0) (hKb : rep u b = 0) {M : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), |f x| ≤ M) :
    ∀ x ∈ Icc a b, |rep u x| ≤ M := by
  have hM : 0 ≤ M := by
    have hne : (volume.restrict (Ioo a b)) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
      linarith
    have : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.2 hne
    obtain ⟨x, hx⟩ := hf.exists
    exact (abs_nonneg _).trans hx
  have h1 := coeFn_constLinf a b 1
  have hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), (1 : ℝ) ≤ constLinf a b 1 x := by
    filter_upwards [h1] with x hx; rw [hx]
  have hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ constLinf a b 1 x := by
    filter_upwards [h1] with x hx; rw [hx]; exact zero_le_one
  intro x hx
  rw [abs_le]
  constructor
  · exact rep_ge_of_ge_of_isWeakSolution hab _ _ one_pos hα hγ f hu (K := -M)
      (by rw [hKa]; linarith) (by rw [hKb]; linarith)
      (by filter_upwards [hf, h1] with y hy hy'; rw [hy', mul_one]; linarith [(abs_le.1 hy).1])
      x hx
  · exact rep_le_of_le_of_isWeakSolution hab _ _ one_pos hα hγ f hu (K := M)
      (by rw [hKa]; exact hM) (by rw [hKb]; exact hM)
      (by filter_upwards [hf, h1] with y hy hy'; rw [hy', mul_one]; exact (abs_le.1 hy).2) x hx

open SobolevInterval in
/-- **Corollary 8.20 (iii) of [brezis2011functional]**: for the model problem with `f = 0`,
`|u| ≤ max |u(a)| |u(b)|` on `[a, b]`, that is, `‖u‖_∞ ≤ ‖u‖_{L^∞(∂I)}`. -/
theorem abs_rep_le_max_of_isWeakSolution (hab : a < b) {u : SobolevInterval 1 a b}
    (hu : ∀ v ∈ SobolevIntervalZero a b, modelForm a b u v = load a b 0 v) :
    ∀ x ∈ Icc a b, |rep u x| ≤ max |rep u a| |rep u b| := by
  have h1 := coeFn_constLinf a b 1
  have hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), (1 : ℝ) ≤ constLinf a b 1 x := by
    filter_upwards [h1] with x hx; rw [hx]
  have hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ constLinf a b 1 x := by
    filter_upwards [h1] with x hx; rw [hx]; exact zero_le_one
  have h0 := Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))
  set K := max |rep u a| |rep u b| with hK
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (le_max_left _ _)
  intro x hx
  rw [abs_le]
  constructor
  · exact rep_ge_of_ge_of_isWeakSolution hab _ _ one_pos hα hγ 0 hu (K := -K)
      (by linarith [neg_abs_le (rep u a), le_max_left |rep u a| |rep u b|])
      (by linarith [neg_abs_le (rep u b), le_max_right |rep u a| |rep u b|])
      (by filter_upwards [h0, h1] with y hy hy'; rw [hy, hy', Pi.zero_apply, mul_one]; linarith)
      x hx
  · exact rep_le_of_le_of_isWeakSolution hab _ _ one_pos hα hγ 0 hu (K := K)
      ((le_abs_self _).trans (le_max_left _ _)) ((le_abs_self _).trans (le_max_right _ _))
      (by filter_upwards [h0, h1] with y hy hy'; rw [hy, hy', Pi.zero_apply, mul_one]; exact hK0)
      x hx

/-! ### Proposition 8.21: the maximum principle for the Neumann problem -/

open SobolevInterval in
/-- **Proposition 8.21 of [brezis2011functional] (the maximum principle for the Neumann
problem)**: if `u ∈ H¹(a, b)` satisfies `∫ u' v' + ∫ u v = ∫ f v` for every `v ∈ H¹(a, b)` and
`f ≤ K` almost everywhere, then `u ≤ K` on `[a, b]`. The same truncation `v = G(u − K)`, now
admissible without any boundary condition; here the vanishing of `∫ (u − K) G(u − K)` gives
`u ≤ K` almost everywhere, hence everywhere by continuity. -/
theorem rep_le_of_le_of_isWeakSolution_neumann (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {u : SobolevInterval 1 a b}
    (hu : ∀ v, modelForm a b u v = load a b f v) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), f x ≤ K) : ∀ x ∈ Icc a b, rep u x ≤ K := by
  have h1 := coeFn_constLinf a b 1
  obtain ⟨-, hB⟩ := integral_eq_zero_of_form_truncationElem hab (constLinf a b 1) (constLinf a b 1)
    (by filter_upwards [h1] with x hx; rw [hx]; exact zero_le_one)
    (by filter_upwards [h1] with x hx; rw [hx]; exact zero_le_one) f (K := K)
    (by filter_upwards [hf, h1] with x hx hx'; rw [hx', mul_one]; exact hx) (hu _)
  refine le_on_Icc_of_ae_le hab (continuousOn_rep hab.le u) ?_
  filter_upwards [hB, h1, fn_truncationElem hab u K, SobolevInterval.fn_ae_eq_repLp u,
    ae_restrict_mem measurableSet_Ioo] with x hx hx1 hx2 hx3 hxI
  rw [hx1, one_mul, deriv_zero, deriv_zero, hx2, hx3] at hx
  rw [SobolevInterval.rep_eq_repLp hab u (Ioo_subset_Icc_self hxI), ← sub_nonpos]
  exact mul_truncation_eq_zero_iff.1 hx

open SobolevInterval in
/-- **Proposition 8.21, the lower bound**: `K ≤ f` almost everywhere implies `K ≤ u` on
`[a, b]` for the weak solution of the Neumann problem. -/
theorem rep_ge_of_ge_of_isWeakSolution_neumann (hab : a < b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {u : SobolevInterval 1 a b}
    (hu : ∀ v, modelForm a b u v = load a b f v) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo a b)), K ≤ f x) : ∀ x ∈ Icc a b, K ≤ rep u x := by
  have hu' : ∀ v, modelForm a b (-u) v = load a b (-f) v := fun v ↦ by
    rw [map_neg, neg_apply, hu v, load_neg, neg_apply]
  have h := rep_le_of_le_of_isWeakSolution_neumann hab (-f) hu' (K := -K)
    (by filter_upwards [hf, Lp.coeFn_neg f] with x h1 h2; rw [h2, Pi.neg_apply]; linarith)
  intro x hx
  have := h x hx
  rw [SobolevInterval.rep_neg hab u hx] at this
  simp only [Pi.neg_apply] at this
  linarith

/-! ### Remarks 26 and 27: the classical maximum principle -/

/-- **The one-sided second-derivative test at a right endpoint**, the mirror image of
`IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Ici` through `y ↦ 2 x₀ − y`: if `u` has a local maximum
at `x₀` among the points of `(−∞, x₀]`, with the one-sided derivatives `u'` there and
`u' x₀ = 0`, and `u'` has one-sided derivative `c` at `x₀`, then `c ≤ 0`. Belongs beside the
`Ici` version in `Numlib/Analysis/Calculus/DerivativeTest.lean`. -/
theorem _root_.IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Iic {u u' : ℝ → ℝ} {x₀ c : ℝ}
    (hmax : IsLocalMaxOn u (Iic x₀) x₀)
    (hu : ∀ᶠ y in 𝓝[≤] x₀, HasDerivWithinAt u (u' y) (Iic x₀) y)
    (hu' : HasDerivWithinAt u' c (Iic x₀) x₀) (h0 : u' x₀ = 0) : c ≤ 0 := by
  set r : ℝ → ℝ := fun y ↦ 2 * x₀ - y with hr
  have hrd : ∀ y, HasDerivAt r (-1) y := fun y ↦ (hasDerivAt_id y).const_sub (2 * x₀)
  have hrmaps : MapsTo r (Ici x₀) (Iic x₀) := fun y hy ↦ by
    simp only [hr, mem_Ici, mem_Iic] at hy ⊢; linarith
  have hrx₀ : r x₀ = x₀ := by change 2 * x₀ - x₀ = x₀; ring
  have hrt : Tendsto r (𝓝[Ici x₀] x₀) (𝓝[Iic x₀] x₀) := by
    have h1 : Tendsto r (𝓝[Ici x₀] x₀) (𝓝 x₀) := by
      have := (hrd x₀).continuousAt.tendsto
      rw [hrx₀] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1
      (eventually_nhdsWithin_of_forall fun y hy ↦ hrmaps hy)
  have hmax' : IsLocalMaxOn (u ∘ r) (Ici x₀) x₀ := by
    have h1 : IsMaxFilter u (𝓝[Iic x₀] x₀) (r x₀) := by rwa [hrx₀]
    exact h1.comp_of_tendsto hrt
  have hu'' : ∀ᶠ y in 𝓝[≥] x₀, HasDerivWithinAt (u ∘ r) (-(u' (r y))) (Ici x₀) y := by
    have hev : ∀ᶠ y in 𝓝[≥] x₀, HasDerivWithinAt u (u' (r y)) (Iic x₀) (r y) := hrt.eventually hu
    filter_upwards [hev] with y hy
    have h2 : HasDerivWithinAt (u ∘ r) (u' (r y) * -1) (Ici x₀) y :=
      hy.comp y (hrd y).hasDerivWithinAt hrmaps
    exact h2.congr_deriv (by ring)
  have hc : HasDerivWithinAt (fun y ↦ -(u' (r y))) c (Ici x₀) x₀ := by
    have h1 : HasDerivWithinAt u' c (Iic x₀) (r x₀) := by rwa [hrx₀]
    have h2 : HasDerivWithinAt (fun y ↦ -(u' (r y))) (-(c * -1)) (Ici x₀) x₀ :=
      (h1.comp x₀ (hrd x₀).hasDerivWithinAt hrmaps).neg
    exact h2.congr_deriv (by ring)
  exact IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Ici hmax' hu'' hc (by simp [hrx₀, h0])

/-- For `v ∈ C²[a, b]`, `v` has derivative `v'` and `v'` has derivative `v''` within `[a, b]` at
every point of `[a, b]`. -/
theorem contDiffMapIcc_hasDerivWithinAt (hab : a < b) (v : ContDiffMapIcc hab.le 2) (t : Icc a b) :
    HasDerivWithinAt v.extend (v.shift.extend t) (Icc a b) t ∧
      HasDerivWithinAt v.shift.extend (v.deriv 2 t) (Icc a b) t := by
  refine ⟨?_, v.shift.hasDerivWithinAt_extend t⟩
  have := v.hasDerivWithinAt_extend t
  rwa [show v.deriv 1 t = v.shift.extend t by rw [ContDiffMapIcc.extend_val]; rfl] at this

/-- At an interior point of `[a, b]`, the second derivative of `v ∈ C²[a, b]` is
`deriv (deriv v)`. -/
theorem deriv_deriv_contDiffMapIcc_extend (hab : a < b) (v : ContDiffMapIcc hab.le 2) {x : ℝ}
    (hx : x ∈ Ioo a b) :
    _root_.deriv (_root_.deriv v.extend) x = v.deriv 2 ⟨x, Ioo_subset_Icc_self hx⟩ := by
  have hnhds : Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  have h1 : _root_.deriv v.extend =ᶠ[𝓝 x] v.shift.extend := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact ((contDiffMapIcc_hasDerivWithinAt hab v ⟨y, Ioo_subset_Icc_self hy⟩).1.hasDerivAt
      (Icc_mem_nhds hy.1 hy.2)).deriv
  rw [h1.deriv_eq]
  exact ((contDiffMapIcc_hasDerivWithinAt hab v ⟨x, Ioo_subset_Icc_self hx⟩).2.hasDerivAt
    hnhds).deriv

/-- **Remark 26 of [brezis2011functional] (the classical maximum principle)**: if `v ∈ C²[a, b]`
satisfies `−v'' + v = f` on `[a, b]`, `v(a) ≤ K`, `v(b) ≤ K` and `f ≤ K` on `[a, b]`, then
`v ≤ K` on `[a, b]`. At an interior maximum `x₀`, `v''(x₀) ≤ 0`
(`IsLocalMax.deriv_deriv_nonpos`), so `v(x₀) = f(x₀) + v''(x₀) ≤ f(x₀) ≤ K`. -/
theorem le_of_contDiffMapIcc_classical (hab : a < b) (v : ContDiffMapIcc hab.le 2) {f : ℝ → ℝ}
    (hode : ∀ x : Icc a b, -v.deriv 2 x + v x = f x) {K : ℝ}
    (hKa : v ⟨a, left_mem_Icc.2 hab.le⟩ ≤ K) (hKb : v ⟨b, right_mem_Icc.2 hab.le⟩ ≤ K)
    (hf : ∀ x ∈ Icc a b, f x ≤ K) : ∀ x : Icc a b, v x ≤ K := by
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab.le)
    v.extend.continuous.continuousOn
  have hle : ∀ x : Icc a b, v x ≤ v.extend x₀ := fun x ↦ by
    have := isMaxOn_iff.1 hmax x x.2
    rwa [ContDiffMapIcc.extend_val] at this
  suffices h : v.extend x₀ ≤ K from fun x ↦ (hle x).trans h
  rcases eq_or_lt_of_le hx₀.1 with rfl | hlt
  · rw [ContDiffMapIcc.extend_of_mem v hx₀]; exact hKa
  rcases eq_or_lt_of_le hx₀.2 with rfl | hlt'
  · rw [ContDiffMapIcc.extend_of_mem v hx₀]; exact hKb
  have hx₀' : x₀ ∈ Ioo a b := ⟨hlt, hlt'⟩
  have hloc : IsLocalMax v.extend x₀ := hmax.isLocalMax (Icc_mem_nhds hlt hlt')
  have h2 := hloc.deriv_deriv_nonpos v.extend.continuous.continuousAt
  rw [deriv_deriv_contDiffMapIcc_extend hab v hx₀'] at h2
  have := hode ⟨x₀, hx₀⟩
  rw [ContDiffMapIcc.extend_of_mem v hx₀]
  linarith [hf x₀ hx₀]

/-- At a maximum of `v ∈ C²[a, b]` on `[a, b]` attained at `a` with `v'(a) = 0`, `v''(a) ≤ 0`
(the one-sided second-derivative test). -/
theorem contDiffMapIcc_deriv_two_nonpos_left (hab : a < b) (v : ContDiffMapIcc hab.le 2)
    (hmax : IsMaxOn v.extend (Icc a b) a) (hva : v.deriv 1 ⟨a, left_mem_Icc.2 hab.le⟩ = 0) :
    v.deriv 2 ⟨a, left_mem_Icc.2 hab.le⟩ ≤ 0 := by
  have hd := contDiffMapIcc_hasDerivWithinAt hab v
  have hshift : ∀ t : Icc a b, v.shift.extend t = v.deriv 1 t := fun t ↦ by
    rw [ContDiffMapIcc.extend_val]; rfl
  refine IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Ici (u := v.extend) (u' := v.shift.extend)
    (x₀ := a) ?_ ?_ ?_ ?_
  · exact Filter.mem_of_superset (Icc_mem_nhdsGE hab) fun y hy ↦ isMaxOn_iff.1 hmax y hy
  · filter_upwards [Ico_mem_nhdsGE hab] with y hy
    refine ((hd ⟨y, Ico_subset_Icc_self hy⟩).1).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (inter_mem_nhdsWithin (Ici a) (Iio_mem_nhds hy.2))
      fun z hz ↦ ⟨hz.1, hz.2.le⟩
  · exact ((hd ⟨a, left_mem_Icc.2 hab.le⟩).2).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
  · exact (hshift ⟨a, left_mem_Icc.2 hab.le⟩).trans hva

/-- At a maximum of `v ∈ C²[a, b]` on `[a, b]` attained at `b` with `v'(b) = 0`, `v''(b) ≤ 0`
(the one-sided second-derivative test). -/
theorem contDiffMapIcc_deriv_two_nonpos_right (hab : a < b) (v : ContDiffMapIcc hab.le 2)
    (hmax : IsMaxOn v.extend (Icc a b) b) (hvb : v.deriv 1 ⟨b, right_mem_Icc.2 hab.le⟩ = 0) :
    v.deriv 2 ⟨b, right_mem_Icc.2 hab.le⟩ ≤ 0 := by
  have hd := contDiffMapIcc_hasDerivWithinAt hab v
  have hshift : ∀ t : Icc a b, v.shift.extend t = v.deriv 1 t := fun t ↦ by
    rw [ContDiffMapIcc.extend_val]; rfl
  refine IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Iic (u := v.extend) (u' := v.shift.extend)
    (x₀ := b) ?_ ?_ ?_ ?_
  · exact Filter.mem_of_superset (Icc_mem_nhdsLE hab) fun y hy ↦ isMaxOn_iff.1 hmax y hy
  · filter_upwards [Ioc_mem_nhdsLE hab] with y hy
    refine ((hd ⟨y, Ioc_subset_Icc_self hy⟩).1).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (inter_mem_nhdsWithin (Iic b) (Ioi_mem_nhds hy.1))
      fun z hz ↦ ⟨hz.2.le, hz.1⟩
  · exact ((hd ⟨b, right_mem_Icc.2 hab.le⟩).2).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)
  · exact (hshift ⟨b, right_mem_Icc.2 hab.le⟩).trans hvb

/-- **Remark 27 of [brezis2011functional] (the classical maximum principle, Neumann
conditions)**: if `v ∈ C²[a, b]` satisfies `−v'' + v = f` on `[a, b]`, `v'(a) = v'(b) = 0` and
`f ≤ K` on `[a, b]`, then `v ≤ K` on `[a, b]`. At an interior maximum as in Remark 26; at an
endpoint the one-sided second-derivative test gives `v'' ≤ 0` there as well. -/
theorem le_of_contDiffMapIcc_classical_neumann (hab : a < b) (v : ContDiffMapIcc hab.le 2)
    {f : ℝ → ℝ} (hode : ∀ x : Icc a b, -v.deriv 2 x + v x = f x)
    (hva : v.deriv 1 ⟨a, left_mem_Icc.2 hab.le⟩ = 0)
    (hvb : v.deriv 1 ⟨b, right_mem_Icc.2 hab.le⟩ = 0)
    {K : ℝ} (hf : ∀ x ∈ Icc a b, f x ≤ K) : ∀ x : Icc a b, v x ≤ K := by
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab.le)
    v.extend.continuous.continuousOn
  have hle : ∀ x : Icc a b, v x ≤ v.extend x₀ := fun x ↦ by
    have := isMaxOn_iff.1 hmax x x.2
    rwa [ContDiffMapIcc.extend_val] at this
  suffices h : v.deriv 2 ⟨x₀, hx₀⟩ ≤ 0 by
    have := hode ⟨x₀, hx₀⟩
    intro x
    refine (hle x).trans ?_
    rw [ContDiffMapIcc.extend_of_mem v hx₀]
    linarith [hf x₀ hx₀]
  rcases eq_or_lt_of_le hx₀.1 with h | hlt
  · subst h
    exact contDiffMapIcc_deriv_two_nonpos_left hab v hmax hva
  rcases eq_or_lt_of_le hx₀.2 with h | hlt'
  · subst h
    exact contDiffMapIcc_deriv_two_nonpos_right hab v hmax hvb
  · have hx₀' : x₀ ∈ Ioo a b := ⟨hlt, hlt'⟩
    have hloc : IsLocalMax v.extend x₀ := hmax.isLocalMax (Icc_mem_nhds hlt hlt')
    have h2 := hloc.deriv_deriv_nonpos v.extend.continuous.continuousAt
    rwa [deriv_deriv_contDiffMapIcc_extend hab v hx₀'] at h2

/-! ### Remark 28: the maximum principle on `ℝ` -/

namespace Line

/-- Almost-everywhere statements over the restriction of Lebesgue measure to the whole line. -/
theorem ae_restrict_top_iff {P : ℝ → Prop} :
    (∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), P x) ↔ ∀ᵐ x, P x := by
  rw [Opens.coe_top, Measure.restrict_univ]

open SobolevIntervalLp in
/-- `G(ũ − K) ∈ L²(ℝ)` for `u ∈ H¹(ℝ)` and `K ≥ 0` (Corollary 8.11 needs `G(−K) = 0`). -/
theorem memLp_truncation_rep_top (u : SobolevIntervalLp 1 2 ⊤) {K : ℝ} (hK : 0 ≤ K) :
    MemLp (fun t ↦ truncation (rep u t - K)) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (memSobolevIntervalLp_one_iff.1 (memSobolevIntervalLp_comp Opens.ordConnected_top u
    (contDiff_truncation_sub K) (truncation_eq_zero_of_nonpos (by linarith))).1).1

open SobolevIntervalLp in
/-- `2 max (ũ − K) 0 · u' ∈ L²(ℝ)`. -/
theorem memLp_deriv_truncation_rep_mul_top (u : SobolevIntervalLp 1 2 ⊤) (K : ℝ) :
    MemLp (fun t ↦ 2 * max (rep u t - K) 0 * deriv u 1 t) 2
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
  have := memLp_deriv_comp Opens.ordConnected_top u (contDiff_truncation_sub K)
  simp only [deriv_truncation_sub] at this
  exact this

open SobolevIntervalLp in
/-- The chain rule for `G(ũ − K)` on `ℝ`. -/
theorem hasWeakDerivOn_truncation_rep_top (u : SobolevIntervalLp 1 2 ⊤) (K : ℝ) :
    HasWeakDerivOn (fun t ↦ truncation (rep u t - K))
      (fun t ↦ 2 * max (rep u t - K) 0 * deriv u 1 t) ⊤ := by
  have := hasWeakDerivOn_comp Opens.ordConnected_top u (contDiff_truncation_sub K)
  simp only [deriv_truncation_sub] at this
  exact this

/-- **The truncation `G(u − K)` of `u ∈ H¹(ℝ)`** as an element of `H¹(ℝ)`, for `K ≥ 0`. -/
def truncationElem (u : SobolevIntervalLp 1 2 ⊤) {K : ℝ} (hK : 0 ≤ K) : SobolevIntervalLp 1 2 ⊤ :=
  SobolevIntervalLp.mk
    ![(memLp_truncation_rep_top u hK).toLp (fun t ↦ truncation (SobolevIntervalLp.rep u t - K)),
      (memLp_deriv_truncation_rep_mul_top u K).toLp
        (fun t ↦ 2 * max (SobolevIntervalLp.rep u t - K) 0 * SobolevIntervalLp.deriv u 1 t)]
    fun j ↦ by
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := ⊤) one_le_two)
    · exact (hasWeakDerivOn_truncation_rep_top u K).congr_ae
        (memLp_truncation_rep_top u hK).coeFn_toLp.symm
        (memLp_deriv_truncation_rep_mul_top u K).coeFn_toLp.symm

open SobolevIntervalLp in
/-- The function of the truncated element on `ℝ`. -/
theorem fn_truncationElem (u : SobolevIntervalLp 1 2 ⊤) {K : ℝ} (hK : 0 ≤ K) :
    fn (truncationElem u hK) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ truncation (rep u t - K) :=
  (memLp_truncation_rep_top u hK).coeFn_toLp

open SobolevIntervalLp in
/-- The weak derivative of the truncated element on `ℝ`. -/
theorem coeFn_deriv_truncationElem_one (u : SobolevIntervalLp 1 2 ⊤) {K : ℝ} (hK : 0 ≤ K) :
    ⇑(deriv (truncationElem u hK) 1) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ 2 * max (rep u t - K) 0 * deriv u 1 t :=
  (memLp_deriv_truncation_rep_mul_top u K).coeFn_toLp

/-- The load of `−f` is `−load f`. -/
theorem load_neg (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) : load (-f) = -load f := by
  ext v
  rw [neg_apply, load_apply_inner, load_apply_inner, inner_neg_left]

/-- The weak solution depends linearly on the datum: `solution (−f) = −solution f`. -/
theorem solution_neg (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    solution (-f) = -solution f :=
  (eq_solution_of_forall fun v ↦ by
    rw [form_apply, inner_neg_left, ← form_apply, form_solution, load_neg, neg_apply]).symm

open SobolevIntervalLp in
/-- The continuous representative of the weak solution is continuous on `ℝ`. -/
theorem continuous_rep_solution (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    Continuous (rep (solution f)) := by
  have := continuousOn_rep Opens.ordConnected_top (solution f)
  rwa [Opens.coe_top, closure_univ, continuousOn_univ] at this

open SobolevIntervalLp in
/-- **Remark 28 of [brezis2011functional] (the maximum principle on `ℝ`)**: for `f ∈ L²(ℝ)`
with `f ≤ K` almost everywhere, `0 ≤ K`, the weak solution `u` of `−u'' + u = f` on `ℝ` satisfies
`u ≤ K` everywhere. The truncation `G(u − K) ∈ H¹(ℝ)` (which needs `0 ≤ K`) tested in the weak
equation gives `∫ (u − K) G(u − K) = 0`, so `u ≤ K` almost everywhere, hence everywhere by
continuity. -/
theorem rep_le_of_le (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), f x ≤ K) :
    ∀ x, rep (solution f) x ≤ K := by
  set v := truncationElem (solution f) hK with hvdef
  have hI := Opens.ordConnected_top
  have hv₀ : (deriv v 0 : ℝ → ℝ) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun x ↦ truncation (fn (solution f) x - K) := by
    rw [deriv_zero]
    filter_upwards [fn_truncationElem (solution f) hK, fn_ae_eq_rep hI (solution f)] with x h1 h2
    rw [h1, h2]
  have hv₁ : (deriv v 1 : ℝ → ℝ) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun x ↦ 2 * max (fn (solution f) x - K) 0 * deriv (solution f) 1 x := by
    filter_upwards [coeFn_deriv_truncationElem_one (solution f) hK, fn_ae_eq_rep hI (solution f)]
      with x h1 h2
    rw [h1, h2]
  have hmul : ∀ (g h : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))),
      Integrable (fun x ↦ g x * h x) (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := fun g h ↦
    memLp_one_iff_integrable.1
      ((Lp.memLp g).mul (r := 1) (hpqr := holderTriple_two_two_one) (Lp.memLp h))
  have i1 : Integrable (fun x ↦ (1 : ℝ) * deriv (solution f) 1 x * deriv v 1 x)
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    (hmul (deriv (solution f) 1) (deriv v 1)).congr
      (Eventually.of_forall fun x ↦ by simp only [one_mul])
  have i2 : Integrable (fun x ↦ (1 : ℝ) * fn (solution f) x * deriv v 0 x)
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    (hmul (deriv (solution f) 0) (deriv v 0)).congr
      (Eventually.of_forall fun x ↦ by simp only [one_mul]; rfl)
  have i3 : Integrable (fun x ↦ f x * deriv v 0 x) (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    hmul f (deriv v 0)
  have i4 : Integrable (fun x ↦ (1 : ℝ) * deriv v 0 x)
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
    refine (Lp.memLp (deriv (solution f) 0)).integrable_sq.mono'
      ((Lp.aestronglyMeasurable (deriv v 0)).const_mul 1) ?_
    filter_upwards [hv₀] with x hx
    rw [one_mul, hx, Real.norm_eq_abs, abs_of_nonneg (truncation_nonneg _), truncation]
    have h1 : max (fn (solution f) x - K) 0 ≤ |fn (solution f) x| := by
      rcases le_or_gt (fn (solution f) x - K) 0 with h | h
      · rw [max_eq_right h]; exact abs_nonneg _
      · rw [max_eq_left h.le]; linarith [le_abs_self (fn (solution f) x)]
    calc max (fn (solution f) x - K) 0 ^ 2 ≤ |fn (solution f) x| ^ 2 :=
          pow_le_pow_left₀ (le_max_right _ _) h1 2
      _ = deriv (solution f) 0 x ^ 2 := by rw [sq_abs]; rfl
  have heq : ∫ x, ((1 : ℝ) * deriv (solution f) 1 x * deriv v 1 x
        + 1 * fn (solution f) x * deriv v 0 x) ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
      = ∫ x, f x * deriv v 0 x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
    have h := form_solution f v
    rw [form_apply, inner_eq_integral, load_apply_inner, L2.inner_def] at h
    have e1 : ∫ x, ((1 : ℝ) * deriv (solution f) 1 x * deriv v 1 x
          + 1 * fn (solution f) x * deriv v 0 x) ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
        = ∫ x in ((⊤ : Opens ℝ) : Set ℝ),
          (fn (solution f) x * fn v x + deriv (solution f) 1 x * deriv v 1 x) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by
        simp only [one_mul, deriv_zero]; ring)
    have e2 : ∫ x in ((⊤ : Opens ℝ) : Set ℝ), ⟪f x, deriv v 0 x⟫_ℝ
        = ∫ x, f x * deriv v 0 x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by
        simp only [RCLike.inner_apply, conj_trivial, mul_comm])
    rw [e1, h, e2]
  obtain ⟨-, hB⟩ := integral_eq_zero_of_truncation (μ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ))
    (α := fun _ ↦ 1) (γ := fun _ ↦ 1) (f := fun x ↦ f x) (u₀ := fn (solution f))
    (u₁ := deriv (solution f) 1) (v₀ := deriv v 0) (v₁ := deriv v 1) (K := K)
    (Eventually.of_forall fun _ ↦ zero_le_one) (Eventually.of_forall fun _ ↦ zero_le_one)
    (by filter_upwards [hf] with x hx; rw [mul_one]; exact hx) hv₀ hv₁ i1 i2 i3 i4 heq
  have hae : ∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), rep (solution f) x ≤ K := by
    filter_upwards [hB, hv₀, fn_ae_eq_rep hI (solution f)] with x h1 h2 h3
    rw [one_mul, h2, h3] at h1
    rw [← sub_nonpos]
    exact mul_truncation_eq_zero_iff.1 h1
  exact le_of_ae_le (continuous_rep_solution f) (ae_restrict_top_iff.1 hae)

open SobolevIntervalLp in
/-- **Remark 28, the lower bound**: for `f ∈ L²(ℝ)` with `K ≤ f` almost everywhere and `K ≤ 0`,
the weak solution satisfies `K ≤ u` everywhere — the upper bound applied to `−f`. -/
theorem le_rep_of_le (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) {K : ℝ} (hK : K ≤ 0)
    (hf : ∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), K ≤ f x) :
    ∀ x, K ≤ rep (solution f) x := by
  have h := rep_le_of_le (-f) (K := -K) (by linarith)
    (by filter_upwards [hf, Lp.coeFn_neg f] with x h1 h2; rw [h2, Pi.neg_apply]; linarith)
  intro x
  have := h x
  rw [solution_neg] at this
  have e := rep_smul Opens.ordConnected_top (-1) (solution f) (Opens.mem_closure_top x)
  simp only [neg_one_smul, Pi.neg_apply] at e
  linarith

end Line

end EllipticInterval
