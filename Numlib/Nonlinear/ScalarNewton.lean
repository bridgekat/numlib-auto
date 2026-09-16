import Numlib.Analysis.Calculus.RootMultiplicity
import Numlib.Nonlinear.Newton
import Numlib.Nonlinear.Order

/-!
# Newton's method for a real function of one real variable

`Newton.scalarStep f f' x = x - f x / f' x` is the scalar instance of the Banach-space
`Newton.step` of `Numlib/Nonlinear/Newton.lean` — the two agree everywhere, including where
`f' x = 0`, since `ContinuousLinearMap.inverse 0 = 0` and `a / 0 = 0` (`Newton.scalarStep_eq_step`)
— together with what the scalar setting adds ([quarteroni2000numerical] §6.2.2, §6.3.1, §6.6.2,
Exercise 6.2; [kress1998numerical] §6.2; [han2009theoretical] §5.4):

* the iteration function `φ_Newt = scalarStep f f'` and its derivatives at a simple root,
  `φ_Newt'(α) = 0` (`hasDerivAt_scalarStep`) and `φ_Newt''(α) = f''(α) / f'(α)`
  (`deriv2_scalarStep_root`), and its order `2` with the classical constant
  `f''(α) / (2 f'(α))` (`tendsto_scalarStep_sub_div_sq`, `hasIterationOrder_scalarStep_two`);
* at a root of multiplicity `m`, linear convergence with factor `1 - 1/m`
  (`tendsto_scalarStep_sub_div_of_isRootOfMultiplicity`, the book's (6.22));
* the two repairs: the modified Newton method `x - m f x / f' x` (`modifiedScalarStep`), which is
  quadratic again when `m` is known (`tendsto_modifiedScalarStep_sub_div_sq`,
  `exists_ball_abs_modifiedScalarStep_sub_le`, Exercise 6.2), and the adaptive Newton method
  (`adaptiveStep`), which estimates `m` from the increment ratios (`multiplicityEstimate`,
  `tendsto_multiplicityEstimate`, the book's (6.40)).

Multiplicity is `IsRootOfMultiplicity f α m` of `Numlib/Analysis/Calculus/RootMultiplicity`; every
multiple-root proof writes `f x = (x - α)^m h x` with `h` `C¹` at `α`, `h α = f^{(m)}(α) / m!` and
`h'(α) = f^{(m+1)}(α) / (m + 1)!` (`IsRootOfMultiplicity.exists_eq_pow_mul_deriv`), and then
`f'(x) = (x - α)^{m-1} (m h x + (x - α) h'(x))` near `α` (`Newton.deriv_eq_of_eq_pow_mul`). The
modified step's error is then `(x - α)² h'(x) / (m h x + (x - α) h'(x))`, whose ratio limit gives
Newton's constant for `m = 1`.
-/

open Filter Topology Set

namespace Newton

section Defs

/-- One scalar Newton step `x ↦ x - f x / f' x` ([quarteroni2000numerical] (6.16)); the iteration
function `φ_Newt` of §6.3.1 is `scalarStep f f'` itself. Lean's `a / 0 = 0` makes it stall where
`f' x = 0`. -/
noncomputable def scalarStep (f f' : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / f' x

/-- A root of `f` is a fixed point of the scalar Newton step. -/
theorem scalarStep_apply_of_eq_zero (f f' : ℝ → ℝ) {x : ℝ} (hx : f x = 0) :
    scalarStep f f' x = x := by
  simp [scalarStep, hx]

/-- The scalar step is the Banach-space `Newton.step` with the derivative `f' x • id`, for every
`x` — also where `f' x = 0`, where both sides equal `x` (`ContinuousLinearMap.inverse` of `0` is
`0`). Through this every theorem of `Numlib/Nonlinear/Newton.lean` (local quadratic convergence,
Kantorovich) is available to the scalar setting without restatement. -/
theorem scalarStep_eq_step (f f' : ℝ → ℝ) (x : ℝ) :
    scalarStep f f' x = step f (fun x => f' x • ContinuousLinearMap.id ℝ ℝ) x := by
  unfold scalarStep step
  congr 1
  by_cases h : f' x = 0
  · simp [h]
  · have hinv : (f' x • ContinuousLinearMap.id ℝ ℝ).inverse =
        (f' x)⁻¹ • ContinuousLinearMap.id ℝ ℝ :=
      ContinuousLinearMap.inverse_eq
        (by rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
          mul_inv_cancel₀ h, one_smul, ContinuousLinearMap.id_comp])
        (by rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
          inv_mul_cancel₀ h, one_smul, ContinuousLinearMap.id_comp])
    rw [hinv]
    simp [div_eq_inv_mul]

/-- The derivative of the Newton iteration function where `f' x ≠ 0`: with `f'` the derivative of
`f` and `f''` that of `f'` at `x`, `φ_Newt'(x) = f x f''(x) / f'(x)²` (quotient rule). At a simple
root, `f α = 0` gives `φ_Newt'(α) = 0`, the first display of [quarteroni2000numerical] §6.3.1. -/
theorem hasDerivAt_scalarStep {f f' : ℝ → ℝ} {x f'' : ℝ} (hf : HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' f'' x) (hx : f' x ≠ 0) :
    HasDerivAt (scalarStep f f') (f x * f'' / (f' x) ^ 2) x := by
  refine ((hasDerivAt_id x).sub (hf.div hf' hx)).congr_deriv ?_
  field_simp
  ring

end Defs

section Multiple

variable {f : ℝ → ℝ} {α : ℝ} {m : ℕ}

/-- **The derivative near a multiple root.** If `f x = (x - α)^{m+1} h x` with `h` `C¹` at `α`,
then near `α`, `f'(x) = (x - α)^m ((m + 1) h x + (x - α) h'(x))`. -/
theorem deriv_eq_of_eq_pow_mul {h : ℝ → ℝ} (hh : ContDiffAt ℝ 1 h α)
    (hfh : ∀ x, f x = (x - α) ^ (m + 1) * h x) :
    ∀ᶠ x in 𝓝 α, deriv f x =
      (x - α) ^ m * (((m + 1 : ℕ) : ℝ) * h x + (x - α) * deriv h x) := by
  filter_upwards [hh.eventually_hasDerivAt] with x hx
  have hpow : HasDerivAt (fun x => (x - α) ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * (x - α) ^ (m + 1 - 1) * 1) x :=
    ((hasDerivAt_id' x).sub_const α).pow (m + 1)
  have hd : HasDerivAt f _ x :=
    (hpow.mul hx).congr_of_eventuallyEq (Eventually.of_forall fun y => hfh y)
  rw [hd.deriv]
  simp only [Nat.add_sub_cancel, mul_one]
  ring

/-- The denominator `c h x + (x - α) h'(x)` of the multiple-root error formulas tends to
`c h α` when `h` is `C¹` at `α`. -/
theorem tendsto_const_mul_add_sub_mul_deriv {h : ℝ → ℝ} (hh : ContDiffAt ℝ 1 h α) (c : ℝ) :
    Tendsto (fun x => c * h x + (x - α) * deriv h x) (𝓝 α) (𝓝 (c * h α)) := by
  have := (hh.continuousAt.tendsto.const_mul c).add
    (((continuous_id.sub (continuous_const (y := α))).tendsto α).mul hh.continuousAt_deriv.tendsto)
  simpa using this

/-- **[quarteroni2000numerical] (6.22): at a root of multiplicity `m` Newton's method is linear
with factor `1 - 1/m`.** If `1 ≤ m`, `f` is `C^{m+1}` at `α` and `α` is a root of multiplicity
`m`, then `(scalarStep f f' x - α) / (x - α) → 1 - 1/m` as `x → α`, `x ≠ α`. With
`f x = e^m h x` and `f'(x) = e^{m-1} (m h x + e h'(x))`, the ratio is `1 - h x / (m h x + e h'(x))`.
The limit form is stated rather than a derivative of `φ_Newt` at `α`, where `φ_Newt` takes the
junk value `α - 0 / 0 = α`; it is what (6.22) and §6.6.2 use (Exercise 6.2). -/
theorem tendsto_scalarStep_sub_div_of_isRootOfMultiplicity (hm : 1 ≤ m)
    (hf : ContDiffAt ℝ (m + 1 : ℕ) f α) (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (scalarStep f (deriv f) x - α) / (x - α)) (𝓝[≠] α) (𝓝 (1 - 1 / m)) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  obtain ⟨h, hh, hhα, -, hfh⟩ := hα.exists_eq_pow_mul_deriv hf
  have hc0 : h α ≠ 0 := hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero
  have hDen := tendsto_const_mul_add_sub_mul_deriv hh ((q + 1 : ℕ) : ℝ)
  have hDen0 : ((q + 1 : ℕ) : ℝ) * h α ≠ 0 := mul_ne_zero (by positivity) hc0
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (hh.continuousAt.tendsto.div hDen hDen0)).mono_left (nhdsWithin_le_nhds (s := {α}ᶜ))
  rw [div_mul_cancel_right₀ hc0, ← one_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (deriv_eq_of_eq_pow_mul hh hfh),
    nhdsWithin_le_nhds (hDen.eventually (isOpen_ne.mem_nhds hDen0))] with x hx hdx hden
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  simp only [Pi.div_apply]
  rw [scalarStep, hdx, hfh x, sub_right_comm, sub_div, div_self he]
  congr 1
  generalize x - α = e at he hden ⊢
  field_simp
  ring

/-- At a root of multiplicity `m ≥ 2`, Newton's method has iteration order `1` at `α`: the
convergence factor `1 - 1/m` is below one. -/
theorem hasIterationOrder_scalarStep_one_of_isRootOfMultiplicity (hm : 2 ≤ m)
    (hf : ContDiffAt ℝ (m + 1 : ℕ) f α) (hα : IsRootOfMultiplicity f α m) :
    HasIterationOrder (scalarStep f (deriv f)) α 1 := by
  refine hasIterationOrder_one_of_tendsto_sub_div
    (scalarStep_apply_of_eq_zero f (deriv f) (hα.eq_zero (by omega))) ?_
    (tendsto_scalarStep_sub_div_of_isRootOfMultiplicity (by omega) hf hα)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (0 : ℝ) < 1 / m := by positivity
  have h2 : (1 : ℝ) / m ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- **The modified Newton method** ([quarteroni2000numerical] (6.23)) for a root of known
multiplicity `m`: `x ↦ x - m f x / f' x`. -/
noncomputable def modifiedScalarStep (f f' : ℝ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  x - m * (f x / f' x)

/-- With `m = 1` the modified method is Newton's method. -/
theorem modifiedScalarStep_one (f f' : ℝ → ℝ) : modifiedScalarStep f f' 1 = scalarStep f f' := by
  funext x
  simp [modifiedScalarStep, scalarStep]

/-- A root of `f` is a fixed point of the modified Newton step. -/
theorem modifiedScalarStep_apply_of_eq_zero (f f' : ℝ → ℝ) (m : ℕ) {x : ℝ} (hx : f x = 0) :
    modifiedScalarStep f f' m x = x := by
  simp [modifiedScalarStep, hx]

/-- **The modified Newton method is of second order at a root of multiplicity `m`, with its
constant** ([quarteroni2000numerical] Exercise 6.2): if `1 ≤ m`, `f` is `C^{m+1}` at `α` and `α`
is a root of multiplicity `m`, then
`(modifiedScalarStep f f' m x - α) / (x - α)² → f^{(m+1)}(α) / ((m + 1) m f^{(m)}(α))`. With
`f x = e^m h x`, the step's error is `e² h'(x) / (m h x + e h'(x))`, and `h'(α) / (m h α)` is the
limit. For `m = 1` this is Newton's constant `f''(α) / (2 f'(α))`. -/
theorem tendsto_modifiedScalarStep_sub_div_sq (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (modifiedScalarStep f (deriv f) m x - α) / (x - α) ^ 2) (𝓝[≠] α)
      (𝓝 (iteratedDeriv (m + 1) f α / ((m + 1) * m * iteratedDeriv m f α))) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  obtain ⟨h, hh, hhα, hhα', hfh⟩ := hα.exists_eq_pow_mul_deriv hf
  have hc0 : h α ≠ 0 := hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero
  have hDen := tendsto_const_mul_add_sub_mul_deriv hh ((q + 1 : ℕ) : ℝ)
  have hDen0 : ((q + 1 : ℕ) : ℝ) * h α ≠ 0 := mul_ne_zero (by positivity) hc0
  have hlim := (hh.continuousAt_deriv.tendsto.div hDen hDen0).mono_left
    (nhdsWithin_le_nhds (s := {α}ᶜ))
  have hD0 : iteratedDeriv (q + 1) f α ≠ 0 := hα.2
  rw [hhα', hhα, show iteratedDeriv (q + 1 + 1) f α / ((q + 1 + 1).factorial : ℝ) /
      (((q + 1 : ℕ) : ℝ) * (iteratedDeriv (q + 1) f α / (q + 1).factorial)) =
      iteratedDeriv (q + 1 + 1) f α /
        ((((q + 1 : ℕ) : ℝ) + 1) * ((q + 1 : ℕ) : ℝ) * iteratedDeriv (q + 1) f α) by
    rw [Nat.factorial_succ (q + 1)]
    push_cast
    field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (deriv_eq_of_eq_pow_mul hh hfh),
    nhdsWithin_le_nhds (hDen.eventually (isOpen_ne.mem_nhds hDen0))] with x hx hdx hden
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  simp only [Pi.div_apply]
  rw [modifiedScalarStep, hdx, hfh x, sub_right_comm]
  generalize x - α = e at he hden ⊢
  rw [show e ^ (q + 1) * h x / (e ^ q * (((q + 1 : ℕ) : ℝ) * h x + e * deriv h x)) =
      e * h x / (((q + 1 : ℕ) : ℝ) * h x + e * deriv h x) by
    rw [pow_succ, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero q he)],
    div_eq_div_iff hden (pow_ne_zero 2 he), sub_mul, mul_div_assoc', div_mul_cancel₀ _ hden]
  ring

/-- **[quarteroni2000numerical] Exercise 6.2: the modified Newton method is second order at a
root of multiplicity `m`**, as a bound: if `1 ≤ m`, `f` is `C^{m+1}` at `α` and `α` is a root of
multiplicity `m`, then on a ball around `α`, `|modifiedScalarStep f f' m x - α| ≤ C |x - α|²`. -/
theorem exists_ball_abs_modifiedScalarStep_sub_le (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    ∃ ε > 0, ∃ C, ∀ x ∈ Metric.ball α ε,
      |modifiedScalarStep f (deriv f) m x - α| ≤ C * |x - α| ^ 2 := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (eventually_abs_sub_le_mul_abs_pow_of_tendsto
    (modifiedScalarStep_apply_of_eq_zero f (deriv f) m (hα.eq_zero hm))
    (tendsto_modifiedScalarStep_sub_div_sq hm hf hα))
  exact ⟨ε, hε, _, fun x hx => h (Metric.mem_ball.1 hx)⟩

/-- The modified Newton method has iteration order `2` at a root of multiplicity `m`. -/
theorem hasIterationOrder_modifiedScalarStep_two (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    HasIterationOrder (modifiedScalarStep f (deriv f) m) α 2 := by
  have := hasIterationOrder_of_tendsto_sub_div_pow
    (modifiedScalarStep_apply_of_eq_zero f (deriv f) m (hα.eq_zero hm)) le_rfl
    (tendsto_modifiedScalarStep_sub_div_sq hm hf hα)
  simpa using this

end Multiple

section Simple

variable {f : ℝ → ℝ} {α : ℝ}

/-- **Newton's method at a simple root, the classical constant**: if `f α = 0`, `f` is `C²` at `α`
and `f'(α) ≠ 0`, then `(scalarStep f f' x - α) / (x - α)² → f''(α) / (2 f'(α))` as `x → α`,
`x ≠ α` — the case `m = 1` of `tendsto_modifiedScalarStep_sub_div_sq`. Only `C²` is needed,
whereas reading it off `φ_Newt''(α) = f''(α) / f'(α)` through Property 6.4 would ask `C³`. -/
theorem tendsto_scalarStep_sub_div_sq (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) :
    Tendsto (fun x => (scalarStep f (deriv f) x - α) / (x - α) ^ 2) (𝓝[≠] α)
      (𝓝 (iteratedDeriv 2 f α / (2 * deriv f α))) := by
  have hroot : IsRootOfMultiplicity f α 1 := isRootOfMultiplicity_one_iff.2 ⟨hα, hf'⟩
  have := tendsto_modifiedScalarStep_sub_div_sq le_rfl (by simpa using hf) hroot
  rw [modifiedScalarStep_one] at this
  simpa [one_add_one_eq_two] using this

/-- **Newton's method is of order `2` at a simple root** in the sense of Definition 6.1
([quarteroni2000numerical] §6.3.1; [kress1998numerical] Thm 6.20; [han2009theoretical] Thm 5.4.1):
if `f α = 0`, `f` is `C²` at `α` and `f'(α) ≠ 0`, then `scalarStep f f'` has iteration order `2`
at `α`. -/
theorem hasIterationOrder_scalarStep_two (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) : HasIterationOrder (scalarStep f (deriv f)) α 2 := by
  have := hasIterationOrder_of_tendsto_sub_div_pow (scalarStep_apply_of_eq_zero f (deriv f) hα)
    le_rfl (tendsto_scalarStep_sub_div_sq hα hf hf')
  simpa using this

/-- **`φ_Newt''(α) = f''(α) / f'(α)`** at a simple root of a `C³` function
([quarteroni2000numerical] §6.3.1): the second derivative of the Newton iteration function at `α`.
Near `α`, `φ_Newt' = f f'' / f'²`, whose derivative at `α` reduces to `f''(α) / f'(α)` because
`f α = 0`. -/
theorem deriv2_scalarStep_root (hf : ContDiffAt ℝ 3 f α) (hα : f α = 0) (hf' : deriv f α ≠ 0) :
    iteratedDeriv 2 (scalarStep f (deriv f)) α = iteratedDeriv 2 f α / deriv f α := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  have hfb : ContDiffOn ℝ (3 : ℕ) f (Metric.ball α r) := by exact_mod_cast hfu.mono hru
  have hd : ∀ j < 3, ∀ x ∈ Metric.ball α r,
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := fun j hj x hx =>
    hfb.hasDerivAt_iteratedDeriv_of_isOpen Metric.isOpen_ball hj hx
  have hcont : ContinuousAt (deriv f) α := by
    have := (hfb.continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball (j := 1)
      (by norm_num)).continuousAt (Metric.ball_mem_nhds α hr)
    simpa using this
  -- `φ_Newt' = f f'' / f'²` near `α`
  have hφ' : deriv (scalarStep f (deriv f)) =ᶠ[𝓝 α]
      fun x => f x * iteratedDeriv 2 f x / (deriv f x) ^ 2 := by
    filter_upwards [Metric.ball_mem_nhds α hr, hcont.eventually_ne hf'] with x hx hx'
    have h1 : HasDerivAt f (deriv f x) x := by simpa using hd 0 (by norm_num) x hx
    have h2 : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
      simpa using hd 1 (by norm_num) x hx
    exact (hasDerivAt_scalarStep h1 h2 hx').deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hφ'.deriv_eq]
  -- differentiate `f f'' / f'²` at `α`
  have h1 : HasDerivAt f (deriv f α) α := by
    simpa using hd 0 (by norm_num) α (Metric.mem_ball_self hr)
  have h2 : HasDerivAt (deriv f) (iteratedDeriv 2 f α) α := by
    simpa using hd 1 (by norm_num) α (Metric.mem_ball_self hr)
  have h3 : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f α) α :=
    hd 2 (by norm_num) α (Metric.mem_ball_self hr)
  refine ((h1.mul h3).div (h2.pow 2) (pow_ne_zero 2 hf')).deriv.trans ?_
  simp only [Pi.mul_apply, Pi.pow_apply, hα]
  field_simp
  ring

end Simple

section Adaptive

/-- **The multiplicity estimate** of [quarteroni2000numerical] (6.40),
`m^{(k+2)} = 1 / (1 - λ^{(k+2)})` with `λ` the increment ratio `aitkenRatio`; in the book's other
form, `(x^{(k+1)} - x^{(k)}) / (2 x^{(k+1)} - x^{(k+2)} - x^{(k)})`. -/
noncomputable def multiplicityEstimate (x : ℕ → ℝ) (k : ℕ) : ℝ := 1 / (1 - aitkenRatio x k)

/-- The estimate in the book's second form (when the increment `x (k+1) - x k` is nonzero; where it
vanishes the two forms are `1` and `0` under Lean's `a / 0 = 0`). -/
theorem multiplicityEstimate_eq (x : ℕ → ℝ) (k : ℕ) (h : x (k + 1) - x k ≠ 0) :
    multiplicityEstimate x k = (x (k + 1) - x k) / (2 * x (k + 1) - x (k + 2) - x k) := by
  unfold multiplicityEstimate aitkenRatio
  rw [one_sub_div h, one_div_div]
  congr 1
  ring

/-- **The estimate finds the multiplicity** ([quarteroni2000numerical] §6.6.2): along a Newton
orbit `x (k+1) = scalarStep f f' (x k)` converging to a root `α` of multiplicity `m ≥ 1` without
hitting it, `multiplicityEstimate x k → m`. The error ratios tend to `1 - 1/m ≠ 1` by (6.22), so
`aitkenRatio x → 1 - 1/m` by (6.34) and `1 / (1 - (1 - 1/m)) = m`. -/
theorem tendsto_multiplicityEstimate {f : ℝ → ℝ} {α : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiffAt ℝ (m + 1 : ℕ) f α) (hα : IsRootOfMultiplicity f α m) {x : ℕ → ℝ}
    (hx : ∀ k, x (k + 1) = scalarStep f (deriv f) (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) : Tendsto (multiplicityEstimate x) atTop (𝓝 m) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hratio : Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 (1 - 1 / m)) := by
    have := (tendsto_scalarStep_sub_div_of_isRootOfMultiplicity hm hf hα).comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
    refine this.congr fun k => ?_
    simp [Function.comp, hx]
  have h1 : (1 : ℝ) - 1 / m ≠ 1 := by
    intro h
    have : (1 : ℝ) / m = 0 := by linarith
    exact hm0 (by simpa using this)
  have := (tendsto_const_nhds (x := (1 : ℝ))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_aitkenRatio hne hratio h1))
    (sub_ne_zero.2 h1.symm)
  rw [sub_sub_cancel, one_div_one_div] at this
  exact this

/-- **The adaptive Newton method** ([quarteroni2000numerical] (6.39)) as a step on the last three
iterates `(x_{k-2}, x_{k-1}, x_k)`, producing `(x_{k-1}, x_k, x_k - m_k f x_k / f' x_k)` with
`m_k = (x_{k-1} - x_{k-2}) / (2 x_{k-1} - x_k - x_{k-2})` the estimate (6.40) (junk `m_k = 0` when
the denominator vanishes; the book's Program 56 freezes the previous estimate instead and updates
it only when the ratios have settled, a safeguard that belongs to the implementation). A definition
only: the book proves nothing about the adaptive iteration. -/
noncomputable def adaptiveStep (f f' : ℝ → ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (s.2.1, s.2.2, s.2.2 - (s.2.1 - s.1) / (2 * s.2.1 - s.2.2 - s.1) * (f s.2.2 / f' s.2.2))

end Adaptive

end Newton
