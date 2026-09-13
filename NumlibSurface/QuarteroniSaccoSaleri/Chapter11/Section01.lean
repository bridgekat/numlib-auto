import Numlib.Analysis.ODE.Cauchy
import Numlib.Analysis.ODE.Gronwall

/-!
# Quarteroni–Sacco–Saleri §11.1: the Cauchy problem

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.1.

The scalar Cauchy problem (11.1), `y'(t) = f(t, y(t))` on an interval `I ∋ t₀` with `y(t₀) = y₀`,
its equivalence with the integral equation (11.2) for a continuous `f`, the two existence and
uniqueness results the book recalls (local, under a Lipschitz condition (11.3) on a box, with the
radius bounds `r₀ < min(r_J, r_Σ / M)`; global, under a uniform Lipschitz condition), the
perturbed problem (11.4) and Liapunov stability (Definition 11.1, (11.5)) with its asymptotic
form (11.6), the stability estimate `|y(t) - z(t)| ≤ (1 + |t - t₀|) ε e^{L |t - t₀|}` under a
uniform Lipschitz condition and the constant `C = (1 + K_I) e^{L K_I}` it gives, and Gronwall's
lemma (Lemma 11.1).

Everything is the real case `E = ℝ` of `Numlib/Analysis/ODE/Cauchy` (`ODE.IsSolutionOn`,
`ODE.IsLiapunovStable`, `ODE.IsAsymptoticallyStable`, the existence theorems and the estimate
`ODE.norm_sub_le_of_lipschitz`) and of `Numlib/Analysis/ODE/Gronwall`
(`Gronwall.le_mul_exp_integral`).

## Main definitions

* `cauchyProblem f t₀ y₀ I y` — `y` solves (11.1) on `I`.
* `definition_11_1 f t₀ y₀ I` — the Cauchy problem is Liapunov stable on `I`.
* `definition_11_1_asymptotic f t₀ y₀` — the Cauchy problem is asymptotically stable.

## Main results

* `equation_11_2` — for a continuous `f`, (11.1) on `[t₀, t₀ + T]` is equivalent to (11.2).
* `localExistenceUniqueness`, `globalExistenceUniqueness` — items 1 and 2 of §11.1.
* `isLiapunovStable_of_lipschitz`, `isLiapunovStable_of_lipschitz_estimate` — uniform Lipschitz
  continuity of `f` in `y` gives Liapunov stability, through the displayed estimate.
* `lemma_11_1`, `lemma_11_1_continuous` — Gronwall's lemma, as printed and with a continuous
  weight.

## Conventions

The field is `f : ℝ → ℝ → ℝ`, continuity "with respect to both variables" is continuity of
`(t, y) ↦ f t y` on the strip `I ×ˢ univ`, and `y ∈ C¹(I)` solving (11.1) is
`HasDerivWithinAt y (f t (y t)) I t` at every `t ∈ I` (one-sided at the endpoints); the
continuity of `y'` follows from that of `f`. The book's bound `r₀ < 1/L` in item 1 is not needed
and is dropped (see the errata).
-/

open Set Filter Topology MeasureTheory

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ y₀ T : ℝ} {I : Set ℝ} {y z : ℝ → ℝ}

/-- **The Cauchy problem (11.1)**: `y ∈ C¹(I)` with `y'(t) = f(t, y(t))` for `t ∈ I` and
`y(t₀) = y₀`; `ODE.IsSolutionOn` at `E = ℝ`. -/
def cauchyProblem (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) (I : Set ℝ) (y : ℝ → ℝ) : Prop :=
  ODE.IsSolutionOn f t₀ y₀ I y

/-- (11.1), unfolded: `y(t₀) = y₀` and `y'(t) = f(t, y(t))` (within `I`) for every `t ∈ I`. -/
theorem cauchyProblem_iff :
    cauchyProblem f t₀ y₀ I y ↔ y t₀ = y₀ ∧ ∀ t ∈ I, HasDerivWithinAt y (f t (y t)) I t :=
  Iff.rfl

/-- **The integral form (11.2)**: if `f` is continuous (in both variables) on the strip over
`[t₀, t₀ + T]` and `y` is continuous there, then `y` solves the Cauchy problem (11.1) on
`[t₀, t₀ + T]` iff `y(t) - y₀ = ∫_{t₀}^t f(τ, y(τ)) dτ` for every `t ∈ [t₀, t₀ + T]`. -/
theorem equation_11_2 (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T) ×ˢ univ))
    (hy : ContinuousOn y (Icc t₀ (t₀ + T))) :
    cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y ↔
      ∀ t ∈ Icc t₀ (t₀ + T), y t - y₀ = ∫ τ in t₀..t, f τ (y τ) := by
  rw [cauchyProblem, ODE.isSolutionOn_iff_integral (left_mem_Icc.2 (by linarith)) hf hy]
  exact forall₂_congr fun t _ => by rw [sub_eq_iff_eq_add']

/-- **Local existence and uniqueness** (§11.1, item 1): let `J = [t₀ - r_J, t₀ + r_J]` and
`Σ = [y₀ - r_Σ, y₀ + r_Σ]` be neighbourhoods of `t₀` and `y₀` (`r_Σ > 0`), let `f` be continuous
on `J × Σ`, satisfy the Lipschitz condition (11.3) `|f(t, y₁) - f(t, y₂)| ≤ L |y₁ - y₂|` there
with `L > 0`, and let `M` bound `|f|` on `J × Σ`. Then for every `0 < r₀ < min (r_J, r_Σ / M)`
the Cauchy problem has exactly one solution on `[t₀ - r₀, t₀ + r₀]` with values in `Σ`. The
book's third bound `r₀ < 1/L` is not needed (`ODE.exists_isSolutionOn_of_lipschitzOnWith`). -/
theorem localExistenceUniqueness {rJ rS r₀ L M : ℝ} (hL : 0 < L) (hrS : 0 < rS)
    (hf : ContinuousOn (Function.uncurry f) (Icc (t₀ - rJ) (t₀ + rJ) ×ˢ Icc (y₀ - rS) (y₀ + rS)))
    (hlip : ∀ t ∈ Icc (t₀ - rJ) (t₀ + rJ), ∀ y₁ ∈ Icc (y₀ - rS) (y₀ + rS),
      ∀ y₂ ∈ Icc (y₀ - rS) (y₀ + rS), |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hM : ∀ t ∈ Icc (t₀ - rJ) (t₀ + rJ), ∀ v ∈ Icc (y₀ - rS) (y₀ + rS), |f t v| ≤ M)
    (hr₀ : 0 < r₀) (hr₀' : r₀ < min rJ (rS / M)) :
    ∃ y : ℝ → ℝ, cauchyProblem f t₀ y₀ (Icc (t₀ - r₀) (t₀ + r₀)) y ∧
      (∀ t ∈ Icc (t₀ - r₀) (t₀ + r₀), y t ∈ Icc (y₀ - rS) (y₀ + rS)) ∧
      ∀ z : ℝ → ℝ, cauchyProblem f t₀ y₀ (Icc (t₀ - r₀) (t₀ + r₀)) z →
        (∀ t ∈ Icc (t₀ - r₀) (t₀ + r₀), z t ∈ Icc (y₀ - rS) (y₀ + rS)) →
        EqOn y z (Icc (t₀ - r₀) (t₀ + r₀)) := by
  have hrJ : r₀ ≤ rJ := (lt_min_iff.1 hr₀').1.le
  have hrM : r₀ < rS / M := (lt_min_iff.1 hr₀').2
  have hM0 : 0 ≤ M :=
    (abs_nonneg _).trans (hM t₀ ⟨by linarith, by linarith⟩ y₀ ⟨by linarith, by linarith⟩)
  have hMpos : 0 < M := lt_of_le_of_ne hM0 fun h => by rw [← h, div_zero] at hrM; linarith
  have hMr : M * r₀ ≤ rS := by
    have := (lt_div_iff₀ hMpos).1 hrM
    linarith
  have key := ODE.exists_isSolutionOn_of_lipschitzOnWith (f := f) (t₀ := t₀) (y₀ := y₀)
    (K := ⟨L, hL.le⟩) (rJ := rJ) (rS := rS) (r₀ := r₀) (M := M)
    (by rwa [Real.closedBall_eq_Icc]) (fun t ht => by
      rw [Real.closedBall_eq_Icc]
      exact LipschitzOnWith.of_dist_le_mul fun v₁ hv₁ v₂ hv₂ => by
        rw [Real.dist_eq, Real.dist_eq]
        exact hlip t ht v₁ hv₁ v₂ hv₂)
    (fun t ht v hv => by
      rw [Real.closedBall_eq_Icc] at hv
      rw [Real.norm_eq_abs]
      exact hM t ht v hv) hr₀ hrJ hrS.le hMr
  simpa only [Real.closedBall_eq_Icc, cauchyProblem] using key

/-- **Global existence and uniqueness** (§11.1, item 2): if `f` is continuous on the strip over
`[t₀, t₀ + T]` and uniformly Lipschitz continuous with respect to `y` there, i.e. (11.3) with
`J = [t₀, t₀ + T]` and `Σ = ℝ`, then the Cauchy problem has exactly one solution on `[t₀, t₀ + T]`
(pinned to `y₀` off the interval, so that uniqueness of a function on `ℝ` makes sense);
`ODE.existsUnique_isSolutionOn_of_lipschitz`. -/
theorem globalExistenceUniqueness {L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hf : ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T) ×ˢ univ))
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) :
    ∃! y : ℝ → ℝ, cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y ∧ ∀ t ∉ Icc t₀ (t₀ + T), y t = y₀ :=
  ODE.existsUnique_isSolutionOn_of_lipschitz (K := ⟨L, hL⟩) hT hf (fun t ht =>
    LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht v₁ v₂) y₀

/-- **Definition 11.1 (Liapunov stability)**: the Cauchy problem (11.1) is stable in the sense
of Liapunov on the bounded set `I` if for every perturbation `(δ₀, δ(t))` with `|δ₀| < ε` and
`|δ(t)| < ε` on `I`, the solution `z` of the perturbed problem (11.4),
`z' = f(t, z) + δ(t)`, `z(t₀) = y₀ + δ₀`, satisfies (11.5): `|y(t) - z(t)| < C ε` on `I` for a
constant `C > 0` independent of `ε`; `ODE.IsLiapunovStable` at `E = ℝ`. -/
def definition_11_1 (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) (I : Set ℝ) : Prop :=
  ODE.IsLiapunovStable f t₀ y₀ I

/-- Definition 11.1, unfolded in the book's terms. -/
theorem definition_11_1_iff :
    definition_11_1 f t₀ y₀ I ↔ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ (δ₀ : ℝ) (δ : ℝ → ℝ),
      |δ₀| < ε → ContinuousOn δ I → (∀ t ∈ I, |δ t| < ε) →
        ∀ y z : ℝ → ℝ, cauchyProblem f t₀ y₀ I y →
          cauchyProblem (fun t v => f t v + δ t) t₀ (y₀ + δ₀) I z →
            ∀ t ∈ I, |y t - z t| < C * ε := by
  simp only [definition_11_1, ODE.IsLiapunovStable, Real.norm_eq_abs, cauchyProblem]

/-- **Definition 11.1, asymptotic stability (11.6)**: Liapunov stable on every bounded interval
`[t₀, t₀ + T]`, and `|y(t) - z(t)| → 0` as `t → +∞` for the perturbed solutions on `[t₀, ∞)`
(for perturbations small enough); `ODE.IsAsymptoticallyStable` at `E = ℝ`. -/
def definition_11_1_asymptotic (f : ℝ → ℝ → ℝ) (t₀ y₀ : ℝ) : Prop :=
  ODE.IsAsymptoticallyStable f t₀ y₀

/-- Asymptotic stability, unfolded in the book's terms. -/
theorem definition_11_1_asymptotic_iff :
    definition_11_1_asymptotic f t₀ y₀ ↔
      (∀ T : ℝ, 0 < T → definition_11_1 f t₀ y₀ (Icc t₀ (t₀ + T))) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ (δ₀ : ℝ) (δ : ℝ → ℝ), |δ₀| < ε → ContinuousOn δ (Ici t₀) →
          (∀ t ∈ Ici t₀, |δ t| < ε) → ∀ y z : ℝ → ℝ, cauchyProblem f t₀ y₀ (Ici t₀) y →
            cauchyProblem (fun t v => f t v + δ t) t₀ (y₀ + δ₀) (Ici t₀) z →
              Tendsto (fun t => |y t - z t|) atTop (𝓝 0) := by
  simp only [definition_11_1_asymptotic, ODE.IsAsymptoticallyStable, definition_11_1,
    Real.norm_eq_abs, cauchyProblem]

/-- **The stability estimate of §11.1**: if `f` is uniformly Lipschitz continuous with respect to
`y` on `[t₀, t₀ + T]` with constant `L ≥ 0`, `|δ₀| ≤ ε`, `|δ(t)| ≤ ε` on the interval, `y` solves
(11.1) and `z` the perturbed problem (11.4), then
`|w(t)| = |z(t) - y(t)| ≤ (1 + |t - t₀|) ε e^{L |t - t₀|}` on the interval;
`ODE.norm_sub_le_of_lipschitz`. -/
theorem isLiapunovStable_of_lipschitz_estimate {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    {δ₀ ε : ℝ} {δ : ℝ → ℝ} (hδ₀ : |δ₀| ≤ ε) (hδ : ∀ t ∈ Icc t₀ (t₀ + T), |δ t| ≤ ε)
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hz : cauchyProblem (fun t v => f t v + δ t) t₀ (y₀ + δ₀) (Icc t₀ (t₀ + T)) z) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + T)) :
    |y t - z t| ≤ (1 + |t - t₀|) * ε * Real.exp (L * |t - t₀|) := by
  have hlip' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith ⟨L, hL⟩ (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht v₁ v₂
  have := ODE.norm_sub_le_of_lipschitz hlip' (δ₀ := δ₀) (δ := δ) (ε := ε)
    (by rwa [Real.norm_eq_abs]) (fun t ht => by rw [Real.norm_eq_abs]; exact hδ t ht) hy hz ht
  rw [abs_of_nonneg (sub_nonneg.2 ht.1)]
  exact this

/-- **Uniform Lipschitz continuity gives Liapunov stability** (§11.1): if `f` is uniformly
Lipschitz continuous with respect to `y` on `[t₀, t₀ + T]` with constant `L ≥ 0`, the Cauchy
problem is stable in the sense of Liapunov on `[t₀, t₀ + T]`, with the constant
`C = (1 + K_I) e^{L K_I}`, `K_I = max_{t ∈ I} |t - t₀| = T`; `ODE.isLiapunovStable_of_lipschitz`. -/
theorem isLiapunovStable_of_lipschitz {L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) (y₀ : ℝ) :
    definition_11_1 f t₀ y₀ (Icc t₀ (t₀ + T)) :=
  ODE.isLiapunovStable_of_lipschitz hT (L := ⟨L, hL⟩) (fun t ht =>
    LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht v₁ v₂) y₀

/-- **Lemma 11.1 (Gronwall)**: let `p` be an integrable function, nonnegative on the interval
`(t₀, t₀ + T)`, and let `g` and `φ` be continuous on `[t₀, t₀ + T]`, `g` nondecreasing. If
`φ(t) ≤ g(t) + ∫_{t₀}^t p(τ) φ(τ) dτ` for all `t ∈ [t₀, t₀ + T]`, then
`φ(t) ≤ g(t) exp (∫_{t₀}^t p(τ) dτ)` for all `t ∈ [t₀, t₀ + T]`;
`Gronwall.le_mul_exp_integral`, after replacing `p` by `max p 0`, which agrees with it almost
everywhere. (The continuity of `g` is not needed.) -/
theorem lemma_11_1 {p g φ : ℝ → ℝ} (hp : IntervalIntegrable p MeasureTheory.volume t₀ (t₀ + T))
    (hp0 : ∀ t ∈ Ioo t₀ (t₀ + T), 0 ≤ p t) (_hg : ContinuousOn g (Icc t₀ (t₀ + T)))
    (hgm : MonotoneOn g (Icc t₀ (t₀ + T))) (hφ : ContinuousOn φ (Icc t₀ (t₀ + T)))
    (h : ∀ t ∈ Icc t₀ (t₀ + T), φ t ≤ g t + ∫ τ in t₀..t, p τ * φ τ) :
    ∀ t ∈ Icc t₀ (t₀ + T), φ t ≤ g t * Real.exp (∫ τ in t₀..t, p τ) := by
  intro t ht
  -- the weight `max p 0` agrees with `p` on `(t₀, t₀ + T)`, hence almost everywhere on `(t₀, t]`
  have hae : ∀ t' ∈ Icc t₀ (t₀ + T), ∀ᵐ τ ∂MeasureTheory.volume, τ ∈ uIoc t₀ t' →
      max (p τ) 0 = p τ := by
    intro t' ht'
    have hne : ∀ᵐ τ ∂MeasureTheory.volume, τ ≠ t₀ + T := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with τ hτ hτI
    rw [uIoc_of_le ht'.1] at hτI
    exact max_eq_left (hp0 τ ⟨hτI.1, lt_of_le_of_ne (hτI.2.trans ht'.2) hτ⟩)
  have hint' : IntervalIntegrable (fun τ => max (p τ) 0) MeasureTheory.volume t₀ (t₀ + T) :=
    ⟨Integrable.sup hp.1 (integrable_zero _ _ _), Integrable.sup hp.2 (integrable_zero _ _ _)⟩
  have h1 : ∀ t' ∈ Icc t₀ (t₀ + T),
      ∫ τ in t₀..t', max (p τ) 0 * φ τ = ∫ τ in t₀..t', p τ * φ τ := fun t' ht' =>
    intervalIntegral.integral_congr_ae ((hae t' ht').mono fun τ hτ hτI => by rw [hτ hτI])
  have h2 : ∫ τ in t₀..t, max (p τ) 0 = ∫ τ in t₀..t, p τ :=
    intervalIntegral.integral_congr_ae ((hae t ht).mono fun τ hτ hτI => hτ hτI)
  rw [← h2]
  exact Gronwall.le_mul_exp_integral hint' (fun _ _ => le_max_right _ _) hgm hφ
    (fun t' ht' => by rw [h1 t' ht']; exact h t' ht') ht

/-- **Lemma 11.1 with a continuous weight**, the case §11.1 uses: for `p` continuous and
nonnegative on `[t₀, t₀ + T]`, `g` and `φ` continuous, `g` nondecreasing, the inequality
`φ ≤ g + ∫ p φ` gives `φ(t) ≤ g(t) exp (∫_{t₀}^t p)`;
`Gronwall.le_mul_exp_integral_of_continuousOn`. -/
theorem lemma_11_1_continuous {p g φ : ℝ → ℝ} (hp : ContinuousOn p (Icc t₀ (t₀ + T)))
    (hp0 : ∀ t ∈ Icc t₀ (t₀ + T), 0 ≤ p t) (_hg : ContinuousOn g (Icc t₀ (t₀ + T)))
    (hgm : MonotoneOn g (Icc t₀ (t₀ + T))) (hφ : ContinuousOn φ (Icc t₀ (t₀ + T)))
    (h : ∀ t ∈ Icc t₀ (t₀ + T), φ t ≤ g t + ∫ τ in t₀..t, p τ * φ τ) :
    ∀ t ∈ Icc t₀ (t₀ + T), φ t ≤ g t * Real.exp (∫ τ in t₀..t, p τ) := fun _ ht =>
  Gronwall.le_mul_exp_integral_of_continuousOn hp hp0 hgm hφ h ht

end QuarteroniSaccoSaleri.Chapter11
