import Numlib.Nonlinear.Bisection
import Numlib.Nonlinear.Secant
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Basics

/-!
# Quarteroni–Sacco–Saleri §6.2: a geometric approach to rootfinding

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §6.2: the bisection method (Property 6.1, the sequence of §6.2.1,
(6.8)–(6.9)) and the chord (6.12), secant (6.13)–(6.14) with Property 6.2, regula falsi (6.15) and
Newton (6.16) iterations of §6.2.2, each defined as the book writes it and identified with the
backbone's `Bisection`, `Chord`, `Secant`, `RegulaFalsi` and `Newton.scalarStep`
(`Numlib/Nonlinear/{Bisection, Secant, ScalarNewton}`). The convergence statements the book defers
to §6.3.1 (chord linear, Newton quadratic) are in `Section03`.

## Readings

* Bisection: the tie `f(x^{(k)}) = 0`, undefined in the prose, follows Program 46 (`b := x^{(k)}`);
  the sign property is `f(a^{(k)}) f(b^{(k)}) ≤ 0` (the book's `< 0` fails at an exact hit); the
  bound (6.8)–(6.9) is the book's `(b - a) / 2^k`, weaker than the backbone's `(b - a) / 2^{k+1}`.
* Property 6.2 needs `f'(α) ≠ 0`, which the book does not list, and the two initial values must
  be distinct and different from `α` (a start at `α` stops the method at once).
* The linear order of regula falsi (`regulaFalsi_order_one`) is the backbone's
  `RegulaFalsi.convergesWithOrder_one_iterate`; it needs `f` twice continuously
  differentiable at the root with `f'(α) ≠ 0`, but not the `f''(α) ≠ 0` the classical
  argument through the eventually frozen endpoint would use.
-/

open Filter Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

/-! ### §6.2.1 The bisection method -/

section Bisection

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **Property 6.1 (theorem of zeros for continuous functions).** A continuous
`f : [a, b] → ℝ` with `f(a) f(b) < 0` has a zero `α ∈ (a, b)`. -/
theorem property_6_1 (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b < 0) :
    ∃ α ∈ Ioo a b, f α = 0 :=
  exists_eq_zero_Ioo_of_mul_neg hab hf h

/-- The subintervals `I_k = [a^{(k)}, b^{(k)}]` of the bisection method of §6.2.1, as pairs of
endpoints: the backbone's `Bisection.bracket`. -/
noncomputable def bisectionInterval (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ × ℝ :=
  Bisection.bracket f a b k

/-- **The bisection sequence** of §6.2.1: `x^{(k)} = (a^{(k)} + b^{(k)}) / 2`, the midpoint of
`I_k`, with `I_{k+1}` the half of `I_k` on which `f` changes sign (the tie `f(x^{(k)}) = 0` is
resolved as in Program 46: `b^{(k+1)} := x^{(k)}`). The backbone's `Bisection.iterate`. -/
noncomputable def bisection (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ :=
  Bisection.iterate f a b k

/-- **(6.8).** `|I_k| = (b - a) / 2^k`, the intervals are nested, and the sign property
`f(a^{(k)}) f(b^{(k)}) ≤ 0` persists (the book's `< 0` fails as soon as an iterate is an exact
root). `Bisection.bracket_sub`, `Bisection.bracket_nested`, `Bisection.bracket_mul_nonpos`. -/
theorem equation_6_8 (hab : a ≤ b) (h : f a * f b ≤ 0) (k : ℕ) :
    (bisectionInterval f a b k).2 - (bisectionInterval f a b k).1 = (b - a) / 2 ^ k ∧
      Icc (bisectionInterval f a b (k + 1)).1 (bisectionInterval f a b (k + 1)).2 ⊆
        Icc (bisectionInterval f a b k).1 (bisectionInterval f a b k).2 ∧
      f (bisectionInterval f a b k).1 * f (bisectionInterval f a b k).2 ≤ 0 :=
  ⟨Bisection.bracket_sub f a b k, Bisection.bracket_nested hab k, Bisection.bracket_mul_nonpos h k⟩

/-- **Global convergence of bisection** (the sentences after (6.8)): for `f` continuous on
`[a, b]` with `f(a) f(b) < 0` there is a root `α ∈ (a, b)` with `|e^{(k)}| ≤ (b - a) / 2^k` for
all `k`, so `x^{(k)} → α`. `Bisection.exists_tendsto_iterate`, whose root lies in the open interval
because `f(a), f(b) ≠ 0`. -/
theorem bisection_tendsto (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b < 0) :
    ∃ α ∈ Ioo a b, f α = 0 ∧ (∀ k, |bisection f a b k - α| ≤ (b - a) / 2 ^ k) ∧
      Tendsto (bisection f a b) atTop (𝓝 α) := by
  obtain ⟨α, hα, hfα, hlim, -, hbound⟩ := Bisection.exists_tendsto_iterate hab hf h.le
  have hfa : f a ≠ 0 := fun h0 => by simp [h0] at h
  have hfb : f b ≠ 0 := fun h0 => by simp [h0] at h
  refine ⟨α, ⟨lt_of_le_of_ne hα.1 fun heq => hfa (heq ▸ hfα),
    lt_of_le_of_ne hα.2 fun heq => hfb (heq.symm ▸ hfα)⟩, hfα, fun k => ?_, hlim⟩
  refine (hbound k).trans ?_
  have : 0 ≤ b - a := sub_nonneg.2 hab
  rw [pow_succ, ← div_div]
  exact half_le_self (by positivity)

/-- **(6.9), the iteration count.** With `α` the root of `bisection_tendsto` and a tolerance
`ε > 0`, `|x^{(m)} - α| ≤ ε` as soon as `m ≥ log₂(b - a) - log₂ ε`.
`Bisection.abs_iterate_sub_le_of_le_logb`, which needs only `log₂((b - a) / ε) ≤ m + 1`. -/
theorem equation_6_9 (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b < 0) :
    ∃ α ∈ Ioo a b, f α = 0 ∧ ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      Real.logb 2 (b - a) - Real.logb 2 ε ≤ m → |bisection f a b m - α| ≤ ε := by
  obtain ⟨α, hα, hfα, hlim, hcount⟩ := Bisection.abs_iterate_sub_le_of_le_logb hab hf h.le
  have hfa : f a ≠ 0 := fun h0 => by simp [h0] at h
  have hfb : f b ≠ 0 := fun h0 => by simp [h0] at h
  have hab' : a < b := lt_of_le_of_ne hab fun heq => by subst heq; exact hfa (by nlinarith)
  refine ⟨α, ⟨lt_of_le_of_ne hα.1 fun heq => hfa (heq ▸ hfα),
    lt_of_le_of_ne hα.2 fun heq => hfb (heq.symm ▸ hfα)⟩, hfα, fun m ε hε hm => ?_⟩
  refine hcount m ε hε ?_
  rw [Real.logb_div (sub_ne_zero.2 hab'.ne') hε.ne']
  linarith

end Bisection

/-! ### §6.2.2 The chord, secant, regula falsi and Newton methods -/

section Chord

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **(6.12), the chord method**: `x^{(k+1)} = x^{(k)} - (b - a) / (f(b) - f(a)) · f(x^{(k)})`, the
iteration of `Chord.step` with the fixed slope `q = (f(b) - f(a)) / (b - a)`. -/
noncomputable def chord (f : ℝ → ℝ) (a b x₀ : ℝ) (k : ℕ) : ℝ :=
  (Chord.step f ((f b - f a) / (b - a)))^[k] x₀

/-- The chord recurrence, as the book writes it. -/
theorem chord_succ (f : ℝ → ℝ) (a b x₀ : ℝ) (k : ℕ) :
    chord f a b x₀ (k + 1) = chord f a b x₀ k - (b - a) / (f b - f a) * f (chord f a b x₀ k) := by
  rw [chord, Function.iterate_succ_apply', Chord.step, div_div_eq_mul_div, chord]
  ring

/-- The chord method is the Banach-space chord method `Newton.chordIterate` of
`Numlib/Nonlinear/Newton` with the frozen derivative `A : ℝ ≃L[ℝ] ℝ`, `A 1 = q`. -/
theorem chord_eq_chordIterate (A : ℝ ≃L[ℝ] ℝ) (hA : A 1 = (f b - f a) / (b - a)) (x₀ : ℝ)
    (k : ℕ) : chord f a b x₀ k = Newton.chordIterate f A x₀ k := by
  rw [chord, Newton.chordIterate, funext (Chord.step_eq_chordStep A hA)]

end Chord

section Secant

variable {f : ℝ → ℝ} {α : ℝ}

/-- **(6.13)–(6.14), the secant method**: from `x^{(-1)} = xm1`, `x^{(0)} = x₀`,
`x^{(k+1)} = x^{(k)} - (x^{(k)} - x^{(k-1)}) / (f(x^{(k)}) - f(x^{(k-1)})) · f(x^{(k)})`; the
slope `q_k` of (6.13) is the divided difference `f[x^{(k-1)}, x^{(k)}]`. The backbone's
`Secant.iterate`. -/
noncomputable def secant (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) : ℝ :=
  Secant.iterate f xm1 x₀ k

/-- The secant recurrence (6.14) in the book's form, for `k ≥ 1`
(`Secant.iterate_add_two`); the first step from the two initial values is `Secant.iterate_one`. -/
theorem secant_succ (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) :
    secant f xm1 x₀ (k + 2) = secant f xm1 x₀ (k + 1) -
      (secant f xm1 x₀ (k + 1) - secant f xm1 x₀ k) /
        (f (secant f xm1 x₀ (k + 1)) - f (secant f xm1 x₀ k)) * f (secant f xm1 x₀ (k + 1)) :=
  Secant.iterate_add_two f xm1 x₀ k

/-- **Property 6.2.** Let `f ∈ C²(J)` on a neighbourhood `J` of a root `α` with `f''(α) ≠ 0`
(and `f'(α) ≠ 0`, which the book omits: at a multiple root the secant method is linear). Then
there is `ε > 0` such that for all initial values `x^{(-1)}, x^{(0)} ∈ (α - ε, α + ε)` — distinct
and different from `α` — the sequence (6.14) converges to `α` with order `p = (1 + √5) / 2`.
`Secant.exists_ball_convergesWithOrder_goldenRatio`. -/
theorem property_6_2 (hf : ContDiffAt ℝ 2 f α) (hα : f α = 0) (hf' : deriv f α ≠ 0)
    (hf'' : iteratedDeriv 2 f α ≠ 0) :
    ∃ ε > 0, ∀ xm1 ∈ Ioo (α - ε) (α + ε), ∀ x₀ ∈ Ioo (α - ε) (α + ε), xm1 ≠ x₀ → xm1 ≠ α →
      x₀ ≠ α → definition_6_1 (secant f xm1 x₀) α Real.goldenRatio := by
  obtain ⟨ε, hε, h⟩ := Secant.exists_ball_convergesWithOrder_goldenRatio hα hf hf' hf''
  refine ⟨ε, hε, fun xm1 hxm1 x₀ hx₀ hne h1 h2 => ?_⟩
  rw [← Real.ball_eq_Ioo] at hxm1 hx₀
  exact definition_6_1_of_convergesWithOrder Real.one_lt_goldenRatio.le
    (h xm1 hxm1 x₀ hx₀ hne h1 h2)

end Secant

section RegulaFalsi

variable {f : ℝ → ℝ} {xm1 x₀ : ℝ}

/-- **(6.15), the regula falsi method**: the secant step through `x^{(k)}` and the latest earlier
iterate `x^{(k')}` with `f(x^{(k')}) f(x^{(k)}) < 0`, from a bracketing pair `x^{(-1)}, x^{(0)}`.
The backbone's `RegulaFalsi.iterate`. -/
noncomputable def regulaFalsi (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) : ℝ :=
  RegulaFalsi.iterate f xm1 x₀ k

/-- "Unlike the secant method, the iterates generated by (6.15) are all contained within the
starting interval `[x^{(-1)}, x^{(0)}]`." `RegulaFalsi.iterate_mem_uIcc`. -/
theorem regulaFalsi_mem_uIcc (h : f x₀ * f xm1 < 0) (k : ℕ) :
    regulaFalsi f xm1 x₀ k ∈ uIcc xm1 x₀ :=
  RegulaFalsi.iterate_mem_uIcc h k

/-- **"The Regula Falsi method … has linear convergence order"** (§6.2.2, quoted there from
Ralston and Rabinowitz without proof): from a bracketing pair `f(x^{(0)}) f(x^{(-1)}) < 0` of a
function continuous on `[[x^{(-1)}, x^{(0)}]]` whose only zero there is `α`, at which `f` is twice
continuously differentiable with `f'(α) ≠ 0`, the iterates converge to `α` with order `1` in the
sense of Definition 6.1. `RegulaFalsi.tendsto_iterate` and
`RegulaFalsi.convergesWithOrder_one_iterate`. -/
theorem regulaFalsi_order_one (hf : ContinuousOn f (uIcc xm1 x₀)) (h : f x₀ * f xm1 < 0) {α : ℝ}
    (huniq : ∀ y ∈ uIcc xm1 x₀, f y = 0 → y = α) (hC : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) :
    Tendsto (regulaFalsi f xm1 x₀) atTop (𝓝 α) ∧ definition_6_1 (regulaFalsi f xm1 x₀) α 1 :=
  ⟨RegulaFalsi.tendsto_iterate hf h huniq,
    definition_6_1_of_convergesWithOrder le_rfl
      (RegulaFalsi.convergesWithOrder_one_iterate hf h huniq hC hf')⟩

end RegulaFalsi

section Newton

/-- **(6.16), Newton's method**: `x^{(k+1)} = x^{(k)} - f(x^{(k)}) / f'(x^{(k)})`, with `f'` passed
as a function as in the book's Program 50 (`dfun`); the theorems take `f' = deriv f`. The
iteration of the backbone's `Newton.scalarStep`. -/
noncomputable def newton (f f' : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) : ℝ :=
  (Newton.scalarStep f f')^[k] x₀

/-- The Newton recurrence, as the book writes it. -/
theorem newton_succ (f f' : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) :
    newton f f' x₀ (k + 1) = newton f f' x₀ k - f (newton f f' x₀ k) / f' (newton f f' x₀ k) := by
  rw [newton, Function.iterate_succ_apply']
  rfl

/-- The scalar Newton method is the Banach-space one of `Numlib/Nonlinear/Newton` with the
derivative `f' x • id`. `Newton.scalarStep_eq_step`. -/
theorem newton_eq_iterate (f f' : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) :
    newton f f' x₀ k = Newton.iterate f (fun x => f' x • ContinuousLinearMap.id ℝ ℝ) x₀ k := by
  rw [newton, Newton.iterate, funext (Newton.scalarStep_eq_step f f')]

end Newton

end QuarteroniSaccoSaleri.Chapter06
