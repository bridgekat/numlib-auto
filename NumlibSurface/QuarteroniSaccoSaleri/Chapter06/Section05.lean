import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section03

/-!
# Quarteroni–Sacco–Saleri §6.5: stopping criteria

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §6.5: the two stopping tests for a sequence converging to a zero `α`
of `f`, as the limits that justify them — the residual test with the error estimate obtained by
"applying the estimate (6.6)" (`residualTest`, `residualTest_simple`), and the increment test
(6.31) (`equation_6_31`). The backbone is `IsRootOfMultiplicity.tendsto_abs_sub_div_abs_rpow`
(`Numlib/Analysis/Calculus/RootMultiplicity`) and `tendsto_sub_div_sub_succ_of_hasDerivAt`
(`Numlib/Nonlinear/Order`). Example 6.9 is a numerical run, and the three qualitative
conclusions about `|f'(α)| ≃ 1`, `≪ 1`, `≫ 1` are readings of the factor `1 / |f'(α)|`.

The book's error is `e^{(k)} = α - x^{(k)}`; with that sign the constant of (6.31) comes out as
printed, `1 / (1 - φ'(α))`. Both limits need `x^{(k)} ≠ α`, which the book does not say.
-/

open Filter Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

variable {f φ : ℝ → ℝ} {α : ℝ}

-- `α ≠ 0` is the book's standing assumption for a relative error; the limit is trivially true
-- at `α = 0`, where both sides are `0` under Lean's `a / 0 = 0`.
set_option linter.unusedVariables false in
/-- **The residual test's error estimate** (the display after item 1 of §6.5). If `x^{(k)} → α`
without reaching it, where `α ≠ 0` is a root of `f ∈ C^m` of multiplicity `m ≥ 1`, then
`|e^{(k)}| / |α| ≲ (m! / (|f^{(m)}(α)| |α|^m))^{1/m} |f(x^{(k)})|^{1/m}` in the sense that the
ratio of the two sides tends to `1`: (6.6) along the sequence. `equation_6_4` composed with
`x^{(k)} → α` in `𝓝[≠] α`, and the constant identity `rpow_div_abs_eq`. -/
theorem residualTest {m : ℕ} (hm : 1 ≤ m) (hf : ContDiffAt ℝ m f α)
    (hα : IsRootOfMultiplicity f α m) (hα0 : α ≠ 0) {x : ℕ → ℝ} (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (|x k - α| / |α|) / |f (x k)| ^ (1 / (m : ℝ))) atTop
      (𝓝 ((m.factorial / (|iteratedDeriv m f α| * |α| ^ m)) ^ (1 / (m : ℝ)))) := by
  have h := ((equation_6_4 hm hf hα).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)).div_const |α|
  rw [rpow_div_abs_eq (by positivity) hm, div_div] at h
  refine h.congr fun k => ?_
  simp only [Function.comp]
  rw [div_right_comm]

/-- **The residual test at a simple root**: "the error is bound to the residual by the factor
`1 / |f'(α)|`" — `|x^{(k)} - α| / |f(x^{(k)})| → 1 / |f'(α)|` along a sequence converging to a
simple root `α` without reaching it. The `m = 1` case of `residualTest`, without the division by
`|α|` (so `α = 0` is allowed). -/
theorem residualTest_simple (hf : ContDiffAt ℝ 1 f α) (hα : f α = 0) (hf' : deriv f α ≠ 0)
    {x : ℕ → ℝ} (hne : ∀ k, x k ≠ α) (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => |x k - α| / |f (x k)|) atTop (𝓝 (1 / |deriv f α|)) := by
  have hroot : IsRootOfMultiplicity f α 1 := isRootOfMultiplicity_one_iff.2 ⟨hα, hf'⟩
  have h := (equation_6_4 le_rfl (by simpa using hf) hroot).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
  simp only [Function.comp_def] at h
  simpa using h

/-- **(6.31), the increment test.** For a fixed-point orbit `x^{(k+1)} = φ(x^{(k)})` converging to
`α = φ(α)` without reaching it, with `φ` differentiable at `α` and `φ'(α) ≠ 1`,
`e^{(k)} ≃ (x^{(k+1)} - x^{(k)}) / (1 - φ'(α))` with `e^{(k)} = α - x^{(k)}`, as the limit of the
ratios: `(α - x^{(k)}) / (x^{(k+1)} - x^{(k)}) → 1 / (1 - φ'(α))` (and the increments are
eventually nonzero). The test is unreliable when `φ'(α)` is close to `1`, optimal for second-order
methods where `φ'(α) = 0` (Newton), still satisfactory for `-1 < φ'(α) < 0`.
`tendsto_sub_div_sub_succ_of_hasDerivAt`. -/
theorem equation_6_31 (hφ : DifferentiableAt ℝ φ α) (hα : φ α = α) (h1 : deriv φ α ≠ 1)
    {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    (∀ᶠ k in atTop, x (k + 1) - x k ≠ 0) ∧
      Tendsto (fun k => (α - x k) / (x (k + 1) - x k)) atTop (𝓝 (1 / (1 - deriv φ α))) :=
  tendsto_sub_div_sub_succ_of_hasDerivAt hφ.hasDerivAt hα h1 hx hne hlim

end QuarteroniSaccoSaleri.Chapter06
