/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpOrder`, beside `MeasureTheory.Lp.coeFn_le`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Convexity of order intervals in `L^p`

In the lattice `L^p(μ)` of real functions, a lower bound of two elements is a lower bound of their
convex combinations (`MeasureTheory.Lp.le_smul_add_smul_of_le`), so the order interval
`{f | c ≤ f}` is convex (`MeasureTheory.Lp.convex_Ici`). This is what makes the admissible set
`{v ∈ H¹₀(Ω) | v ≥ ψ a.e.}` of an obstacle problem convex.
-/

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- In `L^p(μ)`, a lower bound of two functions is a lower bound of their convex combinations:
`h ≤ f`, `h ≤ g`, `a, b ≥ 0`, `a + b = 1` give `h ≤ a • f + b • g`. -/
theorem le_smul_add_smul_of_le {h f g : Lp ℝ p μ} (hf : h ≤ f) (hg : h ≤ g) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) : h ≤ a • f + b • g := by
  rw [← Lp.coeFn_le] at hf hg ⊢
  filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g, hf, hg]
    with x h1 h2 h3 hfx hgx
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  calc h x = a * h x + b * h x := by rw [← add_mul, hab, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hfx ha) (mul_le_mul_of_nonneg_left hgx hb)

/-- In `L^p(μ)` the order interval `Ici c = {f | c ≤ f}` is convex. -/
theorem convex_Ici (c : Lp ℝ p μ) : Convex ℝ (Set.Ici c) :=
  fun _ hf _ hg _ _ ha hb hab ↦ le_smul_add_smul_of_le hf hg ha hb hab

end MeasureTheory.Lp
