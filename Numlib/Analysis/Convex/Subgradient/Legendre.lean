import Numlib.Analysis.Convex.Subgradient.Gradient

/-!
# The Legendre transformation

Let `f` be a convex function, differentiable on an open set `C`. Its *Legendre conjugate* is the
pair `(D, g)` with `D = ∇f(C)` the image of the gradient mapping and `g y = ⟨x, y⟩ - f x` for any
`x` with `∇f x = y`. The value of `g` does not depend on which such `x` is chosen, and `g` is
nothing but the restriction of the Fenchel conjugate `f*` to `D`; in particular `D ⊆ dom f*`.

## Main results

* `legendreDom` — the set `D`, the image of the gradient mapping, with
  `legendreDom_subset_dom_conj` for `D ⊆ dom f*`.
* `conj_eq_of_hasGradientAtFn` — `f*(∇f x) = ⟨x, ∇f x⟩ - f x`: both the formula for `g` and, at a
  stroke, its well-definedness (Theorem 26.4 in [^1]).

## Implementation notes

There is deliberately no `legendreConj` definition: `y ↦ ⟨(∇f)⁻¹ y, y⟩ - f ((∇f)⁻¹ y)` would need
a choice function and would then have to be proved equal to `conj B f` on `D` anyway, and
`conj_eq_of_hasGradientAtFn` is that equality without the detour.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26.
-/

open Set Filter Topology

namespace ConvexAnalysis

section Legendre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x : E}
  {y : StrongDual ℝ E}

private theorem eq_coe_of_coe_add_eq_coe {c : EReal} {r s : ℝ}
    (h : ((r : ℝ) : EReal) + c = ((s : ℝ) : EReal)) : c = ((s - r : ℝ) : EReal) := by
  rcases eq_or_ne c ⊤ with rfl | hct
  · simp at h
  rcases eq_or_ne c ⊥ with rfl | hcb
  · simp at h
  obtain ⟨t, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hct)
  rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
  rw [EReal.coe_eq_coe_iff]
  linarith

/-- A function is finite wherever it has a gradient. -/
theorem HasGradientAtFn.exists_coe (h : HasGradientAtFn f y x) :
    ∃ r : ℝ, f x = ((r : ℝ) : EReal) := by
  obtain ⟨g, hfg, -⟩ := h
  exact ⟨g x, hfg.self_of_nhds⟩

/-- Where `f` is differentiable, Fenchel's inequality holds with equality at `(x, ∇f x)`. -/
theorem HasGradientAtFn.add_conj_eq (hf : ConvexFn f) (h : HasGradientAtFn f y x) :
    f x + conj (topDualPairing ℝ E).flip f y = ((y x : ℝ) : EReal) :=
  (h.proper hf).mem_subgradient_iff_add_conj_eq.1 (h.mem_subgradient hf)

/-- The Legendre conjugate at `∇f x` *is* `f*` at `∇f x`, given by the formula
`⟨x, ∇f x⟩ - f x`. -/
theorem conj_eq_of_hasGradientAtFn (hf : ConvexFn f) (h : HasGradientAtFn f y x) {r : ℝ}
    (hr : f x = ((r : ℝ) : EReal)) :
    conj (topDualPairing ℝ E).flip f y = ((y x - r : ℝ) : EReal) :=
  eq_coe_of_coe_add_eq_coe (by rw [← hr]; exact h.add_conj_eq hf)

/-- **Well-definedness**: `⟨x, y⟩ - f x` is the same for every `x` with `∇f x = y`, because it is
`f* y`. So `∇f` need not be one-to-one for `g` to be single-valued. -/
theorem sub_eq_sub_of_hasGradientAtFn (hf : ConvexFn f) {x₁ x₂ : E} {r₁ r₂ : ℝ}
    (h₁ : HasGradientAtFn f y x₁) (h₂ : HasGradientAtFn f y x₂)
    (hr₁ : f x₁ = ((r₁ : ℝ) : EReal)) (hr₂ : f x₂ = ((r₂ : ℝ) : EReal)) :
    y x₁ - r₁ = y x₂ - r₂ := by
  have he : ((y x₁ - r₁ : ℝ) : EReal) = ((y x₂ - r₂ : ℝ) : EReal) := by
    rw [← conj_eq_of_hasGradientAtFn hf h₁ hr₁, ← conj_eq_of_hasGradientAtFn hf h₂ hr₂]
  exact_mod_cast he

/-- The domain `D` of the Legendre conjugate, the image of the gradient mapping. Every gradient is
attained at an interior point of `dom f` (`HasGradientAtFn.mem_interior_dom`), so no interiority
side condition is needed here. -/
def legendreDom (f : E → EReal) : Set (StrongDual ℝ E) := {y | ∃ x, HasGradientAtFn f y x}

theorem mem_legendreDom_iff : y ∈ legendreDom f ↔ ∃ x, HasGradientAtFn f y x := Iff.rfl

theorem HasGradientAtFn.mem_legendreDom (h : HasGradientAtFn f y x) : y ∈ legendreDom f := ⟨x, h⟩

theorem exists_mem_interior_dom_of_mem_legendreDom (hy : y ∈ legendreDom f) :
    ∃ x ∈ interior (dom f), HasGradientAtFn f y x := by
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx.mem_interior_dom, hx⟩

/-- Every gradient of `f` is a point where `f*` is finite: `D ⊆ dom f*`. -/
theorem legendreDom_subset_dom_conj (hf : ConvexFn f) :
    legendreDom f ⊆ dom (conj (topDualPairing ℝ E).flip f) := by
  rintro y ⟨x, hx⟩
  obtain ⟨r, hr⟩ := hx.exists_coe
  rw [mem_dom, conj_eq_of_hasGradientAtFn hf hx hr]
  exact EReal.coe_lt_top _

end Legendre

end ConvexAnalysis
