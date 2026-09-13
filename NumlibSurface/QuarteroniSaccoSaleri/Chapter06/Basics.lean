import Numlib.Nonlinear.Order

/-!
# Quarteroni–Sacco–Saleri, chapter 6: the order of convergence

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], the opening of chapter 6: Definition 6.1 (the order of convergence of a
sequence of real approximations, in the book's quotient form with its explicit threshold `k₀` and
the restriction `p ≥ 1`), its equivalence with the backbone's `ConvergesWithOrder`
(`Numlib/Nonlinear/Order`), and the remark on the convergence factor for `p = 1`.

## Readings

* Lean's `a / 0 = 0` makes the quotient of (6.2) equal to `0` at a term with `x k = α`; that is
  harmless in a bound, so `definition_6_1` follows from `ConvergesWithOrder` without any
  hypothesis (`definition_6_1_of_convergesWithOrder`), while the converse needs the sequence to
  avoid `α` eventually (`definition_6_1_iff`).
* The remark after Definition 6.1 says that for `p = 1` a factor `C < 1` is *necessary* for
  convergence; what is true is that it is sufficient (`definition_6_1_convergenceFactor`), and
  that a bound (6.2) with `p = 1` and `C ≥ 1` says nothing about convergence. Recorded in
  `notes/book-errata.md`.
-/

open Filter Topology

namespace QuarteroniSaccoSaleri.Chapter06

/-- **Definition 6.1.** A sequence `x^{(k)}` converges to `α` with order `p ≥ 1` if it converges
and there are `C > 0` and `k₀` with `|x^{(k+1)} - α| / |x^{(k)} - α|^p ≤ C` for all `k ≥ k₀`
(the displayed condition (6.2)). -/
def definition_6_1 (x : ℕ → ℝ) (α : ℝ) (p : ℝ) : Prop :=
  1 ≤ p ∧ Tendsto x atTop (𝓝 α) ∧
    ∃ C > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, |x (k + 1) - α| / |x k - α| ^ p ≤ C

/-- The backbone's `ConvergesWithOrder` (the product form of (6.2)) implies Definition 6.1 for
`p ≥ 1`, with no hypothesis on the sequence: at a term with `x k = α` the quotient is `0` by Lean's
convention. -/
theorem definition_6_1_of_convergesWithOrder {x : ℕ → ℝ} {α p : ℝ} (hp : 1 ≤ p)
    (h : ConvergesWithOrder x α p) : definition_6_1 x α p := by
  obtain ⟨hlim, C, hC, hbound⟩ := h
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hbound
  refine ⟨hp, hlim, C, hC, k₀, fun k hk => ?_⟩
  have hk' := hk₀ k hk
  simp only [Real.norm_eq_abs] at hk'
  rcases eq_or_ne (x k) α with hxk | hxk
  · rw [hxk, sub_self, abs_zero, Real.zero_rpow (by linarith), div_zero]
    exact hC.le
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (sub_ne_zero.2 hxk)) p)).2 hk'

/-- **Definition 6.1 is the backbone's `ConvergesWithOrder`** with `p ≥ 1`, for a sequence that
eventually avoids `α`. The hypothesis is needed for the forward direction: at a term with
`x k = α` the quotient form reads `0 ≤ C` while the product form forces `x (k + 1) = α`. -/
theorem definition_6_1_iff {x : ℕ → ℝ} {α p : ℝ} (hx : ∀ᶠ k in atTop, x k ≠ α) :
    definition_6_1 x α p ↔ 1 ≤ p ∧ ConvergesWithOrder x α p := by
  refine ⟨fun ⟨hp, hlim, C, hC, k₀, hk₀⟩ => ⟨hp, hlim, C, hC, ?_⟩,
    fun ⟨hp, h⟩ => definition_6_1_of_convergesWithOrder hp h⟩
  filter_upwards [hx, eventually_ge_atTop k₀] with k hk hk₀'
  have := hk₀ k hk₀'
  simp only [Real.norm_eq_abs]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (sub_ne_zero.2 hk)) p)).1 this

/-- **The remark after Definition 6.1, in its true direction.** If `0 < C < 1` and
`|x^{(k+1)} - α| ≤ C |x^{(k)} - α|` for all `k ≥ k₀`, then `x^{(k)}` converges to `α` with order
`1`, and `C` is called the convergence factor. The book says such a `C < 1` is "necessary" for
convergence when `p = 1`; it is sufficient — a bound (6.2) with `C ≥ 1` and `p = 1` is satisfied
by many non-convergent sequences (`tendsto_of_eventually_norm_sub_succ_le`). -/
theorem definition_6_1_convergenceFactor {x : ℕ → ℝ} {α C : ℝ} {k₀ : ℕ} (hC0 : 0 < C)
    (hC : C < 1) (h : ∀ k ≥ k₀, |x (k + 1) - α| ≤ C * |x k - α|) : definition_6_1 x α 1 :=
  definition_6_1_of_convergesWithOrder le_rfl
    (convergesWithOrder_one_of_eventually_norm_sub_succ_le hC0 hC
      (eventually_atTop.2 ⟨k₀, fun k hk => by simpa [Real.norm_eq_abs] using h k hk⟩))

end QuarteroniSaccoSaleri.Chapter06
