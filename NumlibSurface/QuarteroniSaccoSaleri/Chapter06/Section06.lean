import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section03

/-!
# Quarteroni–Sacco–Saleri §6.6: post-processing techniques for iterative methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §6.6: Aitken's Δ² acceleration ((6.33)–(6.38), Property 6.7) and the
techniques for multiple roots ((6.39)–(6.40)), with Exercise 6.5 (Steffensen's method) attached
because it is the concrete instance of Property 6.7's `p = 1` case and the correct reading of its
last clause. The backbone is `Numlib/Nonlinear/{Order, ScalarNewton}`. The book indexes the
increment ratio (6.33) and Aitken's formula (6.36) from `k ≥ 2`; the backbone's `aitkenRatio` and
`aitkenExtrapolation` start at `k = 0`, and `equation_6_33_eq`, `equation_6_36_eq` and
`equation_6_40_eq` are the shifts.

## Readings

* (6.34) needs `φ'(α) ≠ 1` and an orbit avoiding `α`; the book's derivation assumes linear
  convergence, which is more than needed (for Newton, `φ'(α) = 0` and the limit is `0`).
* Property 6.7's last clause — "if `α` has multiplicity `m ≥ 2` and the method is first-order
  convergent, then Aitken's method converges linearly with factor `1 - 1/m`" — is false as
  printed: for any `φ` differentiable at `α` with `φ'(α) ≠ 1`, `φ_Δ'(α) = 0`
  (`equation_6_38_fixedPoints`), so Aitken's method is superlinear. The statement of
  Isaacson–Keller that the book paraphrases concerns the iteration function `φ = id + f`, whose
  derivative at a multiple root is `1`, i.e. Steffensen's method; that is `property_6_7_multiple`.
  Recorded in `notes/book-errata.md`.
* Property 6.7 for `p ≥ 2` is stated by the book without proof; the backbone proves it under
  `φ ∈ C^p` (the book's neighbourhood hypothesis is `C^{2p}`, which is not needed).
-/

open Filter Set Topology
open scoped fwdDiff

namespace QuarteroniSaccoSaleri.Chapter06

/-! ### §6.6.1 Aitken's acceleration -/

section Aitken

variable {φ : ℝ → ℝ} {α : ℝ}

/-- **(6.33), the increment ratio** `λ^{(k)} = (x^{(k)} - x^{(k-1)}) / (x^{(k-1)} - x^{(k-2)})` for
`k ≥ 2` (junk at `k < 2`, where `k - 1` and `k - 2` truncate). -/
noncomputable def equation_6_33 (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (x k - x (k - 1)) / (x (k - 1) - x (k - 2))

/-- The increment ratio is the backbone's `aitkenRatio`, shifted by two. -/
theorem equation_6_33_eq (x : ℕ → ℝ) (k : ℕ) : equation_6_33 x (k + 2) = aitkenRatio x k := by
  simp [equation_6_33, aitkenRatio]

/-- **(6.34).** For a fixed-point orbit `x^{(k+1)} = φ(x^{(k)})` converging to `α = φ(α)` without
reaching it, with `φ` differentiable at `α` and `φ'(α) ≠ 1`, `λ^{(k)} → φ'(α)`. The book's
derivation assumes linear convergence; `φ'(α) ≠ 1` is what it needs. `tendsto_aitkenRatio` with
`tendsto_sub_div_sub_of_hasDerivAt`. -/
theorem equation_6_34 (hφ : DifferentiableAt ℝ φ α) (hα : φ α = α) (h1 : deriv φ α ≠ 1)
    {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) : Tendsto (equation_6_33 x) atTop (𝓝 (deriv φ α)) := by
  have h := tendsto_aitkenRatio hne (tendsto_sub_div_sub_of_hasDerivAt hφ.hasDerivAt hα hx hne hlim)
    h1
  rw [← tendsto_add_atTop_iff_nat 2]
  exact h.congr fun k => (equation_6_33_eq x k).symm

/-- **(6.36), Aitken's extrapolation formula**
`x̂^{(k)} = x^{(k)} - (x^{(k)} - x^{(k-1)})² / ((x^{(k)} - x^{(k-1)}) - (x^{(k-1)} - x^{(k-2)}))`
for `k ≥ 2`. -/
noncomputable def equation_6_36 (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  x k - (x k - x (k - 1)) ^ 2 / ((x k - x (k - 1)) - (x (k - 1) - x (k - 2)))

/-- Aitken's formula is the backbone's `aitkenExtrapolation`, shifted by two. -/
theorem equation_6_36_eq (x : ℕ → ℝ) (k : ℕ) :
    equation_6_36 x (k + 2) = aitkenExtrapolation x k := by
  simp [equation_6_36, aitkenExtrapolation]

/-- **(6.37), the Δ² form.** With `Δx^{(k)} = x^{(k)} - x^{(k-1)}` and
`Δ²x^{(k)} = Δx^{(k+1)} - Δx^{(k)}`, `x̂^{(k)} = x^{(k)} - (Δx^{(k)})² / Δ²x^{(k-1)}` for `k ≥ 2` —
in Mathlib's forward difference `Δ_[1]`, whose `Δ_[1] x (k - 1) = x^{(k)} - x^{(k-1)}` is the
book's `Δx^{(k)}`. `aitkenExtrapolation_eq_sub_div_fwdDiff`. -/
theorem equation_6_37 (x : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) :
    equation_6_36 x k = x k - (Δ_[1] x (k - 1)) ^ 2 / (Δ_[1]^[2] x (k - 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [equation_6_36_eq, aitkenExtrapolation_eq_sub_div_fwdDiff]
  simp

/-- **(6.38), the iteration function of Aitken's method**
`φ_Δ(x) = (x φ(φ(x)) - φ(x)²) / (φ(φ(x)) - 2 φ(x) + x)`, extended by `x` itself where the
denominator vanishes; Aitken's method is the fixed-point iteration `x^{(k+1)} = φ_Δ(x^{(k)})`
(Program 55). The backbone's `aitkenIterationFunction`. -/
noncomputable def equation_6_38 (φ : ℝ → ℝ) : ℝ → ℝ := aitkenIterationFunction φ

/-- **The two remarks after (6.38).** (i) If `φ` is differentiable at `α = φ(α)` with
`φ'(α) ≠ 1` then `φ_Δ(x) → α` as `x → α` (the book's L'Hôpital argument) — indeed `φ_Δ` is
differentiable at `α` with `φ_Δ'(α) = 0` — and `φ_Δ(α) = α`; (ii) where the denominator does not
vanish the fixed points of `φ_Δ` are those of `φ`. `hasDerivAt_aitkenIterationFunction_zero`,
`aitkenIterationFunction_apply_self`, `aitkenIterationFunction_eq_self_iff`. -/
theorem equation_6_38_fixedPoints (hφ : DifferentiableAt ℝ φ α) (hα : φ α = α)
    (h1 : deriv φ α ≠ 1) :
    Tendsto (equation_6_38 φ) (𝓝 α) (𝓝 α) ∧ HasDerivAt (equation_6_38 φ) 0 α ∧
      equation_6_38 φ α = α ∧
      ∀ x, φ (φ x) - 2 * φ x + x ≠ 0 → (equation_6_38 φ x = x ↔ φ x = x) := by
  have hd := hasDerivAt_aitkenIterationFunction_zero hφ.hasDerivAt hα h1
  refine ⟨?_, hd, aitkenIterationFunction_apply_self hα,
    fun x hx => aitkenIterationFunction_eq_self_iff hx⟩
  have := hd.continuousAt.tendsto
  rwa [aitkenIterationFunction_apply_self hα] at this

/-- **Property 6.7, `p = 1`.** Let `x^{(k+1)} = φ(x^{(k)})` be a fixed-point iteration of order
`1` for a simple zero `α` — read: `φ(α) = α`, `φ ∈ C²` near `α`, `φ'(α) ≠ 1`. Then Aitken's method
converges to `α` with order `2`, "even if the fixed-point method is not" convergent: nothing but
`φ'(α) ≠ 1` is assumed. `hasIterationOrder_aitkenIterationFunction_two`; the asymptotic constant
is `φ'(α) φ''(α) / (2 (φ'(α) - 1))` (`tendsto_aitkenIterationFunction_sub_div_sq`). -/
theorem property_6_7_one (hφ : ContDiffAt ℝ 2 φ α) (hα : φ α = α) (h1 : deriv φ α ≠ 1) :
    ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (fun k => (equation_6_38 φ)^[k] x₀) α 2 := by
  obtain ⟨ε, hε, h⟩ := hasIterationOrder_aitkenIterationFunction_two hφ hα h1
  exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder one_le_two (h x₀ hx₀)⟩

/-- **Property 6.7, `p ≥ 2`.** If the fixed-point iteration has order `p ≥ 2` at the simple zero
`α` in the sense of Property 6.4 (`φ ∈ C^p` near `α`, `φ^{(i)}(α) = 0` for `1 ≤ i < p`,
`φ^{(p)}(α) ≠ 0`), then Aitken's method has order `2p - 1`. Stated by the book without proof
(Isaacson–Keller); `hasIterationOrder_aitkenIterationFunction_of_iteratedDeriv_eq_zero`. -/
theorem property_6_7_higher {p : ℕ} (hp : 2 ≤ p) (hφ : ContDiffAt ℝ p φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i < p → iteratedDeriv i φ α = 0) (hp' : iteratedDeriv p φ α ≠ 0) :
    ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε,
      definition_6_1 (fun k => (equation_6_38 φ)^[k] x₀) α (2 * p - 1) := by
  obtain ⟨ε, hε, h⟩ :=
    hasIterationOrder_aitkenIterationFunction_of_iteratedDeriv_eq_zero hp hφ hα hzero hp'
  refine ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder ?_ (h x₀ hx₀)⟩
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

end Aitken

/-! ### Exercise 6.5: Steffensen's method, and the last clause of Property 6.7 -/

section Steffensen

variable {f : ℝ → ℝ} {α : ℝ}

/-- **Steffensen's method** (Exercise 6.5): `x^{(k+1)} = x^{(k)} - f(x^{(k)}) / ϕ(x^{(k)})` with
`ϕ(x) = (f(x + f(x)) - f(x)) / f(x)`, the iteration of the backbone's `steffensenStep`. -/
noncomputable def steffensen (f : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) : ℝ := (steffensenStep f)^[k] x₀

/-- **Exercise 6.5.** Steffensen's method is a second-order method at a simple root: for
`f α = 0`, `f ∈ C²` near `α` and `f'(α) ≠ 0`, from every `x^{(0)}` close enough to `α` the
iterates converge to `α` with order `2`. It is Aitken's Δ² method for the iteration function
`x + f(x)` (`steffensenStep_eq_aitkenIterationFunction`); `hasIterationOrder_steffensenStep_two`.
-/
theorem exercise_6_5 (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α) (hf' : deriv f α ≠ 0) :
    ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (steffensen f x₀) α 2 := by
  obtain ⟨ε, hε, h⟩ := hasIterationOrder_steffensenStep_two hα hf hf'
  exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder one_le_two (h x₀ hx₀)⟩

/-- **Property 6.7, last clause, read correctly.** "If `α` has multiplicity `m ≥ 2` and the method
is first-order convergent, then Aitken's method converges linearly with factor `C = 1 - 1/m`": as
printed this is false (`equation_6_38_fixedPoints` makes Aitken's method superlinear for any `φ`
with `φ'(α) ≠ 1`). The statement of Isaacson–Keller that the book paraphrases concerns the
iteration function `φ = id + f`, whose derivative at a multiple root is `1`, i.e. Steffensen's
method: at a root of multiplicity `m ≥ 2` of `f ∈ C^{m+1}`,
`(steffensenStep f x - α) / (x - α) → 1 - 1/m` as `x → α`, `x ≠ α`, and along every Steffensen
orbit converging to `α` without reaching it the error ratios tend to `1 - 1/m`.
`tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity`. -/
theorem property_6_7_multiple {m : ℕ} (hm : 2 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (steffensenStep f x - α) / (x - α)) (𝓝[≠] α) (𝓝 (1 - 1 / m)) ∧
      ∀ x₀, (∀ k, steffensen f x₀ k ≠ α) → Tendsto (steffensen f x₀) atTop (𝓝 α) →
        Tendsto (fun k => (steffensen f x₀ (k + 1) - α) / (steffensen f x₀ k - α)) atTop
          (𝓝 (1 - 1 / m)) := by
  have h := tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity hm hf hα
  refine ⟨h, fun x₀ hne hlim => ?_⟩
  have := h.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
  refine this.congr fun k => ?_
  simp [Function.comp, steffensen, Function.iterate_succ_apply']

end Steffensen

/-! ### §6.6.2 Techniques for multiple roots -/

section MultipleRoots

variable {f : ℝ → ℝ} {α : ℝ}

/-- **(6.40), the multiplicity estimate** `m^{(k)} = 1 / (1 - λ^{(k)})`, from the increment ratio
(6.33). -/
noncomputable def equation_6_40 (x : ℕ → ℝ) (k : ℕ) : ℝ := 1 / (1 - equation_6_33 x k)

/-- The estimate is the backbone's `Newton.multiplicityEstimate`, shifted by two. -/
theorem equation_6_40_eq (x : ℕ → ℝ) (k : ℕ) :
    equation_6_40 x (k + 2) = Newton.multiplicityEstimate x k := by
  rw [equation_6_40, Newton.multiplicityEstimate, equation_6_33_eq]

/-- **(6.40), the second form**:
`m^{(k)} = (x^{(k-1)} - x^{(k-2)}) / (2 x^{(k-1)} - x^{(k)} - x^{(k-2)})` for `k ≥ 2` when the
increment `x^{(k-1)} - x^{(k-2)}` is nonzero. `Newton.multiplicityEstimate_eq`. -/
theorem equation_6_40_eq_div (x : ℕ → ℝ) {k : ℕ} (hk : 2 ≤ k) (h : x (k - 1) - x (k - 2) ≠ 0) :
    equation_6_40 x k = (x (k - 1) - x (k - 2)) / (2 * x (k - 1) - x k - x (k - 2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [equation_6_40_eq, Newton.multiplicityEstimate_eq x j (by simpa using h)]
  simp

/-- **"`m^{(k)}` tends to `m` as `k → ∞`"** (§6.6.2): along a Newton orbit
`x^{(k+1)} = x^{(k)} - f(x^{(k)}) / f'(x^{(k)})` converging to a root `α` of multiplicity `m ≥ 1`
(`f ∈ C^{m+1}` near `α`) without reaching it, the estimate (6.40) tends to `m` — by (6.34), since
`φ'_Newt(α) = 1 - 1/m` by (6.22). `Newton.tendsto_multiplicityEstimate`. -/
theorem equation_6_40_tendsto {m : ℕ} (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) {x : ℕ → ℝ}
    (hx : ∀ k, x (k + 1) = Newton.scalarStep f (deriv f) (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) : Tendsto (equation_6_40 x) atTop (𝓝 m) := by
  rw [← tendsto_add_atTop_iff_nat 2]
  exact (Newton.tendsto_multiplicityEstimate hm hf hα hx hne hlim).congr
    fun k => (equation_6_40_eq x k).symm

/-- **(6.39), the adaptive Newton method**: `x^{(k+1)} = x^{(k)} - m^{(k)} f(x^{(k)}) / f'(x^{(k)})`
for `k ≥ 2`, with `m^{(k)}` the estimate (6.40) computed from the last three iterates
`(x^{(k-2)}, x^{(k-1)}, x^{(k)})` — the iteration of the backbone's `Newton.adaptiveStep` on
triples, started from the three iterates `x₀, x₁, x₂` (which Program 56 produces by two plain
Newton steps). A definition only; the book proves nothing about it. -/
noncomputable def equation_6_39 (f f' : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) (k : ℕ) : ℝ :=
  ((Newton.adaptiveStep f f')^[k] (x₀, x₁, x₂)).2.2

end MultipleRoots

end QuarteroniSaccoSaleri.Chapter06
