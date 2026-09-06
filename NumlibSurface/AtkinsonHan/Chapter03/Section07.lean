import Numlib.Approximation.BestApprox
import NumlibSurface.AtkinsonHan.Chapter02.Section04
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Atkinson–Han §3.7: uniform error bounds

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.7.

The section's two abstract ingredients are formalized here:

* the **Lebesgue lemma** `‖f − 𝓟f‖ ≤ (1 + ‖𝓟‖) ‖f − q‖` for a bounded projection `𝓟` and any `q`
  in its range, which is the common form of (3.7.11), (3.7.14) and (3.7.21); and
* the **non-convergence lemma**: if the norms of a sequence of bounded operators on a Banach
  space are unbounded, some vector is not the limit of its images. This is the Banach–Steinhaus
  argument that produces a continuous periodic function whose Fourier partial sums diverge.

## Main results

* `lebesgue_lemma`, `lebesgue_lemma_iInf`, `lebesgue_lemma_one_sub`.
* `exists_not_tendsto_of_not_bddAbove`.
* `IsPeriodicCont`, `PeriodicCont`, `HolderClass`, `HolderClassIcc` — the function spaces
  `C_p(2π)`, `C_p^{k,α}(2π)` and `C^{k,α}[−1, 1]` that Theorems 3.7.1–3.7.2 speak about,
  as definitions only.

## Not formalized here

Everything else in §3.7 is deferred to the trigonometric-approximation phase of the backbone,
because none of the objects it speaks about exist yet in Mathlib or in `Numlib`:

* (3.7.1)–(3.7.2) and **Theorems 3.7.1, 3.7.2** (Jackson's theorems)
  `‖g − qₙ‖_∞ ≤ c^{k+1} M_k / n^{k+α}`, and the polynomial version on `[−1, 1]`: these need the
  space `C_p(2π)` of continuous `2π`-periodic functions, its Hölder subclasses `C_p^{k,α}(2π)`,
  and the trigonometric polynomials `𝕋ₙ`. The two spaces are defined below; the theorems are
  not.
* (3.7.6)–(3.7.10): the Fourier projection `𝓕ₙ` on `C_p(2π)`, the Dirichlet kernel `Dₙ`, the
  identity `‖𝓕ₙ‖ = Lₙ` (which needs the integral-operator norm formula (2.2.8)), and Zygmund's
  asymptotics `Lₙ = (4/π²) log n + O(1)`.
* (3.7.12), (3.7.22): the resulting `c_k log n / n^{k+α}` bounds.
* (3.7.13)–(3.7.17): the least-squares projection `P_N` on a weighted `L²_w(−1, 1)`, its kernel
  `K(x, t)` and `‖P_N‖ = max_x ∫ |K(x, t)| dt`.
* **Theorem 3.7.3** (the Christoffel–Darboux identity), which is purely algebraic from the
  three-term recurrence and belongs with orthogonal polynomials.
* **Example 3.7.4** (the Chebyshev kernel) and §3.7.3 ((3.7.19) trigonometric Lagrange formula,
  (3.7.20) `‖𝓘ₙ‖ ≤ 1 + (2/π) log n`), which need interpolatory projections.
* (3.7.5) `‖f − 𝓕ₙ f‖₂ ≤ √(2π) ‖f − 𝓕ₙ f‖_∞`, which needs `L²` function spaces.
-/

open Filter Topology Bornology

namespace AtkinsonHan.Chapter03

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### The Lebesgue lemma -/

/-- **Lebesgue lemma**, pointwise form. For a bounded projection `𝓟` and any `q` in its range,
`‖u − 𝓟u‖ ≤ (1 + ‖𝓟‖) ‖u − q‖`. This is the shape of Atkinson–Han (3.7.11), (3.7.14) and
(3.7.21): the error of a projection method is within `1 + ‖𝓟‖` of the best approximation error
from the projection space. -/
theorem lebesgue_lemma (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) {q : V}
    (hq : q ∈ LinearMap.range (P : V →ₗ[𝕜] V)) : ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - q‖ :=
  norm_sub_apply_le_of_isIdempotentElem_of_mem P hP u hq

/-- **Lebesgue lemma**, in terms of the best approximation error from the projection space. -/
theorem lebesgue_lemma_iInf (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ (1 + ‖P‖) *
      ⨅ w : (LinearMap.range (P : V →ₗ[𝕜] V) : Set V), ‖u - (w : V)‖ := by
  have h := norm_sub_apply_le_of_isIdempotentElem P hP u
  rw [Metric.infDist_eq_iInf] at h
  simpa only [dist_eq_norm] using h

/-- The sharper constant `‖I − 𝓟‖` in place of `1 + ‖𝓟‖`. -/
theorem lebesgue_lemma_one_sub (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ ‖(1 : V →L[𝕜] V) - P‖ *
      ⨅ w : (LinearMap.range (P : V →ₗ[𝕜] V) : Set V), ‖u - (w : V)‖ := by
  have h := norm_sub_apply_le_of_isIdempotentElem' P hP u
  rw [Metric.infDist_eq_iInf] at h
  simpa only [dist_eq_norm] using h

/-! ### Non-convergence from unbounded operator norms -/

/-- If the operator norms `‖𝓟ₙ‖` are unbounded, then `𝓟ₙ f → f` fails for some `f`. Applied to
the Fourier projections `𝓕ₙ` on `C_p(2π)`, whose norms are the Lebesgue constants
`Lₙ = (4/π²) log n + O(1)` by (3.7.10), this is the paragraph after (3.7.10): there is a
continuous periodic function whose Fourier series does not converge uniformly to it. -/
theorem exists_not_tendsto_of_not_bddAbove [CompleteSpace V] (P : ℕ → V →L[𝕜] V)
    (h : ¬ BddAbove (Set.range fun n => ‖P n‖)) :
    ∃ f : V, ¬ Tendsto (fun n => P n f) atTop (𝓝 f) := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  obtain ⟨C, hC⟩ := banach_steinhaus fun v => Chapter02.exists_norm_le_of_tendsto (hcon v)
  exact h ⟨C, by rintro x ⟨n, rfl⟩; exact hC n⟩

/-! ### The function spaces of Theorems 3.7.1 and 3.7.2

Definitions only. The theorems themselves wait on trigonometric approximation. -/

section Spaces

open Real NNReal

/-- `C_p(2π)` as the book describes it: continuous real functions on `ℝ` of period `2π`. -/
def IsPeriodicCont (g : ℝ → ℝ) : Prop := Continuous g ∧ Function.Periodic g (2 * π)

/-- `C_p(2π)` as a space: continuous real functions on the circle `ℝ / 2πℤ`. Given
`Fact (0 < 2 * π)` the circle is compact, so this carries the sup norm `‖·‖_∞` of the book. -/
abbrev PeriodicCont : Type := C(AddCircle (2 * π), ℝ)

/-- A continuous `2π`-periodic function on `ℝ` is a continuous function on the circle. -/
noncomputable def PeriodicCont.ofIsPeriodicCont {g : ℝ → ℝ} (h : IsPeriodicCont g) :
    PeriodicCont :=
  ⟨h.2.lift, continuous_quot_lift _ h.1⟩

@[simp] theorem PeriodicCont.ofIsPeriodicCont_coe {g : ℝ → ℝ} (h : IsPeriodicCont g) (x : ℝ) :
    PeriodicCont.ofIsPeriodicCont h (x : AddCircle (2 * π)) = g x :=
  h.2.lift_coe x

/-- `C_p^{k,α}(2π)` with constant `M`: `k` times continuously differentiable with `M`-Hölder
`k`-th derivative of exponent `α`. -/
def HolderClass (k : ℕ) (α M : ℝ≥0) (g : ℝ → ℝ) : Prop :=
  IsPeriodicCont g ∧ ContDiff ℝ k g ∧ HolderWith M α (iteratedDeriv k g)

/-- The same class on `[−1, 1]`, used for the polynomial half of Theorem 3.7.2. -/
def HolderClassIcc (k : ℕ) (α M : ℝ≥0) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ k f (Set.Icc (-1) 1) ∧
    HolderOnWith M α (iteratedDerivWithin k f (Set.Icc (-1) 1)) (Set.Icc (-1) 1)

end Spaces

end AtkinsonHan.Chapter03
