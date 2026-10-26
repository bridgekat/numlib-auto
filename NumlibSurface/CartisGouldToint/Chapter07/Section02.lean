import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import NumlibSurface.CartisGouldToint.Chapter07.Section01

/-!
# Cartis–Gould–Toint §7.2: Finding first-order approximate minimizers

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §7.2.2.1: the assumptions on the
problem (7.1.1) under which the two-phase algorithm TPp-GC is analysed.

## Main definitions

* `AssumptionCD1pLC c C p` — c.D1pL.C: the constraint functions are `p` times continuously
  differentiable on an open set containing `𝒞`, with Lipschitz continuous and bounded derivative
  tensors of orders `1, …, p` on `𝒞`;
* `nearFeasible C c β` — the region of near feasibility `ℱ_β = {x ∈ 𝒞 | ‖c(x)‖ ≤ β}` (7.2.7);
* `AssumptionBFb f c C β flow fup` — f.B.Fb: `flow ≤ f(x) ≤ fup` on `ℱ_β`;
* `AssumptionFD1pLC f C p` — f.D1pL.C: the analogue of c.D1pL.C for the objective.

## Deviations from the book

* f.B.Fb is stated "if `ℱ_β ≠ ∅`"; for the universally quantified form used here that proviso is
  vacuous. The constants `flow`, `fup` are explicit arguments.
* In f.D1pL.C the book writes `∇^j_x f_i`; the objective is scalar and `∇^j_x f` is meant.
* The derivative tensors in c.D1pL.C and f.D1pL.C are the Fréchet derivatives
  `iteratedFDeriv ℝ j`, with Mathlib's operator norm; the Lipschitz and boundedness constants are
  existentially quantified, as in the book.
-/

open Set

namespace CartisGouldToint.Chapter07

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-- Smoothness of a scalar function `g` in the sense of c.D1pL.C / f.D1pL.C of
[cartis2022evaluation], §7.2.2.1: `g` is `p` times continuously differentiable on an open set
`𝒟 ⊇ 𝒞`, and for each `j ∈ [1 : p]` its derivative tensor `∇^j g` is Lipschitz continuous and
bounded on `𝒞`. -/
def IsD1pLOn (g : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  (∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p g D) ∧
    ∀ j ∈ Finset.Icc 1 p, (∃ L, IteratedFDerivLipschitzOn g j L C) ∧
      ∃ B, ∀ x ∈ C, ‖iteratedFDeriv ℝ j g x‖ ≤ B

/-- **Assumption c.D1pL.C** of [cartis2022evaluation], §7.2.2.1: the constraint functions
`cᵢ`, `i ∈ [1 : m]`, are `p` times continuously differentiable in an open set containing `𝒞`,
and their derivative tensors `∇^j cᵢ`, `j ∈ [1 : p]`, are Lipschitz continuous and bounded
in `𝒞`. -/
def AssumptionCD1pLC (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  ∀ i, IsD1pLOn (fun x => c x i) C p

/-- **Assumption f.D1pL.C** of [cartis2022evaluation], §7.2.2.1: the objective `f` is `p` times
continuously differentiable in an open set containing `𝒞`, and its derivative tensors `∇^j f`,
`j ∈ [1 : p]`, are Lipschitz continuous and bounded in `𝒞`. -/
def AssumptionFD1pLC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  IsD1pLOn f C p

/-- The region of near feasibility `ℱ_β = {x ∈ 𝒞 | ‖c(x)‖ ≤ β}` of [cartis2022evaluation],
(7.2.7). -/
def nearFeasible (C : Set ℝⁿ) (c : ℝⁿ → ℝᵐ) (β : ℝ) : Set ℝⁿ := {x ∈ C | ‖c x‖ ≤ β}

/-- **Assumption f.B.Fb** of [cartis2022evaluation], §7.2.2.1: `f` is bounded below by `flow`
and above by `fup` on the region of near feasibility `ℱ_β`. -/
def AssumptionBFb (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (β flow fup : ℝ) : Prop :=
  ∀ x ∈ nearFeasible C c β, flow ≤ f x ∧ f x ≤ fup

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {x : ℝⁿ} {p : ℕ} {β β' flow fup : ℝ}

theorem isD1pLOn_iff {g : ℝⁿ → ℝ} :
    IsD1pLOn g C p ↔ (∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p g D) ∧
      ∀ j ∈ Finset.Icc 1 p, (∃ L, IteratedFDerivLipschitzOn g j L C) ∧
        ∃ B, ∀ x ∈ C, ‖iteratedFDeriv ℝ j g x‖ ≤ B :=
  Iff.rfl

theorem assumptionCD1pLC_iff : AssumptionCD1pLC c C p ↔ ∀ i, IsD1pLOn (fun x => c x i) C p :=
  Iff.rfl

theorem assumptionFD1pLC_iff : AssumptionFD1pLC f C p ↔ IsD1pLOn f C p := Iff.rfl

theorem mem_nearFeasible : x ∈ nearFeasible C c β ↔ x ∈ C ∧ ‖c x‖ ≤ β := Iff.rfl

theorem nearFeasible_subset : nearFeasible C c β ⊆ C := fun _ hx => hx.1

theorem nearFeasible_mono (h : β ≤ β') : nearFeasible C c β ⊆ nearFeasible C c β' :=
  fun _ hx => ⟨hx.1, hx.2.trans h⟩

/-- The feasible set lies in every region of near feasibility with `β ≥ 0`. -/
theorem feasibleSet_subset_nearFeasible (hβ : 0 ≤ β) : feasibleSet C c ⊆ nearFeasible C c β :=
  fun _ hx => ⟨hx.1, by simpa [hx.2] using hβ⟩

theorem assumptionBFb_iff :
    AssumptionBFb f c C β flow fup ↔ ∀ x ∈ C, ‖c x‖ ≤ β → flow ≤ f x ∧ f x ≤ fup :=
  ⟨fun h x hx hc => h x ⟨hx, hc⟩, fun h x hx => h x hx.1 hx.2⟩

/-- f.B.Fb with parameter `β` holds for every smaller parameter. -/
theorem AssumptionBFb.mono (h : AssumptionBFb f c C β flow fup) (hβ : β' ≤ β) :
    AssumptionBFb f c C β' flow fup :=
  fun x hx => h x (nearFeasible_mono hβ hx)

end CartisGouldToint.Chapter07
