import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Optimality.ConstrainedMeasure

/-!
# Cartis–Gould–Toint §6.1: Problems with convex constraints

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §6.1: the standing assumption
C.CNe on the constraint set `𝒞 ⊆ ℝⁿ` (`ℝⁿ = EuclideanSpace ℝ (Fin n)`) of the problem
`minimize_{x ∈ 𝒞} f(x)` (6.1.1), and the approximate first- to third-order criticality measures
of §6.1.1.

All measures are instances of the backbone `Optimization.formCriticality A T`, the supremum of
`-A[d]^j` over the displacements `d ∈ T` with `‖d‖ ≤ 1` (the book's `-min_{d ∈ T ∩ 𝓑} A[d]^j`,
with `𝓑` the Euclidean unit ball (6.1.3)), where `A = ∇^j f(x)` is
`iteratedFDeriv ℝ j f x`. The feasible steps `𝒞(x)` (6.1.2) are `Optimization.feasibleSteps C x`
and the restricted sets (6.1.8), (6.1.10) are `Optimization.restrictedSteps`.

## Main definitions

* `AssumptionCNe C` — C.CNe: `𝒞` is closed, convex and nonempty.
* `omega1 f C x` — `ω_{f,𝒞,1}(x)` (6.1.5).
* `restrictedSteps₁ f C τ₁ α x` — `𝒞¹(x, α)` (6.1.8).
* `omega2 f C τ₁ x α` — `ω_{f,𝒞,2}(x, α)` (6.1.7).
* `restrictedSteps₂ f C τ₁ τ₂ α₁ α₂ x` — `𝒞²(x, α₁, α₂)` (6.1.10).
* `omega3 f C τ₁ τ₂ x α₁ α₂` — `ω_{f,𝒞,3}(x, α₁, α₂)` (6.1.9).
* `IsApproxMinimizerCC f C τ₁ τ₂ q ε₁ ε₂ ε₃ x` — `x` is an approximate `q`-th order minimizer
  of `f` within `𝒞`, (6.1.4), (6.1.6) and the third-order condition, `q ∈ {1, 2, 3}`.

## Main results

* `omega1_nonneg`, `omega2_nonneg`, `omega3_nonneg` — the measures are nonnegative at feasible
  points (the "`≥ 0`" of (6.1.5), (6.1.7), (6.1.9)).
* `exists_omega1_eq` — the minimum in (6.1.5) is attained.
* `omega1_eq_zero_iff` — `ω_{f,𝒞,1}(x) = 0` iff `x` satisfies the first-order condition (1.1.6)
  of Theorem 1.1.2.
* `omega1_univ`, `isApproxMinimizerCC_one_univ_iff` — without constraints the first-order measure
  is `‖∇f(x)‖` and the first-order test is `‖∇f(x)‖ ≤ ε₁`.
* `not_assumptionCNe_imp_exists_minimizer` — C.CNe alone does not ensure that (6.1.1) has a
  solution.

## Deviations from the book

* (6.1.5) and (6.1.9) are printed as `min … ≥ 0` without the leading minus sign; the minus sign
  is meant (compare (6.1.7), (6.2.3)–(6.2.5) and the claimed nonnegativity) and is used here.
* The book claims that C.CNe "ensures that (6.1.1) has a solution". This is false without further
  assumptions on `f` (e.g. `𝒞 = ℝ`, `f(x) = x`): `not_assumptionCNe_imp_exists_minimizer`.
* The book requires approximate minimizers to lie "within `𝒞`"; this is the explicit condition
  `x ∈ C` of `IsApproxMinimizerCC` (for `x ∉ C` the measures carry no information).
* The remarks on the (dis)continuity of `ω_{f,𝒞,2}(x, 0)`, on computational cost and on norms other
  than the Euclidean one are not formalized.
-/

open Set Metric
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter06

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Assumption C.CNe** of [cartis2022evaluation] (§6.1): the constraint set `𝒞 ⊆ ℝⁿ` is closed,
convex and nonempty. -/
structure AssumptionCNe (C : Set ℝⁿ) : Prop where
  /-- `𝒞` is closed. -/
  isClosed : IsClosed C
  /-- `𝒞` is convex. -/
  convex : Convex ℝ C
  /-- `𝒞` is nonempty. -/
  nonempty : C.Nonempty

theorem assumptionCNe_iff {C : Set ℝⁿ} :
    AssumptionCNe C ↔ IsClosed C ∧ Convex ℝ C ∧ C.Nonempty :=
  ⟨fun h => ⟨h.isClosed, h.convex, h.nonempty⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- C.CNe alone does not ensure that the problem (6.1.1) has a solution, contrary to the claim
at the start of §6.1 of [cartis2022evaluation]: on `𝒞 = ℝ` (which satisfies C.CNe) the smooth
function `f(x) = x` has no minimizer. -/
theorem not_assumptionCNe_imp_exists_minimizer :
    ¬ ∀ (C : Set (EuclideanSpace ℝ (Fin 1))) (f : EuclideanSpace ℝ (Fin 1) → ℝ),
      AssumptionCNe C → ContDiff ℝ ⊤ f → ∃ x ∈ C, IsMinOn f C x := by
  intro h
  obtain ⟨x, -, hx⟩ := h univ (fun x => x 0)
    ⟨isClosed_univ, convex_univ, univ_nonempty⟩ (by fun_prop)
  have := hx (mem_univ (x - EuclideanSpace.single 0 1))
  simp at this
  linarith

/-- The first-order criticality measure (6.1.5) of [cartis2022evaluation],
`ω_{f,𝒞,1}(x) = -min_{d ∈ 𝒞(x) ∩ 𝓑} ⟨d, ∇¹f(x)⟩` (with the minus sign that the book omits). -/
noncomputable def omega1 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (x : ℝⁿ) : ℝ :=
  Optimization.formCriticality (iteratedFDeriv ℝ 1 f x) (Optimization.feasibleSteps C x)

/-- The set of first-order `α`-restricted feasible steps (6.1.8) of [cartis2022evaluation],
`𝒞¹(x, α) = {d ∈ 𝒞(x) | |⟨d, ∇¹f(x)⟩| ≤ τ₁ α}`. -/
def restrictedSteps₁ (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ α : ℝ) (x : ℝⁿ) : Set ℝⁿ :=
  Optimization.restrictedSteps (iteratedFDeriv ℝ 1 f x) (τ₁ * α) (Optimization.feasibleSteps C x)

/-- The second-order criticality measure (6.1.7) of [cartis2022evaluation],
`ω_{f,𝒞,2}(x, α) = -min_{d ∈ 𝒞¹(x, α) ∩ 𝓑} ⟨d, ∇²f(x) d⟩`. -/
noncomputable def omega2 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ : ℝ) (x : ℝⁿ) (α : ℝ) : ℝ :=
  Optimization.formCriticality (iteratedFDeriv ℝ 2 f x) (restrictedSteps₁ f C τ₁ α x)

/-- The set of second-order `(α₁, α₂)`-restricted feasible steps (6.1.10) of
[cartis2022evaluation], `𝒞²(x, α₁, α₂) = {d ∈ 𝒞¹(x, α₁) | |⟨d, ∇²f(x) d⟩| ≤ τ₂ α₂}`. -/
def restrictedSteps₂ (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ τ₂ α₁ α₂ : ℝ) (x : ℝⁿ) :
    Set ℝⁿ :=
  Optimization.restrictedSteps (iteratedFDeriv ℝ 2 f x) (τ₂ * α₂) (restrictedSteps₁ f C τ₁ α₁ x)

/-- The third-order criticality measure (6.1.9) of [cartis2022evaluation],
`ω_{f,𝒞,3}(x, α₁, α₂) = -min_{d ∈ 𝒞²(x, α₁, α₂) ∩ 𝓑} ∇³f(x)[d]³` (with the minus sign that the
book omits). -/
noncomputable def omega3 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ τ₂ : ℝ) (x : ℝⁿ) (α₁ α₂ : ℝ) :
    ℝ :=
  Optimization.formCriticality (iteratedFDeriv ℝ 3 f x) (restrictedSteps₂ f C τ₁ τ₂ α₁ α₂ x)

/-- Approximate minimizers within `𝒞` ([cartis2022evaluation], §6.1.1 and Step 1 of
Algorithm 6.2.1), for `q ∈ {1, 2, 3}`: `x ∈ 𝒞` is an `ε₁`-approximate first-order minimizer if
`ω_{f,𝒞,1}(x) ≤ ε₁` (6.1.4); an `(ε₁, ε₂)`-approximate second-order minimizer if moreover
`ω_{f,𝒞,2}(x, ε₁) ≤ ε₂` (6.1.6); and an `(ε₁, ε₂, ε₃)`-approximate third-order minimizer if
moreover `ω_{f,𝒞,3}(x, ε₁, ε₂) ≤ ε₃`. The book's `ε₂ = ε₃ = ∞` is `q = 1` and `ε₃ = ∞` is
`q = 2`. Other values of `q` are not used: `q = 0` gives the first-order notion and `q > 3` the
third-order one. -/
def IsApproxMinimizerCC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (τ₁ τ₂ : ℝ) (q : ℕ) (ε₁ ε₂ ε₃ : ℝ)
    (x : ℝⁿ) : Prop :=
  x ∈ C ∧ omega1 f C x ≤ ε₁ ∧ (2 ≤ q → omega2 f C τ₁ x ε₁ ≤ ε₂) ∧
    (3 ≤ q → omega3 f C τ₁ τ₂ x ε₁ ε₂ ≤ ε₃)

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {x d : ℝⁿ} {τ₁ τ₂ α α₁ α₂ : ℝ}

theorem mem_restrictedSteps₁ :
    d ∈ restrictedSteps₁ f C τ₁ α x ↔
      x + d ∈ C ∧ |iteratedFDeriv ℝ 1 f x (fun _ => d)| ≤ τ₁ * α :=
  Iff.rfl

theorem mem_restrictedSteps₂ :
    d ∈ restrictedSteps₂ f C τ₁ τ₂ α₁ α₂ x ↔
      d ∈ restrictedSteps₁ f C τ₁ α₁ x ∧ |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ τ₂ * α₂ :=
  Iff.rfl

theorem isApproxMinimizerCC_iff {q : ℕ} {ε₁ ε₂ ε₃ : ℝ} :
    IsApproxMinimizerCC f C τ₁ τ₂ q ε₁ ε₂ ε₃ x ↔
      x ∈ C ∧ omega1 f C x ≤ ε₁ ∧ (2 ≤ q → omega2 f C τ₁ x ε₁ ≤ ε₂) ∧
        (3 ≤ q → omega3 f C τ₁ τ₂ x ε₁ ε₂ ≤ ε₃) :=
  Iff.rfl

theorem zero_mem_restrictedSteps₁ (hx : x ∈ C) (hα : 0 ≤ τ₁ * α) :
    0 ∈ restrictedSteps₁ f C τ₁ α x :=
  (Optimization.zero_mem_restrictedSteps le_rfl hα).2 (Optimization.zero_mem_feasibleSteps.2 hx)

theorem zero_mem_restrictedSteps₂ (hx : x ∈ C) (hα₁ : 0 ≤ τ₁ * α₁) (hα₂ : 0 ≤ τ₂ * α₂) :
    0 ∈ restrictedSteps₂ f C τ₁ τ₂ α₁ α₂ x :=
  (Optimization.zero_mem_restrictedSteps one_le_two hα₂).2 (zero_mem_restrictedSteps₁ hx hα₁)

/-- The first-order measure is nonnegative at feasible points ((6.1.5)). -/
theorem omega1_nonneg (hx : x ∈ C) : 0 ≤ omega1 f C x :=
  Optimization.formCriticality_nonneg _ le_rfl (Optimization.zero_mem_feasibleSteps.2 hx)

/-- The second-order measure is nonnegative at feasible points ((6.1.7)). -/
theorem omega2_nonneg (hx : x ∈ C) (hα : 0 ≤ τ₁ * α) : 0 ≤ omega2 f C τ₁ x α :=
  Optimization.formCriticality_nonneg _ one_le_two (zero_mem_restrictedSteps₁ hx hα)

/-- The third-order measure is nonnegative at feasible points ((6.1.9)). -/
theorem omega3_nonneg (hx : x ∈ C) (hα₁ : 0 ≤ τ₁ * α₁) (hα₂ : 0 ≤ τ₂ * α₂) :
    0 ≤ omega3 f C τ₁ τ₂ x α₁ α₂ :=
  Optimization.formCriticality_nonneg _ (by norm_num) (zero_mem_restrictedSteps₂ hx hα₁ hα₂)

/-- Under C.CNe the minimum in (6.1.5) is attained at every feasible point. -/
theorem exists_omega1_eq (hC : AssumptionCNe C) (hx : x ∈ C) :
    ∃ d ∈ Optimization.feasibleSteps C x ∩ closedBall 0 1,
      -iteratedFDeriv ℝ 1 f x (fun _ => d) = omega1 f C x := by
  obtain ⟨d, hd, h⟩ := Optimization.exists_formCriticality_eq (iteratedFDeriv ℝ 1 f x)
    (Optimization.isClosed_feasibleSteps hC.isClosed x)
    ⟨0, mem_closedBall_self zero_le_one, Optimization.zero_mem_feasibleSteps.2 hx⟩
  exact ⟨d, ⟨hd.2, hd.1⟩, h⟩

/-- On a convex set, `ω_{f,𝒞,1}(x) = 0` exactly when `x` satisfies the first-order condition
`⟨∇f(x), y - x⟩ ≥ 0` for all `y ∈ 𝒞` ((1.1.6) of Theorem 1.1.2 of [cartis2022evaluation]). -/
theorem omega1_eq_zero_iff (hC : Convex ℝ C) (hx : x ∈ C) :
    omega1 f C x = 0 ↔ ∀ y ∈ C, 0 ≤ ⟪gradient f x, y - x⟫ := by
  simp only [omega1, Optimization.formCriticality_fderiv_eq_zero_iff hC hx, gradient,
    InnerProductSpace.toDual_symm_apply]

/-- Without constraints the first-order measure is `‖∇f(x)‖` (remark after (6.1.10) of
[cartis2022evaluation]). -/
theorem omega1_univ (f : ℝⁿ → ℝ) (x : ℝⁿ) : omega1 f univ x = ‖gradient f x‖ := by
  have h : Optimization.feasibleSteps (univ : Set ℝⁿ) x = univ := by
    ext; simp [Optimization.mem_feasibleSteps]
  rw [omega1, h, Optimization.formCriticality_iteratedFDeriv_one_univ,
    Optimization.norm_gradient_eq]

/-- Without constraints the first-order condition (6.1.4) is the unconstrained test
`‖∇f(x)‖ ≤ ε₁` (2.1.2). -/
theorem isApproxMinimizerCC_one_univ_iff {ε₁ ε₂ ε₃ : ℝ} :
    IsApproxMinimizerCC f univ τ₁ τ₂ 1 ε₁ ε₂ ε₃ x ↔ ‖gradient f x‖ ≤ ε₁ := by
  simp [IsApproxMinimizerCC, omega1_univ]

end CartisGouldToint.Chapter06
