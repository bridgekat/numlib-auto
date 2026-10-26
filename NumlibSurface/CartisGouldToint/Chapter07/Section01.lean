import Mathlib.Analysis.InnerProductSpace.Adjoint
import Numlib.Optimization.Constrained
import Numlib.Optimization.Constrained.TargetResidual
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import NumlibSurface.CartisGouldToint.Chapter06.Section01

/-!
# Cartis–Gould–Toint §7.1: The general constrained problem

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §7.1: the problem

`minimize_{x ∈ 𝒞} f(x)` subject to `c(x) = 0` (7.1.1),

with `f : ℝⁿ → ℝ`, `c : ℝⁿ → ℝᵐ` (`ℝⁿ = EuclideanSpace ℝ (Fin n)`), its Lagrangian
`ℒ(x, y) = f(x) - ⟨y, c(x)⟩` (1.1.1), the local sufficiency of the Lagrangian (Theorem 7.1.1) and
the first-order measures and (approximate) first-order minimizers (7.1.2)–(7.1.4).

## Main definitions

* `lagrangianVec f c x y` — the Lagrangian `ℒ(x, y)` for vector-valued constraints;
* `feasibleSet S c` — the feasible set `ℱ(𝒮, c) = {x ∈ 𝒮 | c(x) = 0}`;
* `omegaL f c C x y` — the first-order measure `ω_{ℒ,𝒞,1}(x, y)` of the Lagrangian (7.1.2)–(7.1.3);
* `IsFirstOrderMinimizerGC f c C x` — first-order minimizer of (7.1.1) (7.1.3);
* `IsApproxFirstOrderGC f c C ε₀ ε₁ x y` — `x` is an `(ε₀, ε₁)`-approximate first-order minimizer of
  `f` within `ℱ(𝒞, c)` with multiplier `y` (7.1.4).

## Main results

* `theorem_7_1_1` — Theorem 7.1.1 (local sufficiency of the Lagrangian);
* `omegaL_univ` — without the convex constraints, `ω_{ℒ,ℝⁿ,1}(x, y) = ‖∇f(x) - (∇c(x))ᵀ y‖`, the
  setting of (7.1.5);
* `IsFirstOrderMinimizerGC.isApproxFirstOrderGC` — a first-order minimizer is an
  `(ε₀, ε₁)`-approximate one for all `ε₀, ε₁ ≥ 0`.

## Deviations from the book

* The convex set `𝒞` of (7.1.1) is closed, bounded, nonempty and convex in the book; these
  properties are not used by the definitions or results of this section and are not imposed.
* Theorem 7.1.1 assumes that `𝒮` is a closed subset of `𝒞`; neither closedness nor `𝒮 ⊆ 𝒞` is
  needed, and `𝒞` does not occur in the statement.
* In (7.1.3)–(7.1.4) the set `𝒞(x)` and the gradient are evaluated at `x_*` (resp. `x_ε`), not at a
  free `x` as printed. The multiplier of (7.1.4) is an explicit argument of
  `IsApproxFirstOrderGC`, and `‖(y, 1)‖ = √(‖y‖² + 1)`.
* (7.1.3) requires `c(x_*) = 0` "for some `y_*`"; the feasibility `x_* ∈ 𝒞` is made explicit.
* The heuristic perturbation argument motivating the scaling `‖(y, 1)‖` after (7.1.5) (with
  footnote 52) is not formalized.
-/

open Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter07

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### The Lagrangian and the feasible set -/

/-- The Lagrangian `ℒ(x, y) = f(x) - ⟨y, c(x)⟩` of [cartis2022evaluation], (1.1.1), for a
vector-valued constraint function `c : ℝⁿ → ℝᵐ` and a multiplier `y ∈ ℝᵐ`. -/
noncomputable def lagrangianVec (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (x : ℝⁿ) (y : ℝᵐ) : ℝ :=
  f x - ⟪y, c x⟫

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C S : Set ℝⁿ} {x : ℝⁿ} {y : ℝᵐ}

theorem lagrangianVec_def : lagrangianVec f c x y = f x - ⟪y, c x⟫ := rfl

/-- The Lagrangian is the augmented Lagrangian `f + ⟪λ, c⟫ + ½ α ‖c‖²` with `α = 0`, `λ = -y`. -/
theorem lagrangianVec_eq_augmented :
    lagrangianVec f c x y = Constrained.augmented f c 0 (-y) x := by
  simp [lagrangianVec, Constrained.augmented, inner_neg_left, sub_eq_add_neg]

/-- The Lagrangian written componentwise: `ℒ(x, y) = f(x) - ∑ᵢ yᵢ cᵢ(x)`
(`Chapter01.lagrangian`). -/
theorem lagrangianVec_eq_lagrangian :
    lagrangianVec f c x y = Chapter01.lagrangian f (fun i z => c z i) x (fun i => y i) := by
  simp [lagrangianVec, Chapter01.lagrangian, PiLp.inner_apply, mul_comm]

/-- The feasible set `ℱ(𝒮, c) = {x ∈ 𝒮 | c(x) = 0}` of [cartis2022evaluation], §7.1. -/
def feasibleSet (S : Set ℝⁿ) (c : ℝⁿ → ℝᵐ) : Set ℝⁿ := {x ∈ S | c x = 0}

theorem mem_feasibleSet : x ∈ feasibleSet S c ↔ x ∈ S ∧ c x = 0 := Iff.rfl

theorem feasibleSet_subset : feasibleSet S c ⊆ S := fun _ hx => hx.1

/-- **Theorem 7.1.1** of [cartis2022evaluation] (local sufficiency of the Lagrangian). If
`x_* ∈ 𝒮` minimizes `ℒ(·, y_*)` over `𝒮` and `c(x_*) = 0`, then `x_*` is feasible and minimizes `f`
over `ℱ(𝒮, c)`. (The book's assumption that `𝒮` is a closed subset of `𝒞` is not needed.) -/
theorem theorem_7_1_1 (hx : x ∈ S) (hmin : IsMinOn (fun z => lagrangianVec f c z y) S x)
    (hc : c x = 0) : x ∈ feasibleSet S c ∧ IsMinOn f (feasibleSet S c) x :=
  ⟨⟨hx, hc⟩, Constrained.isMinOn_of_isMinOn_sub_inner hc hmin⟩

/-! ### First-order measures and minimizers -/

/-- The first-order criticality measure of the Lagrangian ([cartis2022evaluation], (7.1.2) with
`h = ℒ(·, y)`, (7.1.3)): `ω_{ℒ,𝒞,1}(x, y) = -min_{d ∈ 𝒞(x) ∩ 𝓑} ⟨d, ∇ₓℒ(x, y)⟩`. -/
noncomputable def omegaL (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (x : ℝⁿ) (y : ℝᵐ) : ℝ :=
  Chapter06.omega1 (fun z => lagrangianVec f c z y) C x

theorem omegaL_def :
    omegaL f c C x y = Chapter06.omega1 (fun z => lagrangianVec f c z y) C x := rfl

/-- The measure `ω_{ℒ,𝒞,1}(x, y)` is nonnegative at points of `𝒞`. -/
theorem omegaL_nonneg (hx : x ∈ C) : 0 ≤ omegaL f c C x y :=
  Chapter06.omega1_nonneg hx

/-- The gradient of the Lagrangian: `∇ₓℒ(x, y) = ∇f(x) - (∇c(x))ᵀ y`, the transpose being the
adjoint of the derivative of `c`. -/
theorem gradient_lagrangianVec (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) :
    gradient (fun z => lagrangianVec f c z y) x =
      gradient f x - ContinuousLinearMap.adjoint (fderiv ℝ c x) y := by
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (Constrained.hasFDerivAt_sub_inner y hf.hasFDerivAt hc.hasFDerivAt).congr_fderiv ?_
  ext v
  have hg := hf.hasGradientAt
  rw [hasGradientAt_iff_hasFDerivAt] at hg
  rw [hg.fderiv]
  simp [ContinuousLinearMap.adjoint_inner_left]

/-- Without convex constraints the measure (7.1.2) of the Lagrangian is the norm of its gradient,
`ω_{ℒ,ℝⁿ,1}(x, y) = ‖∇f(x) - (∇c(x))ᵀ y‖` ([cartis2022evaluation], (7.1.5)). -/
theorem omegaL_univ (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) :
    omegaL f c univ x y = ‖gradient f x - ContinuousLinearMap.adjoint (fderiv ℝ c x) y‖ := by
  rw [omegaL, Chapter06.omega1_univ, gradient_lagrangianVec hf hc]

/-- A first-order minimizer of (7.1.1) ([cartis2022evaluation], (7.1.3)): `x ∈ 𝒞`, `c(x) = 0`,
and `ω_{ℒ,𝒞,1}(x, y) = 0` for some multiplier `y`. -/
def IsFirstOrderMinimizerGC (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (x : ℝⁿ) : Prop :=
  x ∈ C ∧ c x = 0 ∧ ∃ y, omegaL f c C x y = 0

theorem isFirstOrderMinimizerGC_iff :
    IsFirstOrderMinimizerGC f c C x ↔ x ∈ C ∧ c x = 0 ∧ ∃ y, omegaL f c C x y = 0 :=
  Iff.rfl

/-- An `(ε₀, ε₁)`-approximate first-order minimizer of `f` within `ℱ(𝒞, c)`
([cartis2022evaluation], (7.1.4)), with multiplier `y`: `x ∈ 𝒞`, `‖c(x)‖ ≤ ε₀` and
`ω_{ℒ,𝒞,1}(x, y) ≤ ε₁ ‖(y, 1)‖`, where `‖(y, 1)‖ = √(‖y‖² + 1)`. -/
def IsApproxFirstOrderGC (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (ε₀ ε₁ : ℝ) (x : ℝⁿ)
    (y : ℝᵐ) : Prop :=
  x ∈ C ∧ ‖c x‖ ≤ ε₀ ∧ omegaL f c C x y ≤ ε₁ * √(‖y‖ ^ 2 + 1)

theorem isApproxFirstOrderGC_iff {ε₀ ε₁ : ℝ} :
    IsApproxFirstOrderGC f c C ε₀ ε₁ x y ↔
      x ∈ C ∧ ‖c x‖ ≤ ε₀ ∧ omegaL f c C x y ≤ ε₁ * √(‖y‖ ^ 2 + 1) :=
  Iff.rfl

/-- A first-order minimizer of (7.1.1) is an `(ε₀, ε₁)`-approximate first-order minimizer for all
`ε₀, ε₁ ≥ 0`, with the same multiplier. -/
theorem IsFirstOrderMinimizerGC.isApproxFirstOrderGC {ε₀ ε₁ : ℝ}
    (h : IsFirstOrderMinimizerGC f c C x) (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) :
    ∃ y, IsApproxFirstOrderGC f c C ε₀ ε₁ x y := by
  obtain ⟨hx, hc, y, hy⟩ := h
  exact ⟨y, hx, by simpa [hc] using hε₀, hy ▸ mul_nonneg hε₁ (Real.sqrt_nonneg _)⟩

end CartisGouldToint.Chapter07
