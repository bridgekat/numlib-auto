import Numlib.Analysis.PDE.Elliptic.MaximumPrinciple
import Numlib.MeasureTheory.Function.ContinuousOnClosure
import NumlibSurface.Brezis.Chapter09.Section04

/-!
# Brezis §9.5: Variational formulation of some boundary value problems

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §9.5, on `ℝ^N = EuclideanSpace ℝ (Fin N)` with Lebesgue
measure: the homogeneous Dirichlet problem for `-Δu + u = f` (Example 1, Theorem 9.21), the
inhomogeneous Dirichlet condition (Example 2, Proposition 9.22), general second-order elliptic
equations (Example 3, Theorem 9.23, Remark 23), the homogeneous Neumann problem (Example 4,
Proposition 9.24) and unbounded domains (Example 5).

The backbone is `Numlib/Analysis/PDE/Elliptic/Dirichlet` (the forms `Elliptic.laplaceForm`,
`Elliptic.generalForm`, the load `Elliptic.load`, the weak problems as `IsGalerkinSolution`,
Theorem 9.21, Proposition 9.22, Example 3, Gårding's inequality and the Fredholm alternative,
Proposition 9.24, Steps A and D of Example 1) and, for Remark 23's maximum principle,
`Numlib/Analysis/PDE/Elliptic/MaximumPrinciple`.

## Conventions

* `H^1(Ω) = hSpace N Ω` and `H^1_0(Ω) = hZeroSpace N Ω` (§9.1, §9.4); the book's integrals are
  written with the weak partial derivatives `partialDeriv` and the functions `fn`, and each weak
  problem is restated with the book's display ((32), (34), (38), (40), (45)) and bridged to the
  backbone's `IsGalerkinSolution` by an `_iff` lemma.
* The book's `u ∈ C²(Ω̄)` (footnote 16 of §9.3) is `ContDiffOnClosure ℝ 2 u Ω` together with
  `ContinuousOn u (closure Ω)` — `u` is `C²` on `Ω`, its derivatives of order `≤ 2` extend
  continuously to `Ω̄`, and `u` is its own continuous extension, so that its boundary values are
  meaningful. Mathlib's `ContDiffOn ℝ 2 u (closure Ω)` is a stronger hypothesis
  (`isClassicalSolutionDirichlet_of_contDiffOn`, `example_9_1_stepA_of_contDiffOn`).
* The Laplacian is Mathlib's `Δ` (`InnerProductSpace.instLaplacian`); the data `f` of the weak
  problems are elements of `L²(Ω)`, and the classical equations hold pointwise on `Ω`.
* The coefficients `a_ij, a_i, a₀` of (39)–(40) are `L^∞(Ω)` classes, as in the book, with the
  ellipticity condition (36) almost everywhere (`Elliptic.IsUniformlyElliptic`); for the
  continuous coefficients of Example 3 the pointwise condition (36) is `ellipticityCondition`, and
  `isUniformlyElliptic_of_ellipticityCondition` bridges.
* Hypotheses the book leaves implicit: `N ≥ 1` in Remark 23's maximum-principle clause; the
  boundedness of `Ω` is carried as `Bornology.IsBounded` (Theorem 9.23 needs only `|Ω| < ∞`).

## Main results

* `IsClassicalSolutionDirichlet`, `IsWeakSolutionDirichlet`, `isWeakSolutionDirichlet_iff`,
  `example_9_1_stepA`, `example_9_1_stepA_of_contDiffOn`, `theorem_9_21`, `theorem_9_21_isMinOn`,
  `example_9_1_stepD`, `example_9_1_stepD_of_continuous`. Not yet restated: Example 4's Steps A
  and D (Green's formula and the surface measure on `Γ`).
* `admissibleSetInhomogeneous`, `example_9_2`, `IsClassicalSolutionInhomogeneous`,
  `IsWeakSolutionInhomogeneous`, `example_9_2_stepA`, `proposition_9_22`, `proposition_9_22_iff`,
  `proposition_9_22_isMinOn`.
* `ellipticityCondition`, `IsClassicalSolutionElliptic`, `IsWeakSolutionElliptic`,
  `example_9_3_stepA`, `example_9_3`, `example_9_3_isMinOn`, `IsWeakSolutionGeneralElliptic`,
  `theorem_9_23`,
  `remark_9_23`, `remark_9_23_zero_drift`.
* `IsClassicalSolutionNeumann`, `IsWeakSolutionNeumann`, `proposition_9_24`,
  `proposition_9_24_isMinOn`, `example_9_4_stepD_interior`, `example_9_5_a`, `example_9_5_b`,
  `example_9_5_c`.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

section Example1

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### Example 1: the homogeneous Dirichlet problem for the Laplacian -/

/-- **Definition (§9.5, Example 1): a classical solution of (31)**, `-Δu + u = f` in `Ω`, `u = 0`
on `Γ = ∂Ω`: a function `u ∈ C²(Ω̄)` — `C²` on `Ω` with the derivatives of order `≤ 2` extending
continuously to `Ω̄` (`ContDiffOnClosure`, footnote 16 of §9.3), and `u` itself continuous on `Ω̄`
— satisfying (31) in the usual sense: `-Δ u x + u x = f x` at every `x ∈ Ω`, with Mathlib's
Laplacian `Δ`, and `u x = 0` at every `x ∈ Γ`. -/
def IsClassicalSolutionDirichlet (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f u : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ContDiffOnClosure ℝ 2 u Ω ∧ ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
    (∀ x ∈ Ω, -Δ u x + u x = f x) ∧ EqOn u 0 (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))

/-- A function of class `C²` on `closure Ω` in Mathlib's sense that satisfies (31) is a classical
solution: `ContDiffOn ℝ 2 u (closure Ω)` gives both `ContDiffOnClosure ℝ 2 u Ω`
(`ContDiffOn.contDiffOnClosure`) and the continuity of `u` on `Ω̄`. -/
theorem isClassicalSolutionDirichlet_of_contDiffOn {f u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 2 u (closure (Ω : Set 𝔼))) (heq : ∀ x ∈ Ω, -Δ u x + u x = f x)
    (h0 : EqOn u 0 (frontier (Ω : Set 𝔼))) : IsClassicalSolutionDirichlet Ω f u :=
  ⟨hu.contDiffOnClosure Ω.isOpen, hu.continuousOn, heq, h0⟩

/-- **Definition (§9.5, Example 1): a weak solution of (31)**: a function `u ∈ H^1_0(Ω)`
satisfying `∫_Ω ∇u · ∇v + ∫_Ω u v = ∫_Ω f v` for all `v ∈ H^1_0(Ω)` (32), where
`∇u · ∇v = ∑ᵢ ∂u/∂xᵢ ∂v/∂xᵢ`, for `f ∈ L²(Ω)`. -/
def IsWeakSolutionDirichlet (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (u : hSpace N Ω) : Prop :=
  u ∈ hZeroSpace N Ω ∧ ∀ v ∈ hZeroSpace N Ω,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, partialDeriv u i x * partialDeriv v i x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- **The form of `-Δ + 1` is the left-hand side of (32)**: `∫_Ω ∇u · ∇v + ∫_Ω u v`, as two
integrals (the backbone's `Elliptic.laplaceForm_apply` writes one). -/
theorem laplaceForm_apply_two (u v : hSpace N Ω) :
    Elliptic.laplaceForm Ω u v
      = (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv v i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x := by
  rw [Elliptic.laplaceForm, add_apply, add_apply, Elliptic.dirichletForm_apply,
    Elliptic.pairing_apply, ContinuousLinearMap.id_apply, MeasureTheory.L2.inner_eq_integral_mul]
  rfl

/-- **The weak formulation (32) is the backbone's Galerkin problem** for the form
`Elliptic.laplaceForm Ω` and the load `Elliptic.load Ω f` on `H^1_0(Ω)`. -/
theorem isWeakSolutionDirichlet_iff (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsWeakSolutionDirichlet Ω f u ↔
      IsGalerkinSolution (Elliptic.laplaceForm Ω) (Elliptic.load Ω f) (hZeroSpace N Ω) u := by
  simp only [IsWeakSolutionDirichlet, IsGalerkinSolution, laplaceForm_apply_two,
    Elliptic.load_apply]

/-- **Example 1, Step A: every classical solution is a weak solution.** Let `Ω` be bounded, `u`
a classical solution of (31) (`IsClassicalSolutionDirichlet Ω f u`: `u ∈ C²(Ω̄)` in the sense of
footnote 16 of §9.3, continuous on `Ω̄`, with `-Δu + u = f` in `Ω` and `u = 0` on `Γ`), and
`f ∈ L²(Ω)`. Then `u` is the function of some `U ∈ H^1_0(Ω)`, and `U` is a weak solution of (31).
The backbone's `Elliptic.isGalerkinSolution_laplace_of_classical`: `u` and `∇u` are bounded, so
`u ∈ H^1(Ω) ∩ C(Ω̄)` with `u = 0` on `Γ`, hence `u ∈ H^1_0(Ω)` by Theorem 9.17 (i) ⇒ (ii)
(Remark 19: no regularity of `Ω`); for `v ∈ C_c^1(Ω)` the identity (32) is an integration by
parts, and by density it holds for all `v ∈ H^1_0(Ω)`. -/
theorem example_9_1_stepA (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f u : 𝔼 → ℝ}
    (hu : IsClassicalSolutionDirichlet Ω f u) (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace N Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionDirichlet Ω (hf.toLp f) U := by
  obtain ⟨U, -, hUu, hUw⟩ := Elliptic.isGalerkinSolution_laplace_of_classical Ω hb hu.1 hu.2.1
    hu.2.2.2 hf hu.2.2.1
  exact ⟨U, hUu, (isWeakSolutionDirichlet_iff _ _).2 hUw⟩

/-- **Example 1, Step A, for a solution of class `C²` on `closure Ω`**: the same for `u` with
`ContDiffOn ℝ 2 u (closure Ω)` (Mathlib's reading of `u ∈ C²(Ω̄)`,
`isClassicalSolutionDirichlet_of_contDiffOn`) satisfying (31). -/
theorem example_9_1_stepA_of_contDiffOn (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 2 u (closure (Ω : Set 𝔼))) {f : 𝔼 → ℝ}
    (heq : ∀ x ∈ Ω, -Δ u x + u x = f x) (h0 : EqOn u 0 (frontier (Ω : Set 𝔼)))
    (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace N Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionDirichlet Ω (hf.toLp f) U :=
  example_9_1_stepA hb (isClassicalSolutionDirichlet_of_contDiffOn hu heq h0) hf

/-- **Theorem 9.21 (Dirichlet, Riemann, Poincaré, Hilbert).** Given any `f ∈ L²(Ω)`, there exists
a unique weak solution `u ∈ H^1_0(Ω)` of (31). The backbone's
`Elliptic.existsUnique_isGalerkinSolution_laplace`: Lax–Milgram (Corollary 5.8) in the Hilbert
space `H = H^1_0(Ω)` with the bilinear form `a(u, v) = ∫_Ω (∇u · ∇v + u v)` — the scalar product
of `H^1(Ω)` — and the linear functional `φ : v ↦ ∫_Ω f v`. The book's boundedness of `Ω` is not
needed. -/
theorem theorem_9_21 (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace N Ω, IsWeakSolutionDirichlet Ω f u := by
  simp only [isWeakSolutionDirichlet_iff]
  exact Elliptic.existsUnique_isGalerkinSolution_laplace Ω f

/-- **Theorem 9.21, Dirichlet's principle.** The weak solution `u` of (31) is obtained by
`min_{v ∈ H^1_0(Ω)} {½ ∫_Ω (|∇v|² + |v|²) − ∫_Ω f v}`, and conversely a minimizer over `H^1_0(Ω)`
is the weak solution: for `u ∈ H^1_0(Ω)`, `u` minimizes the energy over `H^1_0(Ω)` if and only if
it is the weak solution of (31). The backbone's
`Elliptic.isMinOn_energy_iff_isGalerkinSolution_laplace` (the form is symmetric and coercive). -/
theorem theorem_9_21_isMinOn (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {u : hSpace N Ω}
    (hu : u ∈ hZeroSpace N Ω) :
    IsMinOn (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) (hZeroSpace N Ω) u
      ↔ IsWeakSolutionDirichlet Ω f u := by
  have e : (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
      = (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) := by
    funext v
    rw [Elliptic.energy_laplace_apply]
    simp only [sq]
    rfl
  rw [e, isWeakSolutionDirichlet_iff]
  exact Elliptic.isMinOn_energy_iff_isGalerkinSolution_laplace Ω hu

end Example1

section Example1StepD

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Example 1, Step D: recovery of a classical solution.** Assume that the weak solution
`U ∈ H^1_0(Ω)` of (31) belongs to `C²(Ω̄)` — it has a representative `u` with
`ContDiffOnClosure ℝ 2 u Ω` continuous on `Ω̄` — and that `Ω` is bounded and of class `C^1`.
Then `u = 0` on `Γ` (by Theorem 9.17) and `-Δu + u = f` a.e. on `Ω` (Corollary 4.24, the
backbone's `Elliptic.laplacian_ae_eq_of_isGalerkinSolution`); with a continuous datum the
equation holds everywhere (`example_9_1_stepD_of_continuous`). -/
theorem example_9_1_stepD (hΩ : IsClassC1 (Ω : Set 𝔼)) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    {U : hSpace (d + 1) Ω} (hU : IsWeakSolutionDirichlet Ω f U) {u : 𝔼 → ℝ}
    (hUu : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
    (hu : ContDiffOnClosure ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set 𝔼))) :
    EqOn u 0 (frontier (Ω : Set 𝔼)) ∧
      (fun x ↦ -Δ u x + u x) =ᵐ[volume.restrict (Ω : Set 𝔼)] f :=
  ⟨theorem_9_17_mpr hΩ (by simp) hU.1 hUu huc,
    Elliptic.laplacian_ae_eq_of_isGalerkinSolution Ω ((isWeakSolutionDirichlet_iff f U).1 hU)
      hu.contDiffOn hUu⟩

/-- **Example 1, Step D, with a continuous datum**: if moreover `f` agrees almost everywhere on
`Ω` with a function `g` continuous on `Ω`, then `-Δu + u = g` everywhere on `Ω`, and `u` is a
classical solution of (31) with datum `g`. The book's "in fact everywhere, since `u ∈ C²(Ω)`"
presumes such a continuous representative of `f ∈ L²(Ω)`. -/
theorem example_9_1_stepD_of_continuous (hΩ : IsClassC1 (Ω : Set 𝔼))
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {U : hSpace (d + 1) Ω}
    (hU : IsWeakSolutionDirichlet Ω f U) {u : 𝔼 → ℝ}
    (hUu : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
    (hu : ContDiffOnClosure ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set 𝔼)))
    {g : 𝔼 → ℝ} (hg : ContinuousOn g Ω) (hfg : (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] g) :
    IsClassicalSolutionDirichlet Ω g u :=
  ⟨hu, huc, Elliptic.laplacian_eq_of_isGalerkinSolution_of_continuousOn Ω
    ((isWeakSolutionDirichlet_iff f U).1 hU) hu.contDiffOn hUu hg hfg,
    theorem_9_17_mpr hΩ (by simp) hU.1 hUu huc⟩

end Example1StepD

/-! ### Example 2: the inhomogeneous Dirichlet condition -/

section Example2

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Definition (§9.5, Example 2): the set `K = {v ∈ H^1(Ω) : v − g̃ ∈ H^1_0(Ω)}`** for
`g̃ ∈ H^1(Ω)` (the book: `g̃ ∈ H^1(Ω) ∩ C(Ω̄)` with `g̃ = g` on `Γ`), the backbone's
`Elliptic.admissibleSet`. -/
noncomputable abbrev admissibleSetInhomogeneous (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (g : hSpace N Ω) : Set (hSpace N Ω) :=
  Elliptic.admissibleSet Ω g

/-- Membership of `K`, unfolded: `v ∈ K ↔ v − g̃ ∈ H^1_0(Ω)`. -/
theorem mem_admissibleSetInhomogeneous_iff {g v : hSpace N Ω} :
    v ∈ admissibleSetInhomogeneous Ω g ↔ v - g ∈ hZeroSpace N Ω :=
  Iff.rfl

/-- **Example 2, the set `K`.** `K` is a nonempty closed convex set in `H^1(Ω)`, and "it follows
from Theorem 9.17 that `K` is independent of the choice of `g̃` and depends only on `g`": two
extensions `g̃ = k₁, k₂ ∈ H^1(Ω) ∩ C(Ω̄)` with the same boundary values `g` on `Γ` define the same
`K`, since `k₁ − k₂ ∈ H^1(Ω) ∩ C(Ω̄)` vanishes on `Γ` and so lies in `H^1_0(Ω)` (Theorem 9.17
(i) ⇒ (ii), which needs no regularity of `Ω`). -/
theorem example_9_2 (g : hSpace N Ω) :
    (admissibleSetInhomogeneous Ω g).Nonempty ∧ IsClosed (admissibleSetInhomogeneous Ω g) ∧
    Convex ℝ (admissibleSetInhomogeneous Ω g) ∧
    ∀ (g₂ : hSpace N Ω) {k₁ k₂ : 𝔼 → ℝ},
      SobolevMultiIndex.fn g =ᵐ[volume.restrict (Ω : Set 𝔼)] k₁ →
      SobolevMultiIndex.fn g₂ =ᵐ[volume.restrict (Ω : Set 𝔼)] k₂ →
      ContinuousOn k₁ (closure (Ω : Set 𝔼)) → ContinuousOn k₂ (closure (Ω : Set 𝔼)) →
      EqOn k₁ k₂ (frontier (Ω : Set 𝔼)) →
      admissibleSetInhomogeneous Ω g = admissibleSetInhomogeneous Ω g₂ := by
  refine ⟨Elliptic.admissibleSet_nonempty Ω g, Elliptic.isClosed_admissibleSet Ω g,
    Elliptic.convex_admissibleSet Ω g, fun g₂ k₁ k₂ h₁ h₂ hc₁ hc₂ hΓ ↦ ?_⟩
  refine Elliptic.admissibleSet_eq_of_sub_mem Ω (theorem_9_17_mp (by simp) (g - g₂)
    ((SobolevMultiIndex.fn_sub g g₂).trans (h₁.sub h₂)) (hc₁.sub hc₂) fun x hx ↦ ?_)
  simp only [Pi.sub_apply, Pi.zero_apply, hΓ hx, sub_self]

/-- **Definition (§9.5, Example 2): a classical solution of (33)**, `-Δu + u = f` in `Ω`,
`u = g` on `Γ`: `u ∈ C²(Ω̄)` (as in `IsClassicalSolutionDirichlet`) satisfying (33). -/
def IsClassicalSolutionInhomogeneous (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f g u : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ContDiffOnClosure ℝ 2 u Ω ∧ ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
    (∀ x ∈ Ω, -Δ u x + u x = f x) ∧ EqOn u g (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))

/-- **Definition (§9.5, Example 2): a weak solution of (33)**: a function `u ∈ K` satisfying
`∫_Ω (∇u · ∇v + u v) = ∫_Ω f v` for all `v ∈ H^1_0(Ω)` (34). -/
def IsWeakSolutionInhomogeneous (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (g u : hSpace N Ω) :
    Prop :=
  u ∈ admissibleSetInhomogeneous Ω g ∧ ∀ v ∈ hZeroSpace N Ω,
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ((∑ i, partialDeriv u i x * partialDeriv v i x)
        + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- **The weak formulation (34) in the backbone's terms**: `u ∈ K` and
`laplaceForm Ω u v = load Ω f v` for all `v ∈ H^1_0(Ω)`. -/
theorem isWeakSolutionInhomogeneous_iff (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (g u : hSpace N Ω) :
    IsWeakSolutionInhomogeneous Ω f g u ↔ u ∈ Elliptic.admissibleSet Ω g ∧
      ∀ v ∈ hZeroSpace N Ω, Elliptic.laplaceForm Ω u v = Elliptic.load Ω f v := by
  simp only [IsWeakSolutionInhomogeneous, Elliptic.laplaceForm_apply, Elliptic.load_apply]
  rfl

/-- **Example 2, "as above, any classical solution is a weak solution".** Let `Ω` be bounded,
`g̃ ∈ H^1(Ω) ∩ C(Ω̄)` with `g̃ = g` on `Γ` — `G : H^1(Ω)` with a representative `k` continuous
on `closure Ω` and `k = g` on `Γ` — and `u` a classical solution of (33)
(`IsClassicalSolutionInhomogeneous Ω f g u`), with `f ∈ L²(Ω)`. Then `u` is the function of some
`U ∈ K`, and `U` is a weak solution of (33): `u − g̃ ∈ H^1(Ω) ∩ C(Ω̄)` vanishes on `Γ`, hence
lies in `H^1_0(Ω)` by Theorem 9.17 (i) ⇒ (ii) (`theorem_9_17_mp`, no regularity of `Ω`), and the
identity (34) is Example 1's Step A without its boundary condition (the backbone's
`Elliptic.exists_sobolev_forall_laplaceForm_eq_load_of_classical`). -/
theorem example_9_2_stepA (hb : Bornology.IsBounded (Ω : Set 𝔼)) {G : hSpace N Ω} {k g : 𝔼 → ℝ}
    (hG : SobolevMultiIndex.fn G =ᵐ[volume.restrict (Ω : Set 𝔼)] k)
    (hk : ContinuousOn k (closure (Ω : Set 𝔼))) (hkg : EqOn k g (frontier (Ω : Set 𝔼)))
    {f u : 𝔼 → ℝ} (hu : IsClassicalSolutionInhomogeneous Ω f g u)
    (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace N Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionInhomogeneous Ω (hf.toLp f) G U := by
  obtain ⟨U, hUu, hUw⟩ :=
    Elliptic.exists_sobolev_forall_laplaceForm_eq_load_of_classical Ω hb hu.1 hf hu.2.2.1
  refine ⟨U, hUu, (isWeakSolutionInhomogeneous_iff _ _ _).2 ⟨?_, hUw⟩⟩
  refine mem_admissibleSetInhomogeneous_iff.2 (theorem_9_17_mp (by simp) (U - G)
    ((SobolevMultiIndex.fn_sub U G).trans (hUu.sub hG)) (hu.2.1.sub hk) fun x hx ↦ ?_)
  simp only [Pi.sub_apply, Pi.zero_apply, hu.2.2.2 hx, hkg hx, sub_self]

/-- **Proposition 9.22.** Given any `f ∈ L²(Ω)`, there exists a unique weak solution `u ∈ K` of
(33). The backbone's `Elliptic.existsUnique_isWeakSolution_inhomogeneous`; the book's proof goes
through the variational inequality (35) (`proposition_9_22_iff`) and Stampacchia's theorem
(Theorem 5.6) on the nonempty closed convex set `K` (`example_9_2`). -/
theorem proposition_9_22 (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (g : hSpace N Ω) :
    ∃! u : hSpace N Ω, IsWeakSolutionInhomogeneous Ω f g u := by
  simp only [isWeakSolutionInhomogeneous_iff]
  exact Elliptic.existsUnique_isWeakSolution_inhomogeneous Ω g f

/-- **Proposition 9.22, the claim of the proof: (34) ⇔ (35).** `u ∈ K` is a weak solution of
(33) if and only if `∫_Ω ∇u · ∇(v − u) + ∫_Ω u (v − u) ≥ ∫_Ω f (v − u)` for all `v ∈ K`: if `u`
is a weak solution, (35) holds with equality; conversely, `v = u ± w` with `w ∈ H^1_0(Ω)` gives
(34). The backbone's `Elliptic.isWeakSolution_inhomogeneous_iff_forall_le`. -/
theorem proposition_9_22_iff (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {g u : hSpace N Ω}
    (hu : u ∈ admissibleSetInhomogeneous Ω g) :
    IsWeakSolutionInhomogeneous Ω f g u ↔ ∀ v ∈ admissibleSetInhomogeneous Ω g,
      ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
        ≤ (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv (v - u) i x)
          + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x := by
  rw [isWeakSolutionInhomogeneous_iff, and_iff_right hu,
    Elliptic.isWeakSolution_inhomogeneous_iff_forall_le Ω (Elliptic.laplaceForm Ω)
      (Elliptic.load Ω f) hu]
  simp only [laplaceForm_apply_two, Elliptic.load_apply]

/-- **Proposition 9.22, "furthermore"**: the weak solution `u ∈ K` of (33) is obtained by
`min_{v ∈ K} {½ ∫_Ω (|∇v|² + v²) − ∫_Ω f v}`, and conversely: for `u ∈ K`, `u` minimizes the
energy over `K` if and only if it is the weak solution. The backbone's
`Elliptic.isMinOn_energy_iff_isWeakSolution_inhomogeneous`. -/
theorem proposition_9_22_isMinOn (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {g u : hSpace N Ω}
    (hu : u ∈ admissibleSetInhomogeneous Ω g) :
    IsMinOn (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) (admissibleSetInhomogeneous Ω g) u
      ↔ IsWeakSolutionInhomogeneous Ω f g u := by
  have e : (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
      = (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) := by
    funext v
    rw [Elliptic.energy_laplace_apply]
    simp only [sq]
    rfl
  rw [e, isWeakSolutionInhomogeneous_iff, and_iff_right hu]
  exact Elliptic.isMinOn_energy_iff_isWeakSolution_inhomogeneous Ω hu

end Example2

/-! ### Example 3: general elliptic equations of second order -/

section Example3

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Definition (§9.5, Example 3): the ellipticity condition (36)** on coefficients
`a_ij : ℝ^N → ℝ`, `1 ≤ i, j ≤ N`: `∑ᵢⱼ a_ij(x) ξᵢ ξⱼ ≥ α |ξ|²` for all `x ∈ Ω` and all `ξ ∈ ℝ^N`,
with `α > 0`. Stated pointwise on `Ω` for functions; the backbone's almost-everywhere
`Elliptic.IsUniformlyElliptic` on `L^∞` classes follows
(`isUniformlyElliptic_of_ellipticityCondition`). -/
def ellipticityCondition (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin N), α * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j

/-- The pointwise ellipticity condition (36) on functions `a_ij` gives the backbone's
almost-everywhere condition on `L^∞(Ω)` classes `A i j` equal to `a_ij` a.e. on `Ω`
(`Elliptic.isUniformlyElliptic_of_forall_mem`). -/
theorem isUniformlyElliptic_of_ellipticityCondition {a : Fin N → Fin N → 𝔼 → ℝ} {α : ℝ}
    (h : ellipticityCondition Ω a α) {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))}
    (hA : ∀ i j, (A i j : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] a i j) :
    Elliptic.IsUniformlyElliptic Ω A α :=
  Elliptic.isUniformlyElliptic_of_forall_mem Ω A h.1 h.2 hA

/-- A function continuous on the closure of a bounded open set is (the function of) an element
of `L^∞(Ω)` (`ContinuousOn.memLp_top_restrict_of_isBounded`). -/
theorem memLp_top_of_continuousOn_closure (hb : Bornology.IsBounded (Ω : Set 𝔼)) {a : 𝔼 → ℝ}
    (ha : ContinuousOn a (closure (Ω : Set 𝔼))) : MemLp a ⊤ (volume.restrict (Ω : Set 𝔼)) :=
  ha.memLp_top_restrict_of_isBounded hb Ω.isOpen.measurableSet

/-- **Definition (§9.5, Example 3): a classical solution of (37)**,
`-∑ᵢⱼ ∂ⱼ(a_ij ∂ᵢu) + a₀ u = f` in `Ω`, `u = 0` on `Γ`, for `a_ij ∈ C¹(Ω̄)`, `a₀ ∈ C(Ω̄)`: a function
`u ∈ C²(Ω̄)` (as in `IsClassicalSolutionDirichlet`) satisfying (37) in the usual sense, with
`∂ⱼ(a_ij ∂ᵢu)(x) = D(a_ij ∂ᵢu)(x) e_j`. -/
def IsClassicalSolutionElliptic (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ) (a₀ f u : EuclideanSpace ℝ (Fin N) → ℝ) :
    Prop :=
  ContDiffOnClosure ℝ 2 u Ω ∧ ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
    (∀ x ∈ Ω, -(∑ i, ∑ j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single j 1)) + a₀ x * u x = f x) ∧
    EqOn u 0 (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))

/-- **Definition (§9.5, Example 3): a weak solution of (37)**: a function `u ∈ H^1_0(Ω)`
satisfying `∫_Ω ∑ᵢⱼ a_ij ∂u/∂xᵢ ∂v/∂xⱼ + ∫_Ω a₀ u v = ∫_Ω f v` for all `v ∈ H^1_0(Ω)` (38), the
coefficients being functions on `Ω`. -/
def IsWeakSolutionElliptic (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ) (a₀ : EuclideanSpace ℝ (Fin N) → ℝ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (u : hSpace N Ω) : Prop :=
  u ∈ hZeroSpace N Ω ∧ ∀ v ∈ hZeroSpace N Ω,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ∑ i, ∑ j, a i j x * partialDeriv u i x * partialDeriv v j x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- **Definition (§9.5, Example 3): a weak solution of (39)**, the general problem with
`a_ij, a_i, a₀ ∈ L^∞(Ω)`: a function `u ∈ H^1_0(Ω)` such that
`∫_Ω ∑ᵢⱼ a_ij ∂u/∂xᵢ ∂v/∂xⱼ + ∫_Ω ∑ᵢ a_i ∂u/∂xᵢ v + ∫_Ω a₀ u v = ∫_Ω f v` for all
`v ∈ H^1_0(Ω)` (40). The associated bilinear form (41) is `Elliptic.generalForm Ω A a₁ a₀`; in
general it is not symmetric (footnote 23). -/
def IsWeakSolutionGeneralElliptic (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (u : hSpace N Ω) : Prop :=
  u ∈ hZeroSpace N Ω ∧ ∀ v ∈ hZeroSpace N Ω,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv v j x)
      + (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          ∑ i, a₁ i x * partialDeriv u i x * SobolevMultiIndex.fn v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- **The form (41) is the left-hand side of (40)**, as three integrals, in the surface's
`partialDeriv` vocabulary (the backbone's `Elliptic.generalForm_apply_three`). -/
theorem generalForm_apply_three (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (u v : hSpace N Ω) :
    Elliptic.generalForm Ω A a₁ a₀ u v
      = (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv v j x)
        + (∫ x in (Ω : Set 𝔼), ∑ i, a₁ i x * partialDeriv u i x * SobolevMultiIndex.fn v x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x :=
  Elliptic.generalForm_apply_three Ω A a₁ a₀ u v

/-- **The weak formulation (40) is the backbone's Galerkin problem** for the form
`Elliptic.generalForm Ω A a₁ a₀` and the load `Elliptic.load Ω f` on `H^1_0(Ω)`. -/
theorem isWeakSolutionGeneralElliptic_iff
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsWeakSolutionGeneralElliptic Ω A a₁ a₀ f u ↔
      IsGalerkinSolution (Elliptic.generalForm Ω A a₁ a₀) (Elliptic.load Ω f)
        (hZeroSpace N Ω) u := by
  simp only [IsWeakSolutionGeneralElliptic, IsGalerkinSolution, generalForm_apply_three,
    Elliptic.load_apply]

/-- **The weak formulation (38), with function coefficients, is the backbone's Galerkin
problem** for the form `Elliptic.generalForm Ω A 0 A₀` on the `L^∞` classes `A i j = a_ij`,
`A₀ = a₀` (almost everywhere on `Ω`) and the load `Elliptic.load Ω f` on `H^1_0(Ω)`. -/
theorem isWeakSolutionElliptic_iff {a : Fin N → Fin N → 𝔼 → ℝ} {a₀ : 𝔼 → ℝ}
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))}
    (hA : ∀ i j, (A i j : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] a i j)
    {A₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))}
    (hA₀ : (A₀ : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] a₀)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsWeakSolutionElliptic Ω a a₀ f u ↔
      IsGalerkinSolution (Elliptic.generalForm Ω A 0 A₀) (Elliptic.load Ω f)
        (hZeroSpace N Ω) u := by
  have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i j, (A i j : 𝔼 → ℝ) x = a i j x :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ hA i j
  have hzero : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i,
      ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ) x = 0 := by
    filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set 𝔼))] with x hx i
    simpa only [Pi.zero_apply] using hx
  have key : ∀ v : hSpace N Ω, Elliptic.generalForm Ω A 0 A₀ u v
      = (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, a i j x * partialDeriv u i x * partialDeriv v j x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x := by
    intro v
    rw [generalForm_apply_three]
    have e1 : ∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv v j x
        = ∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, a i j x * partialDeriv u i x * partialDeriv v j x :=
      integral_congr_ae (hall.mono fun x hx ↦ by simp only [hx])
    have e2 : ∫ x in (Ω : Set 𝔼),
        ∑ i, ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ) x
          * partialDeriv u i x * SobolevMultiIndex.fn v x = ∫ x in (Ω : Set 𝔼), (0 : ℝ) :=
      integral_congr_ae (hzero.mono fun x hx ↦ by simp only [hx, zero_mul,
        Finset.sum_const_zero])
    have e3 : ∫ x in (Ω : Set 𝔼), A₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
        = ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x :=
      integral_congr_ae (hA₀.mono fun x hx ↦ by simp only [hx])
    rw [e1, e2, integral_zero, e3, add_zero]
  simp only [IsWeakSolutionElliptic, IsGalerkinSolution, key, Elliptic.load_apply]

/-- **Example 3, "as above, any classical solution is a weak solution".** Let `Ω` be bounded,
`a_ij ∈ C¹(Ω̄)` (`ContDiffOnClosure ℝ 1 (a i j) Ω`, footnote 16 of §9.3), `a₀ ∈ C(Ω̄)`, `u` a
classical solution of (37) (`IsClassicalSolutionElliptic Ω a a₀ f u`) and `f ∈ L²(Ω)`. Then `u`
is the function of some `U ∈ H^1_0(Ω)`, and `U` is a weak solution of (37). The backbone's
`Elliptic.isGalerkinSolution_general_of_classical` with the `L^∞(Ω)` classes of the coefficients
and no first-order term: `u ∈ H^1(Ω) ∩ C(Ω̄)` vanishes on `Γ`, hence lies in `H^1_0(Ω)`
(Theorem 9.17), and for `v ∈ C_c^1(Ω)` the identity (38) is the integration by parts
`∫_Ω ∂ⱼ(a_ij ∂ᵢu) v = −∫_Ω a_ij ∂ᵢu ∂ⱼv` of the `C¹` functions `a_ij ∂ᵢu`, extended to
`H^1_0(Ω)` by density. -/
theorem example_9_3_stepA (hb : Bornology.IsBounded (Ω : Set 𝔼)) {a : Fin N → Fin N → 𝔼 → ℝ}
    (ha : ∀ i j, ContDiffOnClosure ℝ 1 (a i j) Ω) {a₀ : 𝔼 → ℝ}
    (ha₀ : ContinuousOn a₀ (closure (Ω : Set 𝔼))) {f u : 𝔼 → ℝ}
    (hu : IsClassicalSolutionElliptic Ω a a₀ f u) (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace N Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionElliptic Ω a a₀ (hf.toLp f) U := by
  have hA := fun i j ↦ (ha i j).memLp_of_isBounded Ω hb ⊤
  have hA₀ := memLp_top_of_continuousOn_closure hb ha₀
  have hzero : ∀ i, ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ)
      =ᵐ[volume.restrict (Ω : Set 𝔼)] (fun _ ↦ (0 : ℝ)) := fun i ↦ by
    filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set 𝔼))] with x hx
    simpa only [Pi.zero_apply] using hx
  have heq : ∀ x ∈ Ω, -(∑ i, ∑ j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i, (fun _ : 𝔼 ↦ (0 : ℝ)) x * fderiv ℝ u x (EuclideanSpace.single i 1))
      + a₀ x * u x = f x := fun x hx ↦ by
    simpa only [zero_mul, Finset.sum_const_zero, add_zero] using hu.2.2.1 x hx
  obtain ⟨U, -, hUu, hUw⟩ := Elliptic.isGalerkinSolution_general_of_classical Ω hb hu.1 hu.2.1
    hu.2.2.2 (fun i j ↦ (ha i j).contDiffOn) (fun i j ↦ (hA i j).coeFn_toLp) hzero
    hA₀.coeFn_toLp hf heq
  exact ⟨U, hUu, (isWeakSolutionElliptic_iff (fun i j ↦ (hA i j).coeFn_toLp) hA₀.coeFn_toLp
    _ _).2 hUw⟩

end Example3

section Example3Bounded

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Example 3, existence and uniqueness.** Let `Ω ⊆ ℝ^N` be a bounded open set, `a_ij ∈ C(Ω̄)`
(the book: `C¹(Ω̄)`, needed only for the classical formulation) satisfying the ellipticity
condition (36), and `a₀ ∈ C(Ω̄)` with `a₀ ≥ 0` on `Ω`. Then for all `f ∈ L²(Ω)` there exists a
unique weak solution `u ∈ H^1_0(Ω)` of (37): Lax–Milgram in `H = H^1_0(Ω)` with the continuous
bilinear form (38), whose coerciveness comes from the ellipticity assumption, `a₀ ≥ 0` and
Poincaré's inequality (Corollary 9.19). The backbone's
`Elliptic.existsUnique_isGalerkinSolution_general_of_nonneg` on the `L^∞(Ω)` classes of the
coefficients. -/
theorem example_9_3 (hb : Bornology.IsBounded (Ω : Set 𝔼)) {a : Fin (d + 1) → Fin (d + 1) → 𝔼 → ℝ}
    (ha : ∀ i j, ContinuousOn (a i j) (closure (Ω : Set 𝔼))) {α : ℝ}
    (hell : ellipticityCondition Ω a α) {a₀ : 𝔼 → ℝ} (ha₀ : ContinuousOn a₀ (closure (Ω : Set 𝔼)))
    (ha₀0 : ∀ x ∈ Ω, 0 ≤ a₀ x) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace (d + 1) Ω, IsWeakSolutionElliptic Ω a a₀ f u := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hA := fun i j ↦ memLp_top_of_continuousOn_closure hb (ha i j)
  have hA₀ := memLp_top_of_continuousOn_closure hb ha₀
  have hnn : 0 ≤ hA₀.toLp a₀ := by
    refine (Lp.coeFn_nonneg _).1 ?_
    filter_upwards [hA₀.coeFn_toLp, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx]
    exact ha₀0 x hxΩ
  simp only [isWeakSolutionElliptic_iff (A := fun i j ↦ (hA i j).toLp (a i j))
    (fun i j ↦ (hA i j).coeFn_toLp) hA₀.coeFn_toLp]
  exact Elliptic.existsUnique_isGalerkinSolution_general_of_nonneg (le_max_right R 0)
    (hR.trans (ball_subset_ball (le_max_left R 0)))
    (isUniformlyElliptic_of_ellipticityCondition hell fun i j ↦ (hA i j).coeFn_toLp) hnn f

/-- **Example 3, the symmetric case.** If moreover the matrix `(a_ij)` is symmetric, the form
(38) is symmetric and the weak solution `u` of (37) is obtained by
`min_{v ∈ H^1_0} {½ ∫_Ω (∑ᵢⱼ a_ij ∂ᵢv ∂ⱼv + a₀ v²) − ∫_Ω f v}`: for `u ∈ H^1_0(Ω)`, `u` minimizes
this energy over `H^1_0(Ω)` if and only if it is the weak solution. The backbone's
`Elliptic.isMinOn_energy_iff_isGalerkinSolution_general_of_symm`. -/
theorem example_9_3_isMinOn (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {a : Fin (d + 1) → Fin (d + 1) → 𝔼 → ℝ} (ha : ∀ i j, ContinuousOn (a i j) (closure (Ω : Set 𝔼)))
    (hsymm : ∀ i j, a i j = a j i) {α : ℝ} (hell : ellipticityCondition Ω a α) {a₀ : 𝔼 → ℝ}
    (ha₀ : ContinuousOn a₀ (closure (Ω : Set 𝔼))) (ha₀0 : ∀ x ∈ Ω, 0 ≤ a₀ x)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {u : hSpace (d + 1) Ω}
    (hu : u ∈ hZeroSpace (d + 1) Ω) :
    IsMinOn (fun v : hSpace (d + 1) Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        ((∑ i, ∑ j, a i j x * partialDeriv v i x * partialDeriv v j x)
          + a₀ x * SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) (hZeroSpace (d + 1) Ω) u
      ↔ IsWeakSolutionElliptic Ω a a₀ f u := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hA := fun i j ↦ memLp_top_of_continuousOn_closure hb (ha i j)
  have hA₀ := memLp_top_of_continuousOn_closure hb ha₀
  have hnn : 0 ≤ hA₀.toLp a₀ := by
    refine (Lp.coeFn_nonneg _).1 ?_
    filter_upwards [hA₀.coeFn_toLp, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx]
    exact ha₀0 x hxΩ
  have hAsymm : ∀ i j, (hA i j).toLp (a i j) = (hA j i).toLp (a j i) := fun i j ↦ by
    simp only [hsymm i j]
  have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i j,
      ((hA i j).toLp (a i j) : 𝔼 → ℝ) x = a i j x :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ (hA i j).coeFn_toLp
  have e : (fun v : hSpace (d + 1) Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        ((∑ i, ∑ j, a i j x * partialDeriv v i x * partialDeriv v j x)
          + a₀ x * SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
      = (Elliptic.generalForm Ω (fun i j ↦ (hA i j).toLp (a i j)) 0 (hA₀.toLp a₀)).energy
        (Elliptic.load Ω f) := by
    funext v
    rw [SesqForm.energy, Elliptic.generalForm_apply, Elliptic.load_apply]
    simp only [RCLike.re_to_real]
    congr 2
    refine integral_congr_ae ?_
    have hzero : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i,
        ((0 : Fin (d + 1) → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ) x = 0 := by
      filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set 𝔼))] with x hx i
      simpa only [Pi.zero_apply] using hx
    filter_upwards [hall, hzero, hA₀.coeFn_toLp] with x hx hx0 hx₀
    simp only [hx, hx0, hx₀, zero_mul, Finset.sum_const_zero, add_zero, sq, mul_assoc]
    rfl
  rw [e, isWeakSolutionElliptic_iff (A := fun i j ↦ (hA i j).toLp (a i j))
    (fun i j ↦ (hA i j).coeFn_toLp) hA₀.coeFn_toLp]
  exact Elliptic.isMinOn_energy_iff_isGalerkinSolution_general_of_symm (le_max_right R 0)
    (hR.trans (ball_subset_ball (le_max_left R 0)))
    (isUniformlyElliptic_of_ellipticityCondition hell fun i j ↦ (hA i j).coeFn_toLp) hAsymm hnn hu

end Example3Bounded

/-! ### Theorem 9.23: the Fredholm alternative -/

section Fredholm

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

/-- The weak solutions of the homogeneous problem (40) with `f = 0` are the elements of the
backbone's subspace `Elliptic.homogeneousKernel Ω (generalForm Ω A a₁ a₀)` of `H^1(Ω)`. -/
theorem mem_homogeneousKernel_iff_isWeakSolutionGeneralElliptic (u : hSpace N Ω) :
    u ∈ Elliptic.homogeneousKernel Ω (Elliptic.generalForm Ω A a₁ a₀) ↔
      IsWeakSolutionGeneralElliptic Ω A a₁ a₀ 0 u := by
  rw [Elliptic.mem_homogeneousKernel_iff_isGalerkinSolution, isWeakSolutionGeneralElliptic_iff]

/-- **Theorem 9.23 (the Fredholm alternative for (40)).** Let `Ω` be bounded,
`a_ij, a_i, a₀ ∈ L^∞(Ω)` with `(a_ij)` elliptic. If `f = 0`, the set of solutions `u ∈ H^1_0` of
(40) — the subspace `Elliptic.homogeneousKernel`,
`mem_homogeneousKernel_iff_isWeakSolutionGeneralElliptic` — is a finite-dimensional vector space,
say of dimension `d`. Moreover, there exists a subspace
`F ⊆ L²(Ω)` of dimension `d` such that (40) has a solution if and only if `∫_Ω f v = 0` for all
`v ∈ F` (footnote 24: `d` orthogonality conditions). The backbone's
`Elliptic.finiteDimensional_ker_general` and `Elliptic.exists_orthogonality_iff_exists_solution`,
proved as in the book: Gårding's inequality gives `λ` with `a + λ ∫ uv` coercive on `H^1_0`, the
solution operator `T : L² → L²` is compact (the injection `H^1_0 ⊂ L²` is compact for a bounded
`Ω`, Theorem 9.16 and Remark 20), (40) is `v − λ T v = f` with `v = f + λ u`, and Fredholm's
alternative (Theorem 6.6) concludes. Only `|Ω| < ∞` is used. -/
theorem theorem_9_23 (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hA : Elliptic.IsUniformlyElliptic Ω A α) :
    FiniteDimensional ℝ (Elliptic.homogeneousKernel Ω (Elliptic.generalForm Ω A a₁ a₀)) ∧
    ∃ F : Submodule ℝ (Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))), FiniteDimensional ℝ F ∧
      Module.finrank ℝ F
        = Module.finrank ℝ (Elliptic.homogeneousKernel Ω (Elliptic.generalForm Ω A a₁ a₀)) ∧
      ∀ f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
        (∃ u, IsWeakSolutionGeneralElliptic Ω A a₁ a₀ f u) ↔
          ∀ v ∈ F, ∫ x in (Ω : Set 𝔼), f x * v x = 0 := by
  refine ⟨Elliptic.finiteDimensional_ker_general Ω hb.measure_lt_top.ne hA, ?_⟩
  obtain ⟨F, hF, hd, h⟩ := Elliptic.exists_orthogonality_iff_exists_solution Ω (a₁ := a₁)
    (a₀ := a₀) hb.measure_lt_top.ne hA
  refine ⟨F, hF, hd, fun f ↦ ?_⟩
  simp only [isWeakSolutionGeneralElliptic_iff, h f, MeasureTheory.L2.inner_eq_integral_mul]

/-- **Remark 23, first clause.** Suppose that the homogeneous equation associated to (40), i.e.
with `f = 0`, has `u = 0` as its unique solution. Then for every `f ∈ L²` there exists a unique
solution `u ∈ H^1_0` of (40) (footnote 25: existence follows from uniqueness by Fredholm's
alternative). The backbone's `Elliptic.existsUnique_of_ker_eq_bot`. -/
theorem remark_9_23 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (h : ∀ u : hSpace N Ω, IsWeakSolutionGeneralElliptic Ω A a₁ a₀ 0 u → u = 0)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace N Ω, IsWeakSolutionGeneralElliptic Ω A a₁ a₀ f u := by
  simp only [isWeakSolutionGeneralElliptic_iff]
  refine Elliptic.existsUnique_of_ker_eq_bot Ω hb.measure_lt_top.ne hA ?_ f
  rw [Submodule.eq_bot_iff]
  intro u hu
  exact h u ((mem_homogeneousKernel_iff_isWeakSolutionGeneralElliptic u).1 hu)

/-- **Remark 23, second clause, in the case `a_i = 0`** the book proves in §9.7: if `a_i = 0` and
`a₀ ≥ 0` on `Ω`, then for every `f ∈ L²` there exists a unique weak solution `u ∈ H^1_0` of
(40). The homogeneous kernel is trivial because a weak solution `u ∈ H^1_0(Ω)` with `f = 0`
satisfies `u ≥ 0` and `−u ≥ 0` a.e. by the maximum principle in its `H^1_0` form (footnote 38,
the backbone's `Elliptic.nonneg_of_mem_zero_general_zero_drift` and
`nonpos_of_mem_zero_general_zero_drift`); then `remark_9_23`. The case of arbitrary `a_i` is the
general Proposition 9.29 (Gilbarg–Trudinger), not proved by the book. Needs `N ≥ 1` (the
constancy argument of footnote 39 uses `|ℝ^N| = ∞`). -/
theorem remark_9_23_zero_drift (hN : N ≠ 0) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ a₀ x)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace N Ω, IsWeakSolutionGeneralElliptic Ω A 0 a₀ f u := by
  refine remark_9_23 hb hA (fun u hu ↦ ?_) f
  rw [isWeakSolutionGeneralElliptic_iff] at hu
  have hf0 : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)),
      ((0 : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : 𝔼 → ℝ) x = 0 :=
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict (Ω : Set 𝔼))
  have h1 := Elliptic.nonneg_of_mem_zero_general_zero_drift hN hA ha₀ hu.1 hu.2
    (hf0.mono fun x hx ↦ hx.symm.le)
  have h2 := Elliptic.nonpos_of_mem_zero_general_zero_drift hN hA ha₀ hu.1 hu.2
    (hf0.mono fun x hx ↦ hx.le)
  refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
  have hz : SobolevMultiIndex.fn (0 : hSpace N Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] 0 :=
    SobolevMultiIndex.fn_zero
  refine Filter.EventuallyEq.trans ?_ hz.symm
  filter_upwards [h1, h2] with x hx1 hx2
  exact le_antisymm hx2 hx1

end Fredholm

/-! ### Example 4: the homogeneous Neumann problem -/

section Example4

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Definition (§9.5, Example 4): a classical solution of (44)**, `-Δu + u = f` in `Ω`,
`∂u/∂n = 0` on `Γ`, for a given outward unit normal field `n` on `Γ` (no normal field is derived
from the class `C^1` here): `u ∈ C²(Ω̄)` (as in `IsClassicalSolutionDirichlet`) with
`-Δu + u = f` in `Ω`, and the normal derivative `∂u/∂n = ∇u · n` vanishes on `Γ` — read through
the continuous extension `g` of `Du` to `Ω̄` provided by `u ∈ C²(Ω̄)` (unique, `Ω` being dense in
`Ω̄`): `g x (n x) = 0` for every `x ∈ Γ`. -/
def IsClassicalSolutionNeumann (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (n : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (f u : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ContDiffOnClosure ℝ 2 u Ω ∧ ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
    (∀ x ∈ Ω, -Δ u x + u x = f x) ∧
    ∃ g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
      ContinuousOn g (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
      EqOn g (fderiv ℝ u) Ω ∧ ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin N))), g x (n x) = 0

/-- **Definition (§9.5, Example 4): a weak solution of (44)**: a function `u ∈ H^1(Ω)` satisfying
`∫_Ω ∇u · ∇v + ∫_Ω u v = ∫_Ω f v` for all `v ∈ H^1(Ω)` (45). -/
def IsWeakSolutionNeumann (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (u : hSpace N Ω) : Prop :=
  ∀ v : hSpace N Ω,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, partialDeriv u i x * partialDeriv v i x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- **The weak formulation (45) is the backbone's Galerkin problem** for the form
`Elliptic.laplaceForm Ω` and the load `Elliptic.load Ω f` on the whole space `H^1(Ω)`. -/
theorem isWeakSolutionNeumann_iff (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsWeakSolutionNeumann Ω f u ↔
      IsGalerkinSolution (Elliptic.laplaceForm Ω) (Elliptic.load Ω f) ⊤ u := by
  simp only [IsWeakSolutionNeumann, IsGalerkinSolution, Submodule.mem_top, true_and, true_implies,
    laplaceForm_apply_two, Elliptic.load_apply]

/-- **Proposition 9.24.** For every `f ∈ L²(Ω)` there exists a unique weak solution `u ∈ H^1(Ω)`
of the Neumann problem (44): Lax–Milgram in `H = H^1(Ω)`, the backbone's
`Elliptic.existsUnique_isGalerkinSolution_neumann`. The book assumes `Ω` bounded of class `C^1`,
which this proposition does not use. -/
theorem proposition_9_24 (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace N Ω, IsWeakSolutionNeumann Ω f u := by
  simp only [isWeakSolutionNeumann_iff]
  exact Elliptic.existsUnique_isGalerkinSolution_neumann Ω f

/-- **Proposition 9.24, "furthermore"**: the weak solution `u` of (44) is obtained by
`min_{v ∈ H^1(Ω)} {½ ∫_Ω (|∇v|² + v²) − ∫_Ω f v}`, and conversely a minimizer is the weak
solution. The backbone's `Elliptic.isMinOn_energy_iff_isGalerkinSolution_neumann`. -/
theorem proposition_9_24_isMinOn (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsMinOn (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) univ u
      ↔ IsWeakSolutionNeumann Ω f u := by
  have e : (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
      = (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) := by
    funext v
    rw [Elliptic.energy_laplace_apply]
    simp only [sq]
    rfl
  rw [e, isWeakSolutionNeumann_iff]
  exact Elliptic.isMinOn_energy_iff_isGalerkinSolution_neumann Ω u

/-- **Example 4, Step D, the interior clause.** If a weak solution `U ∈ H^1(Ω)` of (44) has a
representative `u ∈ C²(Ω)`, then `-Δu + u = f` a.e. in `Ω`, and everywhere in `Ω` if `f` has a
representative continuous on `Ω`: the weak identity (46) with `v ∈ C_c^1(Ω)` and Corollary 4.24,
the backbone's `Elliptic.laplacian_ae_eq_of_forall_testFunction` — a Neumann weak solution is in
particular a solution against the test functions. -/
theorem example_9_4_stepD_interior {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {U : hSpace N Ω}
    (hU : IsWeakSolutionNeumann Ω f U) {u : 𝔼 → ℝ}
    (hUu : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u) (hu : ContDiffOn ℝ 2 u Ω) :
    (fun x ↦ -Δ u x + u x) =ᵐ[volume.restrict (Ω : Set 𝔼)] f ∧
      ∀ g : 𝔼 → ℝ, ContinuousOn g Ω → (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] g →
        ∀ x ∈ Ω, -Δ u x + u x = g x := by
  have hUw := (isWeakSolutionNeumann_iff f U).1 hU
  have hae := Elliptic.laplacian_ae_eq_of_forall_testFunction Ω
    (fun V _ ↦ hUw.2 V Submodule.mem_top) hu hUu
  refine ⟨hae, fun g hg hfg ↦ ?_⟩
  exact Measure.eqOn_open_of_ae_eq (hae.trans hfg) Ω.isOpen
    ((Elliptic.continuousOn_laplacian Ω hu).neg.add
      (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn) hg

/-! ### Example 5: unbounded domains -/

/-- **Example 5 (a), `Ω = ℝ^N`.** Given `f ∈ L²(ℝ^N)`, the equation `-Δu + u = f` in `ℝ^N` has a
unique weak solution in the following sense: `u ∈ H^1(ℝ^N)` and
`∫ ∇u · ∇v + ∫ u v = ∫ f v` for all `v ∈ H^1(ℝ^N)`. Proposition 9.24 on `Ω = ℝ^N`, which needs no
boundedness (equivalently Theorem 9.21, since `H^1_0(ℝ^N) = H^1(ℝ^N)`, Remark 17). -/
theorem example_9_5_a (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))) :
    ∃! u : hSpace N ⊤, IsWeakSolutionNeumann ⊤ f u :=
  proposition_9_24 f

end Example4

section Example5

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- **Example 5 (b), `Ω = ℝ^N_+` with the Dirichlet condition `u(x', 0) = 0`.** Given
`f ∈ L²(ℝ^N_+)`, the problem `-Δu + u = f` in `ℝ^N_+`, `u(x', 0) = 0`, has a unique weak solution
in the following sense: `u ∈ H^1_0(Ω)` and `∫_Ω ∇u · ∇v + ∫_Ω u v = ∫_Ω f v` for all
`v ∈ H^1_0(Ω)`. Theorem 9.21 on the half space, which needs no boundedness. -/
theorem example_9_5_b
    (f : Lp ℝ 2 (volume.restrict ((EuclideanSpace.upperHalfSpaceOpens d : Opens 𝔼) : Set 𝔼))) :
    ∃! u : hSpace (d + 1) (EuclideanSpace.upperHalfSpaceOpens d),
      IsWeakSolutionDirichlet (EuclideanSpace.upperHalfSpaceOpens d) f u :=
  theorem_9_21 f

/-- **Example 5 (c), `Ω = ℝ^N_+` with the Neumann condition `∂u/∂x_N (x', 0) = 0`.** Given
`f ∈ L²(ℝ^N_+)`, the problem has a unique weak solution in the following sense: `u ∈ H^1(Ω)` and
`∫_Ω ∇u · ∇v + ∫_Ω u v = ∫_Ω f v` for all `v ∈ H^1(Ω)`. Proposition 9.24 on the half space. -/
theorem example_9_5_c
    (f : Lp ℝ 2 (volume.restrict ((EuclideanSpace.upperHalfSpaceOpens d : Opens 𝔼) : Set 𝔼))) :
    ∃! u : hSpace (d + 1) (EuclideanSpace.upperHalfSpaceOpens d),
      IsWeakSolutionNeumann (EuclideanSpace.upperHalfSpaceOpens d) f u :=
  proposition_9_24 f

end Example5

end Brezis.Chapter09
