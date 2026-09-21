import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Numlib.Analysis.Distributions.TestFunctionOps
import Numlib.Analysis.PDE.Elliptic.Dirichlet
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.MeasureTheory.Function.ContinuousOnClosure
import Numlib.MeasureTheory.Function.LpSpace.Order
import Numlib.Variational.Inequality.Basic
import NumlibSurface.AtkinsonHan.Chapter08.Section02
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson–Han §11.1: from variational equations to variational inequalities

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §11.1.

The section motivates the chapter with two problems: the obstacle problem (Example 11.1.1), a
minimization of the Dirichlet energy over a convex set that is not a subspace, and the simplified
friction problem (Example 11.1.2), a minimization over a space of an energy with a
non-differentiable boundary term.  Both are here: the friction problem, whose functional
`g ∫_Γ |v| ds` needs the trace of an `H¹(Ω)` function and the surface measure on `Γ`, is stated
over the boundary interface `BoundaryData Ω`, `BoundaryData.TraceFamily` of
`Numlib/Analysis/Sobolev/Boundary/Data.lean` (instances: bounded `C¹` domains,
`IsContDiffDomain.traceFamily`; polygons without slits, `Triangulation.traceFamily`).

## The obstacle problem

The setting is a bounded open `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}`, the space `V = H¹₀(Ω)` of the backbone,
`SobolevEuclideanZero (d + 1) 1 2 Ω`, an obstacle `ψ ∈ H¹(Ω) = SobolevEuclidean (d + 1) 1 2 Ω`
and a load `f ∈ L²(Ω)`:

* `dirichletBilinForm Ω` is the bilinear form `a(u, v) = ∫_Ω ∇u · ∇v` of (11.1.3) on `H¹₀(Ω)`,
  the operator `modelOperator Ω` of Example 8.2.6 (`Chapter08/Section02`) read as a form of §8.3
  (`dirichletBilinForm_apply` is its value, the backbone's `Elliptic.dirichletForm`): bounded
  with `M = 1`, symmetric, and `V`-elliptic with `α = (1 + (2R)²)⁻¹` by Poincaré's inequality
  (`dirichletBilinForm_isEllipticWith`);
* `loadZero Ω f` is `ℓ(v) = ∫_Ω f v` on `H¹₀(Ω)`;
* `obstacleEnergy Ω f` is the energy `E(v) = ∫_Ω (½ |∇v|² − f v)` of (11.1.5), the energy
  `½ a(v, v) − ℓ(v)` of Theorem 8.3.3 (`obstacleEnergy_apply` is the displayed formula);
* `obstacleSet Ω ψ` is the admissible set `K = {v ∈ H¹₀(Ω) | v ≥ ψ a.e. in Ω}`, nonempty
  (`obstacleSet_nonempty`), closed (`isClosed_obstacleSet`) and convex (`convex_obstacleSet`).

`example_11_1_1` is the characterization of the minimizer by the variational inequality (11.1.7),
`∫_Ω ∇u · ∇(v − u) ≥ ∫_Ω f (v − u)` for all `v ∈ K`, which the book leaves as Exercise 11.1.1 and
which is Theorem 8.3.3's (8.3.3) on the convex set `K`; `example_11_1_1_pointwise` is its
pointwise form (11.1.9).  Existence and uniqueness are Example 11.2.3 (`Chapter11/Section02`)
and Example 11.3.10 (`Chapter11/Section03`).

## The simplified friction problem

For `B : BoundaryData Ω`, `𝒯 : B.TraceFamily` (surface measure `σ = B.σ` on `Γ`, trace
`γ = 𝒯.traceL 2 : H¹(Ω) →L L²(σ)`), `g > 0` and `f ∈ L²(Ω)`:

* `frictionFunctional B 𝒯 g` is `j(v) = g ∫_Γ |v| ds`, convex (`convexOn_frictionFunctional`)
  and continuous (`continuous_frictionFunctional`), positively homogeneous and subadditive;
* `frictionEnergy B 𝒯 g f` is the energy (11.1.12), `E(v) = ∫_Ω (½ (|∇v|² + v²) − f v) + j(v)`
  (`frictionEnergy_apply`), the energy of the form `a(u, v) = ∫_Ω (∇u·∇v + u v)` — the
  backbone's `Elliptic.laplaceForm Ω` — plus `j`;
* `example_11_1_2` is the equivalence of the minimization problem (11.1.12) with the variational
  inequality (11.1.13), `a(u, v − u) + j(v) − j(u) ≥ ℓ(v − u)` for all `v ∈ H¹(Ω)` (Exercise
  11.1.2; the backbone's `isMinOn_energy_add_iff`, which is Theorem 11.2.1 with `K = V`);
* `example_11_1_2_pointwise` is the pointwise form (11.1.14)–(11.1.15) of a smooth solution on
  a bounded `C¹` domain: `−Δu + u = f` a.e. in `Ω`, and `|∂u/∂ν| ≤ g`, `(∂u/∂ν) u + g |u| = 0` at
  every point of `Γ`, the normal derivative being read through the continuous extension of
  `∇u` to `Ω̄`.  It rests on Green's formula `BoundaryData.integral_laplacian_mul_add_eq`, the
  density of smooth functions (`IsContDiffDomain.hasSmoothDensity`), the continuity of the
  outward normal (`IsContDiffDomain.continuousOn_outwardNormal`) and the positivity of the surface
  measure on open sets meeting `Γ` (`IsContDiffDomain.boundaryMeasure_pos_of_isOpen`), through
  bump tests on the boundary (`exists_bump_lt_integral_mul`).

## Deviations from the book

* The book's "`ψ ≤ 0` on `Γ`", a statement about the trace, enters as the hypothesis that the
  positive part `max (ψ, 0)` is the function of an element of `H¹₀(Ω)` — exactly what the book
  uses it for (`max (0, ψ) ∈ K`, Example 11.2.3).  When `ψ` has a representative continuous on
  `closure Ω` that is `≤ 0` on `∂Ω`, this hypothesis follows from the backbone's Theorem 9.17
  (`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`) applied to `max (ψ, 0)`,
  which lies in `H¹(Ω)` by `MemSobolevMultiIndex.posPart`.
* The book's Lipschitz boundary is not needed for the obstacle problem; `Ω` is any bounded open
  set.  For the friction problem it is the `C¹` (or polygonal) hypothesis behind the boundary
  interface, and the pointwise form is proved on a bounded `C¹` domain.
* The pointwise complementarity form (11.1.9) under the regularity (11.1.8) is
  `example_11_1_1_pointwise`, stated through representatives `f̃`, `ψ̃` continuous on `Ω` and
  `ũ` of class `C²` on `Ω`; the book's `u ∈ C(Ω̄)` is not needed for the relations in `Ω`.  It
  runs on the two forms of the fundamental lemma of the calculus of variations of
  `Numlib/Analysis/Distributions/TestFunctionOps.lean` — the inequality form
  `nonneg_on_of_forall_integral_mul_testFunction_nonneg` and the localized form
  `eqOn_zero_of_forall_integral_mul_testFunction_eq_zero` — and the integration by parts
  `Elliptic.dirichletForm_eq_integral_neg_laplacian_mul` of
  `Numlib/Analysis/PDE/Elliptic/Dirichlet.lean`.
* The AH surface's own `H¹₀(Ω)` (`AtkinsonHan.Chapter07.definition_7_2_9`) is the same closure
  taken in the tensor formulation `Sobolev ℝ 1 2 Ω volume`; the backbone's Dirichlet form and
  Poincaré inequality are stated on the multi-index formulation, which is why the obstacle
  problem is set there (see `AtkinsonHan.Chapter08.modelOperator`).
-/

open Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped ContDiff Distributions ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter11

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-! ### The bilinear form, the load and the energy of (11.1.3)–(11.1.5) -/

/-- **The bilinear form `a(u, v) = ∫_Ω ∇u · ∇v` of (11.1.3)** on `H¹₀(Ω)`: the operator
`modelOperator Ω` of Example 8.2.6 read as a bilinear form of §8.3. -/
noncomputable def dirichletBilinForm : BilinForm (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  BilinForm.ofCLM (Chapter08.modelOperator Ω)

/-- `a(u, v)` is the backbone's Dirichlet form `Elliptic.dirichletForm Ω u v = ∫_Ω ∇u · ∇v`
(`Elliptic.dirichletForm_apply`). A `def` rather than an `abbrev`, so that rewriting at a value
of the form never unfolds `modelOperator`. -/
theorem dirichletBilinForm_apply (u v : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    dirichletBilinForm Ω u v = Elliptic.dirichletForm Ω u v :=
  rfl

/-- The form (11.1.3) is bounded with constant `1` (`Elliptic.dirichletForm_isBoundedWith`). -/
theorem dirichletBilinForm_isBoundedWith : (dirichletBilinForm Ω).IsBoundedWith 1 := fun u v ↦ by
  rw [dirichletBilinForm_apply, one_mul, ← Real.norm_eq_abs]
  have h := Elliptic.dirichletForm_isBoundedWith Ω u v
  rwa [one_mul] at h

/-- The form (11.1.3) is `V`-elliptic on `H¹₀(Ω)` of a bounded `Ω ⊆ B(0, R)`, with constant
`(1 + (2R)²)⁻¹`: Poincaré's inequality (`Elliptic.dirichletForm_restrict_isCoerciveWith`). -/
theorem dirichletBilinForm_isEllipticWith {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) :
    (dirichletBilinForm Ω).IsEllipticWith (1 + (2 * R) ^ 2)⁻¹ := fun v ↦ by
  rw [dirichletBilinForm_apply]
  exact Elliptic.dirichletForm_restrict_isCoerciveWith Ω hR hΩ v

/-- The form (11.1.3) is symmetric. -/
theorem dirichletBilinForm_isSymm : LinearMap.BilinForm.IsSymm (dirichletBilinForm Ω) := by
  unfold dirichletBilinForm
  rw [BilinForm.isSymm_ofCLM_iff]
  intro u v
  have h := Elliptic.dirichletForm_isHermitian Ω u v
  rw [conj_trivial] at h
  exact h

/-- **The load `ℓ(v) = ∫_Ω f v` of (11.1.3)** on `H¹₀(Ω)`, for `f ∈ L²(Ω)`: the backbone's
`Elliptic.load Ω f` restricted to `H¹₀(Ω)`. -/
noncomputable def loadZero
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  (Elliptic.load Ω f).comp (SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL

/-- `loadZero Ω f v = ∫_Ω f v`. -/
theorem loadZero_apply
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    loadZero Ω f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      f x * SobolevMultiIndex.fn (v : SobolevEuclidean (d + 1) 1 2 Ω) x :=
  Elliptic.load_apply Ω f v

/-- The load is linear in the datum. -/
theorem loadZero_sub
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    loadZero Ω (f - g) = loadZero Ω f - loadZero Ω g := by
  ext v
  exact Elliptic.load_sub (Ω := Ω) f g v

/-- `‖loadZero Ω f‖ ≤ ‖f‖_{L²(Ω)}`. -/
theorem norm_loadZero_le
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ‖loadZero Ω f‖ ≤ ‖f‖ :=
  ((Elliptic.load Ω f).opNorm_comp_le _).trans <| by
    calc ‖Elliptic.load Ω f‖ * ‖(SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL‖
        ≤ ‖f‖ * 1 := by
          gcongr
          · exact Elliptic.norm_load_le Ω f
          · exact Submodule.norm_subtypeL_le _
      _ = ‖f‖ := mul_one _

/-- `‖loadZero Ω f − loadZero Ω g‖ ≤ ‖f − g‖_{L²(Ω)}`. -/
theorem norm_loadZero_sub_le
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ‖loadZero Ω f - loadZero Ω g‖ ≤ ‖f - g‖ := by
  rw [← loadZero_sub]
  exact norm_loadZero_le Ω _

/-- **The energy functional (11.1.5)**, `E(v) = ∫_Ω (½ |∇v|² − f v)` on `H¹₀(Ω)`: the energy
`½ a(v, v) − ℓ(v)` of Theorem 8.3.3 for the form (11.1.3) and the load `∫_Ω f v`. -/
noncomputable def obstacleEnergy
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    SobolevEuclideanZero (d + 1) 1 2 Ω → ℝ :=
  (dirichletBilinForm Ω).energy (loadZero Ω f)

/-- `∑ᵢ (∂ᵢv)²` is integrable on `Ω` for `v ∈ H¹(Ω)`. -/
theorem integrable_sum_sq_weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω) :
    Integrable (fun x ↦ ∑ i, SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x ^ 2)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  refine integrable_finsetSum _ fun i _ ↦ ?_
  exact (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))
    (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))).congr
    (Eventually.of_forall fun x ↦ by simp [sq])

/-- `f v` is integrable on `Ω` for `f ∈ L²(Ω)` and `v ∈ H¹(Ω)`. -/
theorem integrable_mul_fn
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v : SobolevEuclidean (d + 1) 1 2 Ω) :
    Integrable (fun x ↦ f x * SobolevMultiIndex.fn v x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (L2.integrable_inner (𝕜 := ℝ) f (SobolevMultiIndex.weakDeriv v 0)).congr
    (Eventually.of_forall fun x ↦ by
      simp only [RCLike.inner_apply, conj_trivial]
      rw [mul_comm]
      rfl)

/-- **The energy (11.1.5) is the displayed integral**: `E(v) = ∫_Ω (½ ∑ᵢ (∂ᵢv)² − f v)`. -/
theorem obstacleEnergy_apply
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    obstacleEnergy Ω f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ((1 / 2 : ℝ) * ∑ i, SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
        (MultiIndexLE.single i) x ^ 2
        - f x * SobolevMultiIndex.fn (v : SobolevEuclidean (d + 1) 1 2 Ω) x) := by
  have h1 : dirichletBilinForm Ω v v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ∑ i, SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
        (MultiIndexLE.single i) x ^ 2 := by
    rw [dirichletBilinForm_apply, Elliptic.dirichletForm_apply]
    simp only [sq]
  rw [integral_sub ((integrable_sum_sq_weakDeriv Ω _).const_mul _) (integrable_mul_fn Ω f _),
    integral_const_mul]
  change (1 / 2 : ℝ) * dirichletBilinForm Ω v v - loadZero Ω f v = _
  rw [h1, loadZero_apply]

/-! ### The admissible set `K` -/

/-- **The admissible set `K = {v ∈ H¹₀(Ω) | v ≥ ψ a.e. in Ω}`** of the obstacle problem
(Example 11.1.1), for an obstacle `ψ ∈ H¹(Ω)`: the `v ∈ H¹₀(Ω)` whose function dominates that of
`ψ` in the almost-everywhere order of `L²(Ω)` (`mem_obstacleSet_iff` is the pointwise reading). -/
def obstacleSet (ψ : SobolevEuclidean (d + 1) 1 2 Ω) :
    Set (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  {v | SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume ψ
    ≤ SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume v}

/-- `v ∈ K` iff `ψ ≤ v` almost everywhere on `Ω`. -/
theorem mem_obstacleSet_iff {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {v : SobolevEuclideanZero (d + 1) 1 2 Ω} :
    v ∈ obstacleSet Ω ψ ↔ ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      SobolevMultiIndex.fn ψ x ≤ SobolevMultiIndex.fn (v : SobolevEuclidean (d + 1) 1 2 Ω) x := by
  change SobolevMultiIndex.fnL ℝ _ 1 2 Ω volume ψ ≤ SobolevMultiIndexZero.fnL ℝ _ 1 2 Ω volume v ↔ _
  rw [← Lp.coeFn_le, SobolevMultiIndexZero.fnL_apply, SobolevMultiIndex.fnL_apply]
  exact Iff.rfl

/-- **`K` is closed** in `H¹₀(Ω)`: the preimage of the closed order interval `{g | ψ ≤ g}` of
`L²(Ω)` under the continuous inclusion `H¹₀(Ω) → L²(Ω)`. -/
theorem isClosed_obstacleSet (ψ : SobolevEuclidean (d + 1) 1 2 Ω) :
    IsClosed (obstacleSet Ω ψ) :=
  isClosed_Ici.preimage (SobolevMultiIndexZero.fnL ℝ _ 1 2 Ω volume).continuous

/-- **`K` is convex**: the preimage of a convex order interval under a linear map. -/
theorem convex_obstacleSet (ψ : SobolevEuclidean (d + 1) 1 2 Ω) : Convex ℝ (obstacleSet Ω ψ) :=
  (Lp.convex_Ici _).linear_preimage
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume :
      SobolevEuclideanZero (d + 1) 1 2 Ω →ₗ[ℝ]
        Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))

/-- **`K` is nonempty: it contains `max (0, ψ)`** (Example 11.2.3), as soon as the positive part
of the obstacle is the function of an element of `H¹₀(Ω)` — the reading of the book's "`ψ ≤ 0`
on `Γ`" (see the module docstring). -/
theorem obstacleSet_nonempty {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    (hψ : ∃ w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ max (SobolevMultiIndex.fn ψ x) 0) :
    (obstacleSet Ω ψ).Nonempty := by
  obtain ⟨w, hw, hwψ⟩ := hψ
  refine ⟨⟨w, hw⟩, ?_⟩
  rw [mem_obstacleSet_iff]
  filter_upwards [hwψ] with x hx
  rw [hx]
  exact le_max_left _ _

/-! ### Example 11.1.1: the obstacle problem -/

/-- **Example 11.1.1 (the obstacle problem)**, the variational inequality (11.1.7): on a bounded
open `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}`, for an obstacle `ψ ∈ H¹(Ω)` and a load `f ∈ L²(Ω)`, a displacement
`u ∈ K = {v ∈ H¹₀(Ω) | v ≥ ψ a.e.}` minimizes the energy `E(v) = ∫_Ω (½ |∇v|² − f v)` over `K`
— the minimum-energy principle (11.1.6) — if and only if

  `∫_Ω ∇u · ∇(v − u) ≥ ∫_Ω f (v − u)`  for every `v ∈ K`.

The book leaves this to Exercise 11.1.1; it is Theorem 8.3.3's characterization (8.3.3) of the
minimizer of the energy of a symmetric `V`-elliptic form on a convex set
(`Chapter08.theorem_8_3_3_iff`), the form being (11.1.3) and its ellipticity Poincaré's
inequality.  That the minimizer exists and is unique is Example 11.2.3
(`Chapter11.example_11_2_3`).  The pointwise form (11.1.9) under the regularity (11.1.8) is the
separate node `example_11_1_1_pointwise`. -/
theorem example_11_1_1 {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (ψ : SobolevEuclidean (d + 1) 1 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {u : SobolevEuclideanZero (d + 1) 1 2 Ω} (hu : u ∈ obstacleSet Ω ψ) :
    IsMinOn (obstacleEnergy Ω f) (obstacleSet Ω ψ) u ↔
      ∀ v ∈ obstacleSet Ω ψ,
        ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          f x * SobolevMultiIndex.fn ((v - u : SobolevEuclideanZero (d + 1) 1 2 Ω) :
            SobolevEuclidean (d + 1) 1 2 Ω) x
        ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 2 Ω)
            (MultiIndexLE.single i) x
            * SobolevMultiIndex.weakDeriv ((v - u : SobolevEuclideanZero (d + 1) 1 2 Ω) :
              SobolevEuclidean (d + 1) 1 2 Ω) (MultiIndexLE.single i) x := by
  have key := Chapter08.theorem_8_3_3_iff (dirichletBilinForm_isBoundedWith Ω) (by positivity)
    (dirichletBilinForm_isEllipticWith Ω hR hΩ) (dirichletBilinForm_isSymm Ω) (loadZero Ω f)
    (convex_obstacleSet Ω ψ) hu
  have e : ∀ v w : SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletBilinForm Ω v w
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv (w : SobolevEuclidean (d + 1) 1 2 Ω)
            (MultiIndexLE.single i) x := fun v w ↦
    (dirichletBilinForm_apply Ω v w).trans (Elliptic.dirichletForm_apply Ω v w)
  simp only [e, loadZero_apply] at key
  exact key

/-! ### Example 11.1.1: the pointwise complementarity form (11.1.9) -/

section Pointwise

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The variational inequality at `v = u + w`: `ℓ(w) ≤ a(u, w)`; abstract. -/
theorem le_of_forall_sub_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : BilinForm V} {ℓ : StrongDual ℝ V} {K : Set V} {u : V}
    (hvi : ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u)) {w : V} (hw : u + w ∈ K) : ℓ w ≤ a u w := by
  have := hvi (u + w) hw
  rwa [add_sub_cancel_left] at this

/-- Scaling the variational inequality: `ℓ(ε w) ≤ a(u, ε w)` reads `ε ℓ(w) ≤ ε a(u, w)`;
abstract. -/
theorem smul_le_of_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : BilinForm V} {ℓ : StrongDual ℝ V} {u w : V} {ε : ℝ} (h : ℓ (ε • w) ≤ a u (ε • w)) :
    ε * ℓ w ≤ ε * a u w := by
  rwa [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h

end Pointwise

section PointwiseMain

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open Laplacian in
/-- **The test-function step of Example 11.1.1**: if `u ∈ K` solves the variational inequality
(11.1.7) (in the form of Theorem 8.3.3) and `u + ε φ` is admissible for a test function `φ`, then
`ε ∫_Ω f̃ φ ≤ ε ∫_Ω (−Δũ) φ`, by integration by parts
(`dirichletForm_eq_integral_neg_laplacian_mul`). -/
theorem obstacle_testFunction_step (ψ : SobolevEuclidean (d + 1) 1 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {u : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hvi : ∀ v ∈ obstacleSet Ω ψ, loadZero Ω f (v - u) ≤ dirichletBilinForm Ω u (v - u))
    {f' ψ' u' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hf : (f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] f')
    (hψ : SobolevMultiIndex.fn ψ
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ψ')
    (hu' : SobolevMultiIndex.fn (u : SobolevEuclidean (d + 1) 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u')
    (huc : ContDiffOn ℝ 2 u' Ω) (φ : 𝓓(Ω, ℝ)) (ε : ℝ)
    (hε : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      ψ' x ≤ u' x + ε * φ x) :
    ε * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f' x * φ x
      ≤ ε * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), -Δ u' x * φ x := by
  obtain ⟨Uφ, hUφT, hUφ⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  have hUφ0 : Uφ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω := SobolevMultiIndexZero.testFunctions_le hUφT
  have hmem : u + ε • (⟨Uφ, hUφ0⟩ : SobolevEuclideanZero (d + 1) 1 2 Ω) ∈ obstacleSet Ω ψ := by
    rw [mem_obstacleSet_iff]
    have hcoe : ((u + ε • (⟨Uφ, hUφ0⟩ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
        SobolevEuclideanZero (d + 1) 1 2 Ω) : SobolevEuclidean (d + 1) 1 2 Ω)
        = (u : SobolevEuclidean (d + 1) 1 2 Ω) + ε • Uφ := rfl
    rw [hcoe]
    filter_upwards [hε, hψ, hu', SobolevMultiIndex.fn_add (u : SobolevEuclidean (d + 1) 1 2 Ω)
      (ε • Uφ), SobolevMultiIndex.fn_smul ε Uφ, hUφ] with x hx h2 h3 h4 h5 h6
    rw [h2, h4, Pi.add_apply, h5, Pi.smul_apply, h6, h3, smul_eq_mul]
    exact hx
  have h := smul_le_of_le (le_of_forall_sub_le hvi hmem)
  have hℓ : loadZero Ω f (⟨Uφ, hUφ0⟩ : SobolevEuclideanZero (d + 1) 1 2 Ω)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f' x * φ x := by
    rw [loadZero_apply]
    exact integral_congr_ae (hf.mul hUφ)
  have ha : dirichletBilinForm Ω u (⟨Uφ, hUφ0⟩ : SobolevEuclideanZero (d + 1) 1 2 Ω)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), -Δ u' x * φ x :=
    (dirichletBilinForm_apply Ω _ _).trans
      (Elliptic.dirichletForm_eq_integral_neg_laplacian_mul Ω huc hu' hUφ)
  exact ((congrArg (fun z ↦ ε * z) hℓ).symm.trans_le h).trans_eq (congrArg (fun z ↦ ε * z) ha)

open Laplacian in
/-- **Example 11.1.1, the pointwise form (11.1.9)**: under the additional regularity (11.1.8) —
`f`, `ψ` continuous on `Ω` and the solution `u` of the obstacle problem `C²` on `Ω`, read through
representatives `f̃`, `ψ̃`, `ũ` — the minimizer `u` of the energy over
`K = {v ∈ H¹₀(Ω) | v ≥ ψ a.e.}` satisfies at every point of `Ω`

  `ũ − ψ̃ ≥ 0`,  `−Δũ − f̃ ≥ 0`,  `(ũ − ψ̃)(−Δũ − f̃) = 0`.

The book's argument: `v = u + φ` with `0 ≤ φ ∈ C₀^∞(Ω)` in the variational inequality (11.1.7)
and an integration by parts (`dirichletForm_eq_integral_neg_laplacian_mul`) give
`∫_Ω (−Δũ − f̃) φ ≥ 0`, hence `−Δũ − f̃ ≥ 0` by the fundamental lemma in its inequality form
(`nonneg_on_of_forall_integral_mul_testFunction_nonneg`); where `ũ(x₀) > ψ̃(x₀)`, both
`v = u ± δ φ` are admissible for `φ` supported in a neighbourhood `U(x₀)` on which
`ũ > ψ̃ + δ`, so `∫_Ω (−Δũ − f̃) φ = 0` for those `φ` and `−Δũ − f̃ = 0` on `U(x₀)`
(`eqOn_zero_of_forall_integral_mul_testFunction_eq_zero`).  The book's `u ∈ C(Ω̄)` is not
needed for the relations in `Ω`. -/
theorem example_11_1_1_pointwise {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (ψ : SobolevEuclidean (d + 1) 1 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {u : SobolevEuclideanZero (d + 1) 1 2 Ω} (hu : u ∈ obstacleSet Ω ψ)
    (hmin : IsMinOn (obstacleEnergy Ω f) (obstacleSet Ω ψ) u)
    {f' ψ' u' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hf : (f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] f')
    (hfc : ContinuousOn f' Ω)
    (hψ : SobolevMultiIndex.fn ψ
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ψ')
    (hψc : ContinuousOn ψ' Ω)
    (hu' : SobolevMultiIndex.fn (u : SobolevEuclidean (d + 1) 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u')
    (huc : ContDiffOn ℝ 2 u' Ω) :
    ∀ x ∈ Ω, ψ' x ≤ u' x ∧ 0 ≤ -Δ u' x - f' x ∧ (u' x - ψ' x) * (-Δ u' x - f' x) = 0 := by
  have hΩm := Ω.isOpen.measurableSet
  have hu'c : ContinuousOn u' Ω := (huc.of_le (by norm_num) : ContDiffOn ℝ 1 u' Ω).continuousOn
  have hgc : ContinuousOn (fun x ↦ -Δ u' x - f' x) Ω :=
    (Elliptic.continuousOn_laplacian Ω huc).neg.sub hfc
  -- the variational inequality (11.1.7) in the form of Theorem 8.3.3
  have hvi : ∀ v ∈ obstacleSet Ω ψ, loadZero Ω f (v - u) ≤ dirichletBilinForm Ω u (v - u) :=
    (Chapter08.theorem_8_3_3_iff (dirichletBilinForm_isBoundedWith Ω) (by positivity)
      (dirichletBilinForm_isEllipticWith Ω hR hΩ) (dirichletBilinForm_isSymm Ω) (loadZero Ω f)
      (convex_obstacleSet Ω ψ) hu).1 hmin
  -- (i) `ψ̃ ≤ ũ` on `Ω`
  have h1 : ∀ x ∈ Ω, ψ' x ≤ u' x := by
    refine le_on_of_ae_le (μ := volume) Ω.isOpen ?_ hψc hu'c
    filter_upwards [(mem_obstacleSet_iff Ω).1 hu, hψ, hu'] with x hx h2 h3
    rw [← h2, ← h3]
    exact hx
  -- the test-function step: `u + ε φ ∈ K` gives `ε ∫ f̃ φ ≤ ε ∫ (−Δũ) φ`
  have key : ∀ (φ : 𝓓(Ω, ℝ)) (ε : ℝ),
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        ψ' x ≤ u' x + ε * φ x) →
      ε * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f' x * φ x
        ≤ ε * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), -Δ u' x * φ x :=
    fun φ ε hε ↦ obstacle_testFunction_step ψ f hvi hf hψ hu' huc φ ε hε
  -- (ii) `−Δũ − f̃ ≥ 0` on `Ω`
  have hint : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      (-Δ u' x - f' x) * φ x = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), -Δ u' x * φ x)
        - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f' x * φ x := by
    intro φ
    exact (integral_congr_ae (Eventually.of_forall fun x ↦ by ring)).trans
      (integral_sub (integrable_mul_testFunction (Elliptic.continuousOn_laplacian Ω huc).neg φ)
        (integrable_mul_testFunction hfc φ))
  have h2 : ∀ x ∈ Ω, 0 ≤ -Δ u' x - f' x := by
    refine nonneg_on_of_forall_integral_mul_testFunction_nonneg hgc fun φ hφ ↦ ?_
    rw [hint]
    have := key φ 1 (by
      filter_upwards [ae_restrict_mem hΩm] with x hx
      have := h1 x hx
      have := hφ x
      linarith)
    linarith
  -- (iii) complementarity
  refine fun x₀ hx₀ ↦ ⟨h1 x₀ hx₀, h2 x₀ hx₀, ?_⟩
  rcases (h1 x₀ hx₀).lt_or_eq with hlt | heq
  · -- a ball around `x₀` on which `ũ − ψ̃ > δ`
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (u' x₀ - ψ' x₀) / 2 := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hat : ContinuousAt (fun x ↦ u' x - ψ' x) x₀ :=
      (hu'c.sub hψc).continuousAt (Ω.isOpen.mem_nhds hx₀)
    have hev : ∀ᶠ x in 𝓝 x₀, δ < u' x - ψ' x := hat.eventually (lt_mem_nhds (by rw [hδ]; linarith))
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 (hev.and (Ω.isOpen.mem_nhds hx₀))
    have hUΩ : ball x₀ ε₀ ⊆ Ω := fun x hx ↦ (hball hx).2
    -- on that ball `−Δũ − f̃ = 0`
    have hzero : ∀ x ∈ ball x₀ ε₀, -Δ u' x - f' x = 0 := by
      refine eqOn_zero_of_forall_integral_mul_testFunction_eq_zero hgc isOpen_ball hUΩ
        fun φ hφs ↦ ?_
      obtain ⟨C, hC⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x₀)
      obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = δ / (C + 1) := ⟨_, rfl⟩
      have hε : 0 < ε := by rw [hεdef]; positivity
      have hεC : ε * C < δ := by
        rw [hεdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      -- both `u ± ε φ` are admissible
      have hadm : ∀ s : ℝ, |s| ≤ ε →
          ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
            ψ' x ≤ u' x + s * φ x := by
        intro s hs
        filter_upwards [ae_restrict_mem hΩm] with x hx
        by_cases hxU : x ∈ ball x₀ ε₀
        · have h3 := (hball hxU).1
          have h4 : |s * φ x| ≤ ε * C := by
            rw [abs_mul]
            exact mul_le_mul hs ((Real.norm_eq_abs _).symm.trans_le (hC x)) (abs_nonneg _) hε.le
          linarith [neg_abs_le (s * φ x)]
        · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hxU (hφs h)
          rw [hφx, mul_zero, add_zero]
          exact h1 x hx
      have hp := key φ ε (hadm ε (by rw [abs_of_pos hε]))
      have hm := key φ (-ε) (hadm (-ε) (by rw [abs_neg, abs_of_pos hε]))
      rw [hint]
      nlinarith
    exact mul_eq_zero.2 (Or.inr (hzero x₀ (mem_ball_self hε₀)))
  · rw [heq, sub_self, zero_mul]

end PointwiseMain

/-! ### Example 11.1.2: the simplified friction problem -/

section Friction

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω) (𝒯 : B.TraceFamily)

/-- `ℝ^N`, locally. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The `L¹(σ)` norm is bounded by the `L²(σ)` norm on the finite surface measure `σ`:
`∫ |k| dσ ≤ ‖1‖_{L²(σ)} ‖k‖_{L²(σ)}` (Hölder,
`MeasureTheory.integral_norm_rpow_sub_one_mul_norm_le` at `p = 2`). -/
theorem integral_abs_le_mul_norm (k : Lp ℝ 2 B.σ) :
    ∫ x, |k x| ∂B.σ ≤ (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal * ‖k‖ := by
  have h := MeasureTheory.integral_norm_rpow_sub_one_mul_norm_le (p := 2) ENNReal.ofNat_ne_top
    (Lp.memLp k) (memLp_const (μ := B.σ) (1 : ℝ))
  have h2 : ((2 : ℝ≥0∞).toReal - 1) = 1 := by norm_num
  simp only [h2, Real.rpow_one, norm_one, mul_one, Real.norm_eq_abs] at h
  rw [Lp.norm_def, mul_comm]
  exact h

/-- `k ↦ ∫ |k| dσ` is Lipschitz on `L²(σ)`, with constant `‖1‖_{L²(σ)}`. -/
theorem lipschitzWith_integral_abs :
    LipschitzWith (Real.toNNReal (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal)
      (fun k : Lp ℝ 2 B.σ ↦ ∫ x, |k x| ∂B.σ) := by
  refine LipschitzWith.of_dist_le_mul fun k k' ↦ ?_
  have hI : ∀ k : Lp ℝ 2 B.σ, Integrable (fun x ↦ |k x|) B.σ := fun k ↦
    ((Lp.memLp k).integrable one_le_two).abs
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ ENNReal.toReal_nonneg,
    ← integral_sub (hI k) (hI k')]
  calc |∫ x, (|k x| - |k' x|) ∂B.σ| ≤ ∫ x, |(|k x| - |k' x|)| ∂B.σ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, |(k - k') x| ∂B.σ := by
        refine integral_mono_ae ((hI k).sub (hI k')).abs (hI (k - k')) ?_
        filter_upwards [Lp.coeFn_sub k k'] with x hx
        rw [hx, Pi.sub_apply]
        exact abs_abs_sub_abs_le_abs_sub _ _
    _ ≤ _ := integral_abs_le_mul_norm B (k - k')

/-- **The friction functional `j(v) = g ∫_Γ |v| ds`** of Example 11.1.2 on `V = H¹(Ω)`, through
the trace `γ = 𝒯.traceL 2 : H¹(Ω) →L L²(σ)` of the boundary interface
`Numlib/Analysis/Sobolev/Boundary/Data.lean` (instances: `IsContDiffDomain.traceFamily` on a
bounded `C¹` domain, `Triangulation.traceFamily` on a polygon). -/
noncomputable def frictionFunctional (g : ℝ) (v : SobolevEuclidean N 1 2 Ω) : ℝ :=
  g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ

/-- `j(v) = g ∫ |γ v| dσ`. -/
theorem frictionFunctional_apply (g : ℝ) (v : SobolevEuclidean N 1 2 Ω) :
    frictionFunctional B 𝒯 g v = g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ :=
  rfl

/-- The friction functional depends on the trace only. -/
theorem frictionFunctional_eq_of_traceL_eq (g : ℝ) {v w : SobolevEuclidean N 1 2 Ω}
    (h : 𝒯.traceL 2 ENNReal.ofNat_ne_top v = 𝒯.traceL 2 ENNReal.ofNat_ne_top w) :
    frictionFunctional B 𝒯 g v = frictionFunctional B 𝒯 g w := by
  simp only [frictionFunctional, h]

/-- `j(0) = 0`. -/
theorem frictionFunctional_zero (g : ℝ) : frictionFunctional B 𝒯 g 0 = 0 := by
  simp only [frictionFunctional, map_zero]
  rw [integral_congr_ae ((Lp.coeFn_zero ℝ 2 B.σ).mono fun x hx ↦ by rw [hx, Pi.zero_apply,
    abs_zero]), integral_zero, mul_zero]

/-- `j(2u) = 2 j(u)`: the friction functional is positively homogeneous. -/
theorem frictionFunctional_two_smul (g : ℝ) (u : SobolevEuclidean N 1 2 Ω) :
    frictionFunctional B 𝒯 g ((2 : ℝ) • u) = 2 * frictionFunctional B 𝒯 g u := by
  simp only [frictionFunctional, map_smul]
  rw [integral_congr_ae ((Lp.coeFn_smul (2 : ℝ) (𝒯.traceL 2 ENNReal.ofNat_ne_top u)).mono
    fun x hx ↦ by rw [hx, Pi.smul_apply, smul_eq_mul, abs_mul, abs_two]), integral_const_mul]
  ring

/-- `j(u + w) − j(u) ≤ g ∫ |γ w| dσ`: the friction functional is subadditive. -/
theorem frictionFunctional_add_sub_le {g : ℝ} (hg : 0 ≤ g) (u w : SobolevEuclidean N 1 2 Ω) :
    frictionFunctional B 𝒯 g (u + w) - frictionFunctional B 𝒯 g u
      ≤ g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x| ∂B.σ := by
  have hI : ∀ k : Lp ℝ 2 B.σ, Integrable (fun x ↦ |k x|) B.σ := fun k ↦
    ((Lp.memLp k).integrable one_le_two).abs
  simp only [frictionFunctional, map_add]
  rw [← mul_sub, ← integral_sub (hI _) (hI _)]
  refine mul_le_mul_of_nonneg_left (integral_mono_ae ((hI _).sub (hI _)) (hI _) ?_) hg
  filter_upwards [Lp.coeFn_add (𝒯.traceL 2 ENNReal.ofNat_ne_top u)
    (𝒯.traceL 2 ENNReal.ofNat_ne_top w)] with x hx
  rw [hx, Pi.add_apply]
  linarith [abs_add_le ((𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x)
    ((𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x)]

/-- **The friction functional is continuous** on `H¹(Ω)`: `k ↦ ∫ |k| dσ` is Lipschitz on
`L²(σ)` and the trace is bounded. -/
theorem continuous_frictionFunctional (g : ℝ) : Continuous (frictionFunctional B 𝒯 g) :=
  continuous_const.mul
    ((lipschitzWith_integral_abs B).continuous.comp (𝒯.traceL 2 ENNReal.ofNat_ne_top).continuous)

/-- **The friction functional is convex** for `g ≥ 0`: `|·|` is convex and the trace is linear. -/
theorem convexOn_frictionFunctional {g : ℝ} (hg : 0 ≤ g) :
    ConvexOn ℝ univ (frictionFunctional B 𝒯 g) := by
  refine ⟨convex_univ, fun v _ w _ a b ha hb _ ↦ ?_⟩
  have hI : ∀ k : Lp ℝ 2 B.σ, Integrable (fun x ↦ |k x|) B.σ := fun k ↦
    ((Lp.memLp k).integrable one_le_two).abs
  simp only [frictionFunctional, smul_eq_mul]
  have key : ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top (a • v + b • w) : 𝔼 → ℝ) x| ∂B.σ
      ≤ a * (∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ)
        + b * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x| ∂B.σ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hI _).const_mul a)
      ((hI _).const_mul b)]
    refine integral_mono_ae (hI _) (((hI _).const_mul a).add ((hI _).const_mul b)) ?_
    rw [map_add, map_smul, map_smul]
    filter_upwards [Lp.coeFn_add (a • 𝒯.traceL 2 ENNReal.ofNat_ne_top v)
      (b • 𝒯.traceL 2 ENNReal.ofNat_ne_top w), Lp.coeFn_smul a (𝒯.traceL 2 ENNReal.ofNat_ne_top v),
      Lp.coeFn_smul b (𝒯.traceL 2 ENNReal.ofNat_ne_top w)] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    calc |a * _ + b * _| ≤ |a * _| + |b * _| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top (a • v + b • w) : 𝔼 → ℝ) x| ∂B.σ
      ≤ g * (a * (∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ)
        + b * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x| ∂B.σ) :=
        mul_le_mul_of_nonneg_left key hg
    _ = _ := by ring

/-- **The energy (11.1.12)** of the simplified friction problem on `V = H¹(Ω)`,
`E(v) = ∫_Ω (½ (|∇v|² + v²) − f v) + g ∫_Γ |v| ds`: the energy `½ a(v, v) − ℓ(v)` of the form
`a(u, v) = ∫_Ω (∇u·∇v + u v)` (the backbone's `Elliptic.laplaceForm Ω`) and the load
`ℓ(v) = ∫_Ω f v`, plus the friction functional `j`. -/
noncomputable def frictionEnergy (g : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : SobolevEuclidean N 1 2 Ω → ℝ :=
  (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) + frictionFunctional B 𝒯 g

/-- **The energy (11.1.12) is the displayed formula**:
`E(v) = ∫_Ω (½ (∑ᵢ (∂ᵢv)² + v²) − f v) + g ∫ |γ v| dσ`. -/
theorem frictionEnergy_apply (g : ℝ) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (v : SobolevEuclidean N 1 2 Ω) :
    frictionEnergy B 𝒯 g f v
      = (∫ x in (Ω : Set 𝔼), ((1 / 2 : ℝ) * (∑ i, SobolevMultiIndex.weakDeriv v
          (MultiIndexLE.single i) x ^ 2 + SobolevMultiIndex.fn v x ^ 2)
          - f x * SobolevMultiIndex.fn v x))
        + g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ := by
  change (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) v + frictionFunctional B 𝒯 g v = _
  rw [Elliptic.energy_laplace_apply, frictionFunctional_apply]
  congr 1
  have h1 : Integrable (fun x ↦ ∑ i, SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
      + SobolevMultiIndex.fn v x * SobolevMultiIndex.fn v x) (volume.restrict (Ω : Set 𝔼)) :=
    (integrable_finsetSum _ fun i _ ↦ (Lp.memLp (SobolevMultiIndex.weakDeriv v
      (MultiIndexLE.single i))).integrable_mul (Lp.memLp _)).add
      ((Lp.memLp (SobolevMultiIndex.weakDeriv v 0)).integrable_mul
        (Lp.memLp (SobolevMultiIndex.weakDeriv v 0)))
  have h2 : Integrable (fun x ↦ f x * SobolevMultiIndex.fn v x) (volume.restrict (Ω : Set 𝔼)) :=
    (Lp.memLp f).integrable_mul (Lp.memLp (SobolevMultiIndex.weakDeriv v 0))
  rw [← integral_const_mul, ← integral_sub (h1.const_mul _) h2]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [sq]

/-- **The form `a(u, v) = ∫_Ω (∇u·∇v + u v)` of Example 11.1.2 as a bilinear form of §8.3**:
the backbone's `Elliptic.laplaceForm Ω` read through `BilinForm.ofCLM`, so that Theorems 11.2.2
and 11.3.9 apply to the friction problem. -/
noncomputable def frictionBilinForm : BilinForm (SobolevEuclidean N 1 2 Ω) :=
  BilinForm.ofCLM (Elliptic.laplaceForm Ω)

/-- `a(u, v) = Elliptic.laplaceForm Ω u v`. -/
theorem frictionBilinForm_apply (u v : SobolevEuclidean N 1 2 Ω) :
    frictionBilinForm (Ω := Ω) u v = Elliptic.laplaceForm Ω u v := rfl

/-- The form of Example 11.1.2 is bounded with constant `1`
(`Elliptic.laplaceForm_isBoundedWith_one`). -/
theorem frictionBilinForm_isBoundedWith : (frictionBilinForm (Ω := Ω)).IsBoundedWith 1 :=
  fun u v ↦ by
    rw [frictionBilinForm_apply, ← Real.norm_eq_abs]
    exact Elliptic.laplaceForm_isBoundedWith_one Ω u v

/-- The form of Example 11.1.2 is `V`-elliptic with constant `1`: it is the inner product of
`H¹(Ω)` (`Elliptic.laplaceForm_isCoerciveWith_one`). -/
theorem frictionBilinForm_isEllipticWith : (frictionBilinForm (Ω := Ω)).IsEllipticWith 1 :=
  fun v ↦ Elliptic.laplaceForm_isCoerciveWith_one Ω v

/-- The form of Example 11.1.2 is symmetric. -/
theorem frictionBilinForm_isSymm : LinearMap.BilinForm.IsSymm (frictionBilinForm (Ω := Ω)) := by
  unfold frictionBilinForm
  rw [BilinForm.isSymm_ofCLM_iff]
  intro u v
  have h := Elliptic.laplaceForm_isHermitian Ω u v
  rw [conj_trivial] at h
  exact h

/-- **The variational inequality (11.1.13) at one test element `v`, in the book's display and
in the backbone's vocabulary**:
`∫_Ω f (v − u) ≤ ∫_Ω [∇u·∇(v − u) + u (v − u)] + g ∫_Γ (|v| − |u|) ds` is
`ℓ(v − u) ≤ a(u, v − u) + j(v) − j(u)`. -/
theorem friction_ineq_iff (g : ℝ) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u v : SobolevEuclidean N 1 2 Ω) :
    (∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
      ≤ (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv (v - u) (MultiIndexLE.single i) x)
          + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x))
        + g * ∫ x, (|(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x|
          - |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|) ∂B.σ) ↔
      Elliptic.load Ω f (v - u) ≤ Elliptic.laplaceForm Ω u (v - u)
        + frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u := by
  have hI : ∀ k : Lp ℝ 2 B.σ, Integrable (fun x ↦ |k x|) B.σ := fun k ↦
    ((Lp.memLp k).integrable one_le_two).abs
  rw [Elliptic.laplaceForm_apply, Elliptic.load_apply, frictionFunctional_apply,
    frictionFunctional_apply, add_sub_assoc, ← mul_sub, ← integral_sub (hI _) (hI _)]

/-- **Example 11.1.2 (the simplified friction problem)**, the variational inequality (11.1.13):
on `V = H¹(Ω)`, over the boundary interface `B : BoundaryData Ω`, `𝒯 : B.TraceFamily` of
`Numlib/Analysis/Sobolev/Boundary/Data.lean` — the surface measure `σ = B.σ` on `Γ = ∂Ω`, the
trace `γ = 𝒯.traceL 2 : H¹(Ω) →L L²(σ)`; the instances are `IsContDiffDomain.traceFamily` on a
bounded `C¹` domain and `Triangulation.traceFamily` on a polygon without slits — for `g > 0` and
`f ∈ L²(Ω)`, `u` minimizes the energy (11.1.12)
`E(v) = ∫_Ω (½ (|∇v|² + v²) − f v) + g ∫_Γ |v| ds` over `V` (the minimization problem (11.1.12))
if and only if it satisfies

  `∫_Ω [∇u·∇(v − u) + u (v − u)] + g ∫_Γ (|v| − |u|) ds ≥ ∫_Ω f (v − u)`  for every `v ∈ V`.

The book leaves this to Exercise 11.1.2; it is Theorem 11.2.1 (the backbone's
`isMinOn_energy_add_iff`) with `K = V`, the Gâteaux differentiable convex part `½ a(v, v) − ℓ(v)`
of the energy and the convex continuous friction functional `j` (`convexOn_frictionFunctional`,
`continuous_frictionFunctional`). The book's Lipschitz boundary is the `C¹` or polygonal
hypothesis behind the two instances. The pointwise formulation (11.1.14)–(11.1.15) on a bounded
`C¹` domain is `example_11_1_2_pointwise`. -/
theorem example_11_1_2 {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : SobolevEuclidean N 1 2 Ω) :
    IsMinOn (frictionEnergy B 𝒯 g f) univ u ↔
      ∀ v : SobolevEuclidean N 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
          ≤ (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
              * SobolevMultiIndex.weakDeriv (v - u) (MultiIndexLE.single i) x)
              + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x))
            + g * ∫ x, (|(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x|
              - |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|) ∂B.σ := by
  rw [frictionEnergy, isMinOn_energy_add_iff (Elliptic.laplaceForm_isHermitian Ω) zero_le_one
    (Elliptic.laplaceForm_isCoerciveWith_one Ω) (Elliptic.load Ω f) convex_univ
    (convexOn_frictionFunctional B 𝒯 hg.le) (mem_univ u)]
  simp only [_root_.IsVariationalInequalitySolution, mem_univ, true_and, true_implies,
    SesqForm.inner_rieszRep, SesqForm.inner_toOperator]
  exact forall_congr' fun v ↦ (friction_ineq_iff B 𝒯 g f u v).symm

/-! ### Tools for the pointwise form: bump tests on the boundary -/

/-- A function continuous on `∂Ω` is bounded and measurable for the surface measure of a
`BoundaryData`. Helper; belongs beside `BoundaryData.memLp_of_continuousOn` in
`Numlib/Analysis/Sobolev/Boundary/Trace.lean`. -/
theorem memLp_top_of_continuousOn_frontier {h : 𝔼 → ℝ}
    (hc : ContinuousOn h (frontier (Ω : Set 𝔼))) : MemLp h ⊤ B.σ := by
  have hm : AEStronglyMeasurable h B.σ := by
    rw [← Measure.restrict_eq_self_of_ae_mem B.ae_mem_frontier]
    exact hc.aestronglyMeasurable isClosed_frontier.measurableSet
  have hK : IsCompact (frontier (Ω : Set 𝔼)) :=
    B.isBounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact MemLp.of_bound hm C (B.ae_mem_frontier.mono fun x hx ↦ hC x hx)

/-- **A bump test against a function continuous on the boundary**: for a `BoundaryData` whose
surface measure charges every open set meeting `∂Ω` (a bounded `C¹` domain,
`IsContDiffDomain.boundaryMeasure_pos_of_isOpen`), a function `h` continuous on `∂Ω` and a
boundary point `x₀` with `h x₀ > c`, some smooth compactly supported bump `ψ` with `0 ≤ ψ ≤ 1`
satisfies `c ∫ ψ dσ < ∫ h ψ dσ`: a `ContDiffBump` supported in a ball around `x₀` on which
`h > (c + h x₀)/2`, whose integral is positive because the smaller ball has positive measure.
Helper; belongs in `Numlib/Analysis/Sobolev/Boundary/Trace.lean`. -/
theorem exists_bump_lt_integral_mul
    (hpos : ∀ U : Set 𝔼, IsOpen U → (U ∩ frontier (Ω : Set 𝔼)).Nonempty → 0 < B.σ U)
    {h : 𝔼 → ℝ} (hc : ContinuousOn h (frontier (Ω : Set 𝔼))) {x₀ : 𝔼}
    (hx₀ : x₀ ∈ frontier (Ω : Set 𝔼)) {c : ℝ} (hlt : c < h x₀) :
    ∃ ψ : 𝔼 → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧
      c * ∫ x, ψ x ∂B.σ < ∫ x, h x * ψ x ∂B.σ := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (c + h x₀) / 2 := ⟨_, rfl⟩
  have hcm : c < m := by rw [hm]; linarith
  have hmx : m < h x₀ := by rw [hm]; linarith
  -- a ball on which `h > m`, relative to `∂Ω`
  have hev : ∀ᶠ x in 𝓝[frontier (Ω : Set 𝔼)] x₀, m < h x :=
    (hc x₀ hx₀).eventually (lt_mem_nhds hmx)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  -- the bump
  let ψ : ContDiffBump x₀ := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, fun x ↦ ψ.nonneg, fun x ↦ ψ.le_one, ?_⟩
  have hψc : Continuous ψ := ψ.continuous
  have hIψ : Integrable (fun x ↦ ψ x) B.σ := B.integrable_of_continuous hψc
  have hIhψ : Integrable (fun x ↦ h x * ψ x) B.σ :=
    (memLp_top_of_continuousOn_frontier B hc).integrable_mul (B.memLp_of_continuous hψc 1)
  -- `∫ ψ dσ > 0`
  have hpsi : 0 < ∫ x, ψ x ∂B.σ := by
    have h1 : B.σ.real (ball x₀ (r / 2)) ≤ ∫ x, ψ x ∂B.σ := by
      rw [← integral_indicator_one measurableSet_ball]
      refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_ball) hIψ
        fun x ↦ ?_
      by_cases hx : x ∈ ball x₀ (r / 2)
      · rw [indicator_of_mem hx]
        exact (ψ.one_of_mem_closedBall (ball_subset_closedBall hx)).ge
      · rw [indicator_of_notMem hx]
        exact ψ.nonneg
    refine lt_of_lt_of_le ?_ h1
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hpos _ isOpen_ball ⟨x₀, mem_ball_self (by positivity), hx₀⟩).ne'
      (measure_ne_top _ _)
  -- `∫ h ψ ≥ m ∫ ψ`
  have hle : m * ∫ x, ψ x ∂B.σ ≤ ∫ x, h x * ψ x ∂B.σ := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hIψ.const_mul m) hIhψ ?_
    filter_upwards [B.ae_mem_frontier] with x hx
    by_cases hxb : x ∈ ball x₀ r
    · exact mul_le_mul_of_nonneg_right (hball ⟨hxb, hx⟩).le ψ.nonneg
    · rw [ψ.zero_of_le_dist (not_lt.1 fun h' ↦ hxb (mem_ball.2 h')), mul_zero, mul_zero]
  calc c * ∫ x, ψ x ∂B.σ < m * ∫ x, ψ x ∂B.σ := mul_lt_mul_of_pos_right hcm hpsi
    _ ≤ _ := hle

/-- The inner product of two gradients is the sum of the products of the partial derivatives,
`∇u · ∇v = ∑ᵢ ∂ᵢu ∂ᵢv`. Helper; belongs beside `EuclideanSpace.gradient_apply` in
`Numlib/Analysis/Sobolev/Boundary/Divergence.lean`. -/
theorem inner_gradient_eq_sum (u v : 𝔼 → ℝ) (x : 𝔼) :
    ⟪gradient u x, gradient v x⟫_ℝ
      = ∑ i, fderiv ℝ u x (EuclideanSpace.single i 1)
        * fderiv ℝ v x (EuclideanSpace.single i 1) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [EuclideanSpace.gradient_apply, EuclideanSpace.gradient_apply, RCLike.inner_apply,
    conj_trivial, mul_comm]

open Laplacian in
/-- **The form `a(u, W) = ∫_Ω (∇u·∇W + u W)` of a `C²(Ω̄)` function against a smooth test
function, with its boundary term**: for `u ∈ H¹(Ω)` with a representative `ũ ∈ C²(Ω̄)` whose
derivative extends continuously to `Ω̄` as `G` (the boundary values of `∇ũ`), and `W ∈ H¹(Ω)`
with a `C¹` representative `ψ`, `a(u, W) = ∫_Γ G(ν) ψ dσ + ∫_Ω (−Δũ + ũ) ψ`: Green's formula
`BoundaryData.integral_laplacian_mul_add_eq`. -/
theorem laplaceForm_eq_integral_add_of_contDiffOnClosure {u : SobolevEuclidean N 1 2 Ω}
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hũ2 : ContDiffOnClosure ℝ 2 ũ Ω) {G : 𝔼 → 𝔼 →L[ℝ] ℝ}
    (hG : ContinuousOn G (closure (Ω : Set 𝔼))) (hGe : EqOn G (fderiv ℝ ũ) Ω)
    {W : SobolevEuclidean N 1 2 Ω} {ψ : 𝔼 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hW : SobolevMultiIndex.fn W =ᵐ[volume.restrict (Ω : Set 𝔼)] ψ) :
    Elliptic.laplaceForm Ω u W
      = (∫ x, G x (B.ν x) * ψ x ∂B.σ) + ∫ x in (Ω : Set 𝔼), (-Δ ũ x + ũ x) * ψ x := by
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hũ1 : ContDiffOnClosure ℝ 1 ũ Ω := hũ2.of_le (by norm_num)
  have hgreen := B.integral_laplacian_mul_add_eq hũ2 hG hGe hψ.continuous.continuousOn
    (hψ.contDiffOn.contDiffOnClosure hΩo)
  have hdU := fun i ↦ Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hũ1.contDiffOn hũ i
  have hdW := fun i ↦ Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hψ.contDiffOn hW i
  have hI₁ : IntegrableOn (fun x ↦ ⟪gradient ũ x, gradient ψ x⟫_ℝ) (Ω : Set 𝔼) := by
    have hc : ContinuousOn (fun x ↦ ⟪(InnerProductSpace.toDualReal 𝔼).symm (G x),
        gradient ψ x⟫_ℝ) (closure (Ω : Set 𝔼)) :=
      ((InnerProductSpace.toDualReal 𝔼).symm.continuous.comp_continuousOn hG).inner
        (EuclideanSpace.continuous_gradient hψ).continuousOn
    refine (B.integrableOn_of_continuousOn hc).congr_fun (fun x hx ↦ ?_) hΩm
    simp only [gradient_eq_toDualReal_symm, hGe hx]
  have hI₂ : Integrable (fun x ↦ ũ x * ψ x) (volume.restrict (Ω : Set 𝔼)) :=
    ((Lp.memLp (SobolevMultiIndex.weakDeriv u 0)).integrable_mul
      (Lp.memLp (SobolevMultiIndex.weakDeriv W 0))).congr (hũ.mul hW)
  have hI₃ : Integrable (fun x ↦ Δ ũ x * ψ x) (volume.restrict (Ω : Set 𝔼)) := by
    obtain ⟨G₂, hG₂c, hG₂e⟩ := hũ2.exists_continuousOn_fderiv_fderiv
    have hc : ContinuousOn (fun x ↦ (∑ i, G₂ x (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)) * ψ x) (closure (Ω : Set 𝔼)) :=
      (continuousOn_finsetSum _ fun i _ ↦
        (hG₂c.clm_apply continuousOn_const).clm_apply continuousOn_const).mul
        hψ.continuous.continuousOn
    refine (B.integrableOn_of_continuousOn hc).congr_fun (fun x hx ↦ ?_) hΩm
    simp only [EuclideanSpace.laplacian_eq_sum_fderiv_fderiv_single, hG₂e hx]
  have hL : Elliptic.laplaceForm Ω u W
      = (∫ x in (Ω : Set 𝔼), ⟪gradient ũ x, gradient ψ x⟫_ℝ)
        + ∫ x in (Ω : Set 𝔼), ũ x * ψ x := by
    rw [Elliptic.laplaceForm_apply, ← integral_add hI₁ hI₂]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hdU, ae_all_iff.2 hdW, hũ, hW] with x hxU hxW hUx hWx
    simp only [hxU, hxW, hUx, hWx, inner_gradient_eq_sum]
  have hR : ∫ x in (Ω : Set 𝔼), (-Δ ũ x + ũ x) * ψ x
      = (∫ x in (Ω : Set 𝔼), -(Δ ũ x * ψ x)) + ∫ x in (Ω : Set 𝔼), ũ x * ψ x := by
    have hI₃' : Integrable (fun x ↦ -(Δ ũ x * ψ x)) (volume.restrict (Ω : Set 𝔼)) := hI₃.neg
    rw [← integral_add hI₃' hI₂]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    ring
  rw [hL, hR, integral_neg]
  linarith

/-- **The test-function bound of the friction inequality**: if `u` satisfies
`0 ≤ ∫_Γ h γ(v − u) dσ + j(v) − j(u)` for all `v ∈ H¹(Ω)`, then `|∫_Γ h ψ dσ| ≤ g ∫_Γ ψ dσ`
for every smooth compactly supported `ψ ≥ 0` — test with `v = u ± W`, `W` the element with
function `ψ`, whose trace is `ψ` (`TraceFamily.traceL_ae_eq`), and use the subadditivity of
`j`. -/
theorem abs_integral_mul_le_of_forall_le {g : ℝ} (hg : 0 ≤ g) {h : 𝔼 → ℝ}
    {u : SobolevEuclidean N 1 2 Ω}
    (hvi : ∀ v : SobolevEuclidean N 1 2 Ω,
      0 ≤ (∫ x, h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
        + frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u)
    {ψ : 𝔼 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    |∫ x, h x * ψ x ∂B.σ| ≤ g * ∫ x, ψ x ∂B.σ := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨W, hW⟩ : ∃ W : SobolevEuclidean N 1 2 Ω,
      SobolevMultiIndex.fn W =ᵐ[volume.restrict (Ω : Set 𝔼)] ψ :=
    hψ1.exists_sobolevMultiIndex_of_hasCompactSupport' hψc
  have hγW := 𝒯.traceL_ae_eq 2 ENNReal.ofNat_ne_top W ψ hW hψ.continuous.continuousOn
  have hγneg : 𝒯.traceL 2 ENNReal.ofNat_ne_top (-W) = -𝒯.traceL 2 ENNReal.ofNat_ne_top W :=
    (𝒯.traceL 2 ENNReal.ofNat_ne_top).map_neg W
  have hIψ : ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top W : 𝔼 → ℝ) x| ∂B.σ = ∫ x, ψ x ∂B.σ := by
    refine integral_congr_ae ?_
    filter_upwards [hγW] with x hx
    rw [hx, abs_of_nonneg (hψ0 x)]
  have hIψ' : ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top (-W) : 𝔼 → ℝ) x| ∂B.σ
      = ∫ x, ψ x ∂B.σ := by
    refine integral_congr_ae ?_
    rw [hγneg]
    filter_upwards [Lp.coeFn_neg (𝒯.traceL 2 ENNReal.ofNat_ne_top W), hγW] with x hx hx'
    rw [hx, Pi.neg_apply, hx', abs_neg, abs_of_nonneg (hψ0 x)]
  have hhψ : ∫ x, h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top W : 𝔼 → ℝ) x ∂B.σ
      = ∫ x, h x * ψ x ∂B.σ := by
    refine integral_congr_ae ?_
    filter_upwards [hγW] with x hx
    rw [hx]
  have hhψ' : ∫ x, h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (-W) : 𝔼 → ℝ) x ∂B.σ
      = -∫ x, h x * ψ x ∂B.σ := by
    have e : (fun x ↦ h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (-W) : 𝔼 → ℝ) x) =ᵐ[B.σ]
        fun x ↦ -(h x * ψ x) := by
      rw [hγneg]
      filter_upwards [Lp.coeFn_neg (𝒯.traceL 2 ENNReal.ofNat_ne_top W), hγW] with x hx hx'
      rw [hx, Pi.neg_apply, hx', mul_neg]
    exact (integral_congr_ae e).trans (integral_neg _)
  have e1 : u + W - u = W := add_sub_cancel_left u W
  have e2 : u - W - u = -W := sub_sub_cancel_left u W
  have e3 : u + -W = u - W := (sub_eq_add_neg u W).symm
  have hp := hvi (u + W)
  have hm := hvi (u - W)
  simp only [e1, hhψ] at hp
  simp only [e2, hhψ'] at hm
  have hjp := frictionFunctional_add_sub_le B 𝒯 hg u W
  have hjm := frictionFunctional_add_sub_le B 𝒯 hg u (-W)
  rw [hIψ] at hjp
  rw [hIψ'] at hjm
  simp only [e3] at hjm
  rw [abs_le]
  constructor <;> linarith

/-- **`|h| ≤ g` on `Γ` from the friction inequality**, for `h` continuous on `Γ` and a surface
measure charging every open set meeting `Γ`: where `|h x₀| > g` a bump test
(`exists_bump_lt_integral_mul`) contradicts `abs_integral_mul_le_of_forall_le`. -/
theorem abs_le_of_forall_le
    (hpos : ∀ U : Set 𝔼, IsOpen U → (U ∩ frontier (Ω : Set 𝔼)).Nonempty → 0 < B.σ U)
    {g : ℝ} (hg : 0 ≤ g) {h : 𝔼 → ℝ} (hc : ContinuousOn h (frontier (Ω : Set 𝔼)))
    {u : SobolevEuclidean N 1 2 Ω}
    (hvi : ∀ v : SobolevEuclidean N 1 2 Ω,
      0 ≤ (∫ x, h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
        + frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u) :
    ∀ x ∈ frontier (Ω : Set 𝔼), |h x| ≤ g := by
  intro x₀ hx₀
  rw [abs_le]
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨ψ, hψ, hψc, hψ0, -, hψi⟩ := exists_bump_lt_integral_mul B hpos hc.neg hx₀ (c := g)
      (by simp only [Pi.neg_apply]; linarith)
    have := abs_integral_mul_le_of_forall_le B 𝒯 hg hvi hψ hψc hψ0
    simp only [Pi.neg_apply, neg_mul, integral_neg] at hψi
    rw [abs_le] at this
    linarith [this.1]
  · by_contra hlt
    push Not at hlt
    obtain ⟨ψ, hψ, hψc, hψ0, -, hψi⟩ := exists_bump_lt_integral_mul B hpos hc hx₀ (c := g) hlt
    have := abs_integral_mul_le_of_forall_le B 𝒯 hg hvi hψ hψc hψ0
    rw [abs_le] at this
    linarith [this.2]

/-- **The complementarity clause `h ũ + g |ũ| = 0` on `Γ`** from the friction inequality, for
`u` with trace `ũ` continuous on `Γ`, `h` continuous on `Γ` with `|h| ≤ g` there, and a surface
measure charging every open set meeting `Γ`: `v = 0` and `v = 2u` give
`∫_Γ (h ũ + g |ũ|) dσ = 0`, the integrand is nonnegative (`|h| ≤ g`) and continuous, so it
vanishes where a bump test would otherwise see it. -/
theorem mul_add_abs_eq_zero_of_forall_le
    (hpos : ∀ U : Set 𝔼, IsOpen U → (U ∩ frontier (Ω : Set 𝔼)).Nonempty → 0 < B.σ U)
    {g : ℝ} {h : 𝔼 → ℝ} (hc : ContinuousOn h (frontier (Ω : Set 𝔼)))
    (hle : ∀ x ∈ frontier (Ω : Set 𝔼), |h x| ≤ g) {u : SobolevEuclidean N 1 2 Ω}
    {ũ : 𝔼 → ℝ} (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼)))
    (hγu : (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) =ᵐ[B.σ] ũ)
    (hvi : ∀ v : SobolevEuclidean N 1 2 Ω,
      0 ≤ (∫ x, h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
        + frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u) :
    ∀ x ∈ frontier (Ω : Set 𝔼), h x * ũ x + g * |ũ x| = 0 := by
  have hh : MemLp h 2 B.σ := (memLp_top_of_continuousOn_frontier B hc).mono_exponent le_top
  -- the integral of `h ũ + g |ũ|` vanishes: test with `v = 0` and `v = 2u`
  have hzero : ∫ x, (h x * ũ x + g * |ũ x|) ∂B.σ = 0 := by
    have h0 := hvi 0
    have h2 := hvi ((2 : ℝ) • u)
    have e0 : (0 : SobolevEuclidean N 1 2 Ω) - u = -u := zero_sub u
    have e2 : (2 : ℝ) • u - u = u := by rw [two_smul, add_sub_cancel_right]
    simp only [e0, frictionFunctional_zero] at h0
    simp only [e2, frictionFunctional_two_smul] at h2
    have hγneg : 𝒯.traceL 2 ENNReal.ofNat_ne_top (-u) = -𝒯.traceL 2 ENNReal.ofNat_ne_top u :=
      (𝒯.traceL 2 ENNReal.ofNat_ne_top).map_neg u
    have hIhu : Integrable (fun x ↦ h x * ũ x) B.σ :=
      hh.integrable_mul (B.memLp_of_continuousOn hũc 2)
    have hIu : Integrable (fun x ↦ |ũ x|) B.σ :=
      ((B.memLp_of_continuousOn hũc 1).integrable le_rfl).abs
    have e1 : ∫ x, h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (-u) : 𝔼 → ℝ) x ∂B.σ
        = -∫ x, h x * ũ x ∂B.σ := by
      have e : (fun x ↦ h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (-u) : 𝔼 → ℝ) x) =ᵐ[B.σ]
          fun x ↦ -(h x * ũ x) := by
        rw [hγneg]
        filter_upwards [Lp.coeFn_neg (𝒯.traceL 2 ENNReal.ofNat_ne_top u), hγu] with x hx hx'
        rw [hx, Pi.neg_apply, hx', mul_neg]
      exact (integral_congr_ae e).trans (integral_neg _)
    have e2' : ∫ x, h x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x ∂B.σ
        = ∫ x, h x * ũ x ∂B.σ := by
      refine integral_congr_ae ?_
      filter_upwards [hγu] with x hx
      rw [hx]
    have e3 : frictionFunctional B 𝒯 g u = g * ∫ x, |ũ x| ∂B.σ := by
      rw [frictionFunctional_apply]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hγu] with x hx
      rw [hx]
    rw [e1] at h0
    rw [e2'] at h2
    rw [integral_add hIhu (hIu.const_mul g), integral_const_mul, ← e3]
    linarith
  -- the integrand is nonnegative and continuous on `Γ`
  have hk : ContinuousOn (fun x ↦ h x * ũ x + g * |ũ x|) (frontier (Ω : Set 𝔼)) :=
    (hc.mul (hũc.mono frontier_subset_closure)).add
      (continuousOn_const.mul (hũc.mono frontier_subset_closure).abs)
  have hk0 : ∀ x ∈ frontier (Ω : Set 𝔼), 0 ≤ h x * ũ x + g * |ũ x| := fun x hx ↦ by
    have h1 := hle x hx
    have h2 : -(|h x| * |ũ x|) ≤ h x * ũ x := by rw [← abs_mul]; exact neg_abs_le _
    nlinarith [abs_nonneg (ũ x)]
  intro x₀ hx₀
  by_contra hne
  have hgt : 0 < h x₀ * ũ x₀ + g * |ũ x₀| := lt_of_le_of_ne (hk0 x₀ hx₀) (Ne.symm hne)
  obtain ⟨ψ, hψ, -, -, hψ1, hψi⟩ := exists_bump_lt_integral_mul B hpos hk hx₀ (c := 0) hgt
  rw [zero_mul] at hψi
  have hIk : Integrable (fun x ↦ h x * ũ x + g * |ũ x|) B.σ :=
    (memLp_top_of_continuousOn_frontier B hk).integrable le_top
  have hIkψ : Integrable (fun x ↦ (h x * ũ x + g * |ũ x|) * ψ x) B.σ :=
    (memLp_top_of_continuousOn_frontier B hk).integrable_mul
      (B.memLp_of_continuous hψ.continuous 1)
  have hmono : ∫ x, (h x * ũ x + g * |ũ x|) * ψ x ∂B.σ
      ≤ ∫ x, (h x * ũ x + g * |ũ x|) ∂B.σ := by
    refine integral_mono_ae hIkψ hIk ?_
    filter_upwards [B.ae_mem_frontier] with x hx
    exact mul_le_of_le_one_right (hk0 x hx) (hψ1 x)
  linarith

end Friction

/-! ### Example 11.1.2: the pointwise form (11.1.14)–(11.1.15) on a bounded `C¹` domain -/

section FrictionPointwise

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- `ℝ^{d+1}`, locally. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

open Laplacian in
/-- **The key identity behind (11.1.15)**: for a `C²(Ω̄)` representative `ũ` of `u ∈ H¹(Ω)`
satisfying `−Δũ + ũ = f` a.e. on `Ω`, with `∇ũ` extending continuously to `Ω̄` as `G`,
`a(u, W) − ℓ(W) = ∫_Γ (∂ũ/∂ν) γW dσ` for every `W ∈ H¹(Ω)`, on a bounded `C¹` domain:
Green's formula (`laplaceForm_eq_integral_add_of_contDiffOnClosure`) on the smooth restrictions,
both sides being continuous in `W` and the smooth restrictions dense
(`IsContDiffDomain.hasSmoothDensity`). -/
theorem laplaceForm_sub_load_eq_integral (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u : SobolevEuclidean (d + 1) 1 2 Ω}
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hũ2 : ContDiffOnClosure ℝ 2 ũ Ω) {G : 𝔼 → 𝔼 →L[ℝ] ℝ}
    (hG : ContinuousOn G (closure (Ω : Set 𝔼))) (hGe : EqOn G (fderiv ℝ ũ) Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    (hint : (fun x ↦ -Δ ũ x + ũ x) =ᵐ[volume.restrict (Ω : Set 𝔼)] f)
    (W : SobolevEuclidean (d + 1) 1 2 Ω) :
    Elliptic.laplaceForm Ω u W - Elliptic.load Ω f W
      = ∫ x, G x (hΩ.outwardNormal hb x)
          * ((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top W : 𝔼 → ℝ) x
          ∂(hΩ.boundaryData hb).σ := by
  have hc : ContinuousOn (fun x ↦ G x (hΩ.outwardNormal hb x)) (frontier (Ω : Set 𝔼)) :=
    (hG.mono frontier_subset_closure).clm_apply (hΩ.continuousOn_outwardNormal hb)
  have hhL : MemLp (fun x ↦ G x (hΩ.outwardNormal hb x)) 2 (hΩ.boundaryData hb).σ :=
    (memLp_top_of_continuousOn_frontier (hΩ.boundaryData hb) hc).mono_exponent le_top
  have hfL : ∀ W : SobolevEuclidean (d + 1) 1 2 Ω, Elliptic.load Ω f W
      = ∫ x in (Ω : Set 𝔼), (-Δ ũ x + ũ x) * SobolevMultiIndex.fn W x := fun W ↦ by
    rw [Elliptic.load_apply]
    exact integral_congr_ae (hint.symm.mul (EventuallyEq.refl _ _))
  -- the right side is continuous in `W`
  have hcont : Continuous fun W : SobolevEuclidean (d + 1) 1 2 Ω ↦
      ∫ x, G x (hΩ.outwardNormal hb x)
        * ((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top W : 𝔼 → ℝ) x
        ∂(hΩ.boundaryData hb).σ := by
    have e : (fun W : SobolevEuclidean (d + 1) 1 2 Ω ↦
        ∫ x, G x (hΩ.outwardNormal hb x)
          * ((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top W : 𝔼 → ℝ) x
          ∂(hΩ.boundaryData hb).σ)
        = fun W ↦ ⟪hhL.toLp _, (hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top W⟫_ℝ := by
      funext W
      rw [L2.inner_eq_integral_mul]
      exact integral_congr_ae (hhL.coeFn_toLp.symm.mul (EventuallyEq.refl _ _))
    rw [e]
    exact (innerSL ℝ (hhL.toLp _)).continuous.comp
      ((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top).continuous
  -- the identity on the smooth restrictions
  have hsm : ∀ W ∈ SobolevEuclidean.smoothRestrictions (d + 1) 2 Ω,
      Elliptic.laplaceForm Ω u W - Elliptic.load Ω f W
        = ∫ x, G x (hΩ.outwardNormal hb x)
            * ((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top W : 𝔼 → ℝ) x
            ∂(hΩ.boundaryData hb).σ := by
    intro W hWm
    obtain ⟨ψ, hψ, -, hW⟩ := SobolevEuclidean.exists_contDiff_of_mem_smoothRestrictions hWm
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have e1 := laplaceForm_eq_integral_add_of_contDiffOnClosure (hΩ.boundaryData hb) hũ hũ2 hG
      hGe hψ1 hW
    have e2 : Elliptic.load Ω f W = ∫ x in (Ω : Set 𝔼), (-Δ ũ x + ũ x) * ψ x := by
      rw [hfL W]
      exact integral_congr_ae ((EventuallyEq.refl _ _).mul hW)
    have e3 : ∫ x, G x ((hΩ.boundaryData hb).ν x) * ψ x ∂(hΩ.boundaryData hb).σ
        = ∫ x, G x (hΩ.outwardNormal hb x)
            * ((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top W : 𝔼 → ℝ) x
            ∂(hΩ.boundaryData hb).σ := by
      refine integral_congr_ae ?_
      filter_upwards [(hΩ.traceFamily hb).traceL_ae_eq 2 ENNReal.ofNat_ne_top W ψ hW
        hψ.continuous.continuousOn] with x hx
      simp only [hx, IsContDiffDomain.boundaryData_ν]
    simp only [e1, e2, e3, add_sub_cancel_right]
  exact congrFun (Continuous.ext_on
    (hΩ.hasSmoothDensity (p := 2) ENNReal.ofNat_ne_top).dense_smoothRestrictions
    ((Elliptic.laplaceForm Ω u).continuous.sub (Elliptic.load Ω f).continuous) hcont hsm) W

open Laplacian in
/-- **Example 11.1.2, the pointwise form (11.1.14)–(11.1.15) of a smooth solution**, on a
bounded `C¹` domain `Ω ⊆ ℝ^{d+1}` (the book's Lipschitz boundary is restated as `C¹`, the
hypothesis under which the backbone's surface measure `σ = hΩ.boundaryMeasure hb`, outward
normal `ν = hΩ.outwardNormal hb` — defined at every point of `Γ` and continuous there — and
trace exist): for `g > 0`, `f ∈ L²(Ω)`, let `u ∈ H¹(Ω)` solve the variational inequality
(11.1.13) and have a representative `ũ ∈ C²(Ω̄)` continuous on `Ω̄` whose derivative extends
continuously to `Ω̄` as `G` (the boundary values of `∇ũ`, so that `∂ũ/∂ν = G(ν)` is meaningful
on `Γ`; Exercise 11.1.3's "smooth solution"). Then

  `−Δũ + ũ = f`  a.e. in `Ω`  (11.1.14),

and at every point of `Γ`

  `|∂ũ/∂ν| ≤ g`  and  `(∂ũ/∂ν) ũ + g |ũ| = 0`  (11.1.15).

The book's argument: `v = u ± φ` with `φ ∈ C_c^∞(Ω)` (whose trace vanishes,
`TraceFamily.traceL_eq_zero_of_mem_zero`) gives the weak equation, hence (11.1.14)
(`Elliptic.laplacian_ae_eq_of_forall_testFunction`); Green's formula turns (11.1.13) into
`∫_Γ (∂ũ/∂ν)(γv − γu) dσ + g ∫_Γ (|γv| − |γu|) dσ ≥ 0` for all `v ∈ H¹(Ω)`
(`laplaceForm_sub_load_eq_integral`); with `v = u ± W`, `W` the element of a smooth compactly
supported `ψ ≥ 0`, `|∫_Γ (∂ũ/∂ν) ψ dσ| ≤ g ∫_Γ ψ dσ`, and since `∂ũ/∂ν` is continuous on `Γ` and
every open set meeting `Γ` has positive surface measure, `|∂ũ/∂ν| ≤ g` everywhere on `Γ`
(`abs_le_of_forall_le`); `v = 0` and `v = 2u` give `∫_Γ ((∂ũ/∂ν) ũ + g |ũ|) dσ = 0`, whose
integrand is nonnegative and continuous on `Γ`, hence zero (`mul_add_abs_eq_zero_of_forall_le`).
The book's "at those boundary points where the outward normal vector is defined" is every point
of `Γ` on a `C¹` domain. -/
theorem example_11_1_2_pointwise (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {g : ℝ} (hg : 0 < g)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {u : SobolevEuclidean (d + 1) 1 2 Ω}
    (hu : ∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
      ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
        ≤ (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
            * SobolevMultiIndex.weakDeriv (v - u) (MultiIndexLE.single i) x)
            + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x))
          + g * ∫ x, (|((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x|
            - |((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|)
            ∂(hΩ.boundaryMeasure hb))
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (hũ2 : ContDiffOnClosure ℝ 2 ũ Ω)
    {G : 𝔼 → 𝔼 →L[ℝ] ℝ} (hG : ContinuousOn G (closure (Ω : Set 𝔼)))
    (hGe : EqOn G (fderiv ℝ ũ) Ω) :
    (fun x ↦ -Δ ũ x + ũ x) =ᵐ[volume.restrict (Ω : Set 𝔼)] f ∧
      ∀ x ∈ frontier (Ω : Set 𝔼), |G x (hΩ.outwardNormal hb x)| ≤ g ∧
        G x (hΩ.outwardNormal hb x) * ũ x + g * |ũ x| = 0 := by
  -- the inequality in the backbone's vocabulary
  replace hu : ∀ v, Elliptic.load Ω f (v - u) ≤ Elliptic.laplaceForm Ω u (v - u)
      + frictionFunctional (hΩ.boundaryData hb) (hΩ.traceFamily hb) g v
      - frictionFunctional (hΩ.boundaryData hb) (hΩ.traceFamily hb) g u := fun v ↦
    (friction_ineq_iff (hΩ.boundaryData hb) (hΩ.traceFamily hb) g f u v).1 (hu v)
  have hpos : ∀ U : Set 𝔼, IsOpen U → (U ∩ frontier (Ω : Set 𝔼)).Nonempty →
      0 < (hΩ.boundaryData hb).σ U := fun U hU hne ↦ hΩ.boundaryMeasure_pos_of_isOpen hb hU hne
  have hc : ContinuousOn (fun x ↦ G x (hΩ.outwardNormal hb x)) (frontier (Ω : Set 𝔼)) :=
    (hG.mono frontier_subset_closure).clm_apply (hΩ.continuousOn_outwardNormal hb)
  -- (11.1.14): the interior equation
  have hUw : ∀ V ∈ SobolevMultiIndex.testFunctions ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume,
      Elliptic.laplaceForm Ω u V = Elliptic.load Ω f V := by
    intro V hV
    have hV0 : (hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top V = 0 :=
      (hΩ.traceFamily hb).traceL_eq_zero_of_mem_zero _ (SobolevMultiIndexZero.testFunctions_le hV)
    have hjV₁ : frictionFunctional (hΩ.boundaryData hb) (hΩ.traceFamily hb) g (u + V)
        = frictionFunctional (hΩ.boundaryData hb) (hΩ.traceFamily hb) g u := by
      refine frictionFunctional_eq_of_traceL_eq _ _ g ?_
      rw [map_add, hV0, add_zero]
    have hjV₂ : frictionFunctional (hΩ.boundaryData hb) (hΩ.traceFamily hb) g (u - V)
        = frictionFunctional (hΩ.boundaryData hb) (hΩ.traceFamily hb) g u := by
      refine frictionFunctional_eq_of_traceL_eq _ _ g ?_
      rw [map_sub, hV0, sub_zero]
    have e1 : u + V - u = V := add_sub_cancel_left u V
    have e2 : u - V - u = -V := sub_sub_cancel_left u V
    have h1 := hu (u + V)
    have h2 := hu (u - V)
    simp only [e1, hjV₁] at h1
    simp only [e2, hjV₂] at h2
    have h3 : Elliptic.load Ω f (-V) = -Elliptic.load Ω f V := map_neg _ _
    have h4 : Elliptic.laplaceForm Ω u (-V) = -Elliptic.laplaceForm Ω u V := map_neg _ _
    linarith
  have hint := Elliptic.laplacian_ae_eq_of_forall_testFunction Ω hUw hũ2.contDiffOn hũ
  refine ⟨hint, ?_⟩
  -- the variational inequality in boundary form
  have hvi : ∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
      0 ≤ (∫ x, G x (hΩ.outwardNormal hb x)
          * ((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x
          ∂(hΩ.boundaryData hb).σ)
        + frictionFunctional (hΩ.boundaryData hb) (hΩ.traceFamily hb) g v
        - frictionFunctional (hΩ.boundaryData hb) (hΩ.traceFamily hb) g u := fun v ↦ by
    have h1 := hu v
    have h2 := laplaceForm_sub_load_eq_integral hΩ hb hũ hũ2 hG hGe hint (v - u)
    linarith
  have hle := abs_le_of_forall_le (hΩ.boundaryData hb) (hΩ.traceFamily hb) hpos hg.le hc hvi
  have hγu : ((hΩ.traceFamily hb).traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ)
      =ᵐ[(hΩ.boundaryData hb).σ] ũ := (hΩ.traceFamily hb).traceL_ae_eq 2 _ u ũ hũ hũc
  have hzero := mul_add_abs_eq_zero_of_forall_le (hΩ.boundaryData hb) (hΩ.traceFamily hb) hpos hc
    hle hũc hγu hvi
  exact fun x hx ↦ ⟨hle x hx, hzero x hx⟩

end FrictionPointwise

end AtkinsonHan.Chapter11
