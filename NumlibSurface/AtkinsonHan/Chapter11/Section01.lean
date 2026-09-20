import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Numlib.Analysis.PDE.Elliptic.Dirichlet
import NumlibSurface.AtkinsonHan.Chapter08.Section02
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson–Han §11.1: from variational equations to variational inequalities

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §11.1.

The section motivates the chapter with two problems: the obstacle problem (Example 11.1.1), a
minimization of the Dirichlet energy over a convex set that is not a subspace, and the simplified
friction problem (Example 11.1.2), a minimization over a space of an energy with a
non-differentiable boundary term.  The obstacle problem is here; the friction problem, whose
functional `g ∫_Γ |v| ds` needs the trace of an `H¹(Ω)` function and the surface measure on `Γ`,
is not (see `example_11_1_2` in the plan).

## The obstacle problem

The setting is a bounded open `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}`, the space `V = H¹₀(Ω)` of the backbone,
`SobolevEuclideanZero (d + 1) 1 2 Ω`, an obstacle `ψ ∈ H¹(Ω) = SobolevEuclidean (d + 1) 1 2 Ω`
and a load `f ∈ L²(Ω)`:

* `dirichletBilinForm Ω` is the bilinear form `a(u, v) = ∫_Ω ∇u · ∇v` of (11.1.3) on `H¹₀(Ω)`,
  the operator `modelOperator Ω` of Example 8.2.6 (`Chapter08/Section02`) read as a form of §8.3:
  bounded with `M = 1`, symmetric, and `V`-elliptic with `α = (1 + (2R)²)⁻¹` by Poincaré's
  inequality (`dirichletBilinForm_isEllipticWith`);
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

## Deviations from the book

* The book's "`ψ ≤ 0` on `Γ`", a statement about the trace, enters as the hypothesis that the
  positive part `max (ψ, 0)` is the function of an element of `H¹₀(Ω)` — exactly what the book
  uses it for (`max (0, ψ) ∈ K`, Example 11.2.3).  When `ψ` has a representative continuous on
  `closure Ω` that is `≤ 0` on `∂Ω`, this hypothesis follows from the backbone's Theorem 9.17
  (`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`) applied to `max (ψ, 0)`,
  which lies in `H¹(Ω)` by `MemSobolevMultiIndex.posPart`.
* The book's Lipschitz boundary is not needed; `Ω` is any bounded open set.
* The pointwise complementarity form (11.1.9) under the regularity (11.1.8) is
  `example_11_1_1_pointwise`, stated through representatives `f̃`, `ψ̃` continuous on `Ω` and
  `ũ` of class `C²` on `Ω`; the book's `u ∈ C(Ω̄)` is not needed for the relations in `Ω`.  The
  two forms of the fundamental lemma of the calculus of variations it runs on — the inequality
  form `nonneg_on_of_forall_integral_mul_testFunction_nonneg` and the localized form
  `eqOn_zero_of_forall_integral_mul_testFunction_eq_zero` — and the integration by parts
  `dirichletForm_eq_integral_neg_laplacian_mul` are proved here and belong in the backbone.
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
noncomputable abbrev dirichletBilinForm : BilinForm (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  BilinForm.ofCLM (Chapter08.modelOperator Ω)

/-- The form (11.1.3) is bounded with constant `1` (`Elliptic.dirichletForm_isBoundedWith`). -/
theorem dirichletBilinForm_isBoundedWith : (dirichletBilinForm Ω).IsBoundedWith 1 := fun u v ↦ by
  rw [BilinForm.ofCLM_apply, Chapter08.modelOperator_apply, one_mul, ← Real.norm_eq_abs]
  have h := Elliptic.dirichletForm_isBoundedWith Ω u v
  rwa [one_mul] at h

/-- The form (11.1.3) is `V`-elliptic on `H¹₀(Ω)` of a bounded `Ω ⊆ B(0, R)`, with constant
`(1 + (2R)²)⁻¹`: Poincaré's inequality (`Elliptic.dirichletForm_restrict_isCoerciveWith`). -/
theorem dirichletBilinForm_isEllipticWith {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) :
    (dirichletBilinForm Ω).IsEllipticWith (1 + (2 * R) ^ 2)⁻¹ := fun v ↦ by
  rw [BilinForm.ofCLM_apply, Chapter08.modelOperator_apply]
  exact Elliptic.dirichletForm_restrict_isCoerciveWith Ω hR hΩ v

/-- The form (11.1.3) is symmetric. -/
theorem dirichletBilinForm_isSymm : LinearMap.BilinForm.IsSymm (dirichletBilinForm Ω) := by
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
    rw [BilinForm.ofCLM_apply, Chapter08.modelOperator_apply, Elliptic.dirichletForm_apply]
    simp only [sq]
  rw [integral_sub ((integrable_sum_sq_weakDeriv Ω _).const_mul _) (integrable_mul_fn Ω f _),
    integral_const_mul]
  change (1 / 2 : ℝ) * dirichletBilinForm Ω v v - loadZero Ω f v = _
  rw [h1, loadZero_apply]

/-! ### The admissible set `K` -/

/-- In `L^p(μ)`, a lower bound of two functions is a lower bound of their convex combinations:
`h ≤ f`, `h ≤ g`, `a, b ≥ 0`, `a + b = 1` give `h ≤ a • f + b • g`.  Belongs beside
`MeasureTheory.Lp.coeFn_le` in `Mathlib/MeasureTheory/Function/LpOrder.lean`. -/
theorem _root_.MeasureTheory.Lp.le_smul_add_smul_of_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} {h f g : Lp ℝ p μ} (hf : h ≤ f) (hg : h ≤ g) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) : h ≤ a • f + b • g := by
  rw [← Lp.coeFn_le] at hf hg ⊢
  filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g, hf, hg]
    with x h1 h2 h3 hfx hgx
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  calc h x = a * h x + b * h x := by rw [← add_mul, hab, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hfx ha) (mul_le_mul_of_nonneg_left hgx hb)

/-- In `L^p(μ)` the order interval `Ici c = {f | c ≤ f}` is convex.  Belongs beside
`MeasureTheory.Lp.coeFn_le` in `Mathlib/MeasureTheory/Function/LpOrder.lean`. -/
theorem _root_.MeasureTheory.Lp.convex_Ici {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (c : Lp ℝ p μ) : Convex ℝ (Ici c) :=
  fun _ hf _ hg _ _ ha hb hab ↦ Lp.le_smul_add_smul_of_le hf hg ha hb hab

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
    Elliptic.dirichletForm_apply Ω v w
  simp only [e, loadZero_apply] at key
  exact key

/-! ### Example 11.1.1: the pointwise complementarity form (11.1.9) -/

section Pointwise

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- Two functions continuous on an open set that are ordered almost everywhere are ordered
everywhere on it. -/
theorem le_on_of_ae_le {g h : EuclideanSpace ℝ (Fin N) → ℝ}
    (hle : g ≤ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] h)
    (hg : ContinuousOn g Ω) (hh : ContinuousOn h Ω) : ∀ x ∈ Ω, g x ≤ h x := by
  have hmin : (fun x ↦ min (g x) (h x))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g :=
    hle.mono fun x hx ↦ min_eq_left hx
  have heq := Measure.eqOn_open_of_ae_eq hmin Ω.isOpen (ContinuousOn.inf hg hh) hg
  intro x hx
  have := heq hx
  exact min_eq_left_iff.1 this

/-- A function continuous on `Ω` times a test function is integrable on `Ω`. -/
theorem integrable_mul_testFunction {g : EuclideanSpace ℝ (Fin N) → ℝ} (hg : ContinuousOn g Ω)
    (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ g x * φ x) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  have := (hg.locallyIntegrableOn (μ := volume) Ω.isOpen.measurableSet)
    |>.integrable_smul_left_of_tsupport_subset φ.contDiff.continuous φ.hasCompactSupport
      φ.tsupport_subset
  simp only [smul_eq_mul] at this
  exact this.integrableOn.congr_fun (fun x _ ↦ mul_comm _ _) Ω.isOpen.measurableSet

/-- **The fundamental lemma of the calculus of variations, inequality form**: a function `g`
continuous on an open `Ω ⊆ ℝ^N` with `∫_Ω g φ ≥ 0` for every nonnegative test function `φ` is
nonnegative on `Ω`.  Where `g(x₀) < 0`, a bump at `x₀` supported in `{g < g(x₀)/2}` gives a
negative integral. -/
theorem nonneg_on_of_forall_integral_mul_testFunction_nonneg {g : EuclideanSpace ℝ (Fin N) → ℝ}
    (hg : ContinuousOn g Ω)
    (h : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x * φ x) :
    ∀ x ∈ Ω, 0 ≤ g x := by
  intro x₀ hx₀
  by_contra hneg
  push Not at hneg
  -- a ball around `x₀` inside `Ω` on which `g < g x₀ / 2`
  have hat : ContinuousAt g x₀ := hg.continuousAt (Ω.isOpen.mem_nhds hx₀)
  have hev : ∀ᶠ x in 𝓝 x₀, g x < g x₀ / 2 := hat.eventually (gt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hev.and (Ω.isOpen.mem_nhds hx₀))
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hclosed : closedBall x₀ r ⊆ ball x₀ ε := closedBall_subset_ball (by linarith)
  -- the bump
  let β : ContDiffBump x₀ := ⟨r / 2, r, by positivity, by linarith⟩
  let φ : 𝓓(Ω, ℝ) := ⟨β, β.contDiff, β.hasCompactSupport, by
    rw [β.tsupport_eq]
    exact fun x hx ↦ (hball (hclosed hx)).2⟩
  have hφ : ∀ x, φ x = β x := fun _ ↦ rfl
  have hφ0 : ∀ x, 0 ≤ φ x := fun x ↦ β.nonneg
  have hint := integrable_mul_testFunction hg φ
  -- the integrand is nonpositive everywhere and negative on the inner ball
  have hnonneg : 0 ≤ fun x ↦ -(g x * φ x) := by
    intro x
    simp only [Pi.zero_apply]
    by_cases hx : x ∈ ball x₀ ε
    · have := (hball hx).1
      rw [neg_nonneg]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hφ0 x)
    · have hφx : φ x = 0 := by
        rw [hφ]
        exact β.zero_of_le_dist (by
          rw [mem_ball] at hx
          push Not at hx
          linarith)
      rw [hφx, mul_zero, neg_zero]
  have hsupp : ball x₀ (r / 2) ⊆ Function.support fun x ↦ -(g x * φ x) := by
    intro x hx
    have h1 : φ x = 1 := by
      rw [hφ]
      exact β.one_of_mem_closedBall (ball_subset_closedBall hx)
    have h2 : g x < g x₀ / 2 := (hball (ball_subset_ball (by linarith) hx)).1
    simp only [Function.mem_support, h1, mul_one, neg_ne_zero]
    exact (by linarith : g x < 0).ne
  have hpos : 0 < (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      (Function.support fun x ↦ -(g x * φ x)) := by
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    have hsub : ball x₀ (r / 2) ∩ (Ω : Set (EuclideanSpace ℝ (Fin N))) = ball x₀ (r / 2) :=
      inter_eq_left.2 fun x hx ↦ (hball (ball_subset_ball (by linarith) hx)).2
    rw [Measure.restrict_apply' Ω.isOpen.measurableSet, hsub]
    exact measure_ball_pos _ _ (by positivity)
  have hlt := (integral_pos_iff_support_of_nonneg hnonneg hint.neg).2 hpos
  rw [integral_neg] at hlt
  linarith [h φ hφ0]

/-- **The fundamental lemma on an open subset**: a function `g` continuous on `Ω` with
`∫_Ω g φ = 0` for every test function supported in an open `U ⊆ Ω` vanishes on `U`
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` and continuity). -/
theorem eqOn_zero_of_forall_integral_mul_testFunction_eq_zero {g : EuclideanSpace ℝ (Fin N) → ℝ}
    (hg : ContinuousOn g Ω) {U : Set (EuclideanSpace ℝ (Fin N))} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω)
    (h : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U →
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x * φ x = 0) :
    ∀ x ∈ U, g x = 0 := by
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    ((hg.mono hUΩ).locallyIntegrableOn hU.measurableSet) fun ψ hψ hψc hψs ↦ by
    let φ : 𝓓(Ω, ℝ) := ⟨ψ, hψ, hψc, hψs.trans hUΩ⟩
    have := h φ hψs
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hUΩ (hψs h)), zero_smul]]
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [smul_eq_mul]
      rw [mul_comm]
      rfl)
  have hae : g =ᵐ[volume.restrict U] 0 := (ae_restrict_iff' hU.measurableSet).2 key
  exact Measure.eqOn_open_of_ae_eq hae hU (hg.mono hUΩ) continuousOn_const

open Laplacian in
/-- **Integration by parts against a test function**: for `U ∈ H¹(Ω)` whose function is `C²` on
`Ω` and `V ∈ H¹(Ω)` whose function is a test function `φ`, `∫_Ω ∇U · ∇V = ∫_Ω (−Δu) φ`.  The
Dirichlet form is the form of `−Δ + 1` minus the `L²` product
(`Elliptic.laplaceForm_eq_integral_of_contDiffOn`); belongs beside it in
`Numlib/Analysis/PDE/Elliptic/Dirichlet.lean`. -/
theorem dirichletForm_eq_integral_neg_laplacian_mul {u : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) {U : SobolevEuclidean N 1 2 Ω}
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    {V : SobolevEuclidean N 1 2 Ω} {φ : 𝓓(Ω, ℝ)}
    (hV : SobolevMultiIndex.fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) :
    Elliptic.dirichletForm Ω U V
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), -Δ u x * φ x := by
  have h1 := Elliptic.laplaceForm_eq_integral_of_contDiffOn Ω hu hU hV
  have h2 := Elliptic.laplaceForm_apply_eq_dirichletForm_add_weakDeriv Ω U V
  have h3 : ⟪SobolevMultiIndex.weakDeriv U 0, SobolevMultiIndex.weakDeriv V 0⟫_ℝ
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * φ x := by
    rw [L2.inner_eq_integral_mul]
    exact integral_congr_ae (hU.mul hV)
  have hI1 : Integrable (fun x ↦ -Δ u x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    integrable_mul_testFunction (Elliptic.continuousOn_laplacian Ω hu).neg φ
  have hI2 : Integrable (fun x ↦ u x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    integrable_mul_testFunction (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn φ
  have e : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * φ x
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), -Δ u x * φ x)
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * φ x := by
    rw [← integral_add hI1 hI2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  linarith

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
    dirichletForm_eq_integral_neg_laplacian_mul huc hu' hUφ
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
    refine le_on_of_ae_le ?_ hψc hu'c
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

end AtkinsonHan.Chapter11
