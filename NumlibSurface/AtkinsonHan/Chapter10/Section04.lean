import Numlib.Analysis.Calculus.CurvilinearLaplacian
import Numlib.Variational.Galerkin
import Numlib.FiniteElement.Triangle
import NumlibSurface.AtkinsonHan.Chapter09.Section01
import NumlibSurface.AtkinsonHan.Chapter10.Section03

/-!
# Atkinson–Han §10.4: convergence and error estimates

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.4.

The section applies the abstract theory of Chapter 9 (Lax–Milgram, Céa's inequality) and the
interpolation estimates of §10.3 to the finite element method for a second-order elliptic
problem on a polygon: Theorem 10.4.1 (convergence and the error estimate (10.4.4)), Example
10.4.2 (the Dirichlet problem for the Poisson equation), the Aubin–Nitsche lemma (Theorem
10.4.3) and Corollary 10.4.4.

The book states Theorem 10.4.3 for `V ⊆ H¹(Ω)` and `H = L²(Ω)`; the surface states it for a real
inner product space `V`, a real inner product space `H`, and a continuous linear `ι : V →L[ℝ] H`
standing for the embedding, which is the whole of what the proof uses.  The supremum over the data
`g ∈ H` and the infimum over the finite element space are kept, since they are the book's statement
(10.4.5); both are junk-free because the quantities involved are nonnegative and bounded, and the
boundedness comes from the Lax–Milgram bound `norm_le_of_dualProblem` on the dual solution.

Theorem 10.4.1 and Example 10.4.2 are stated on the triangulation scaffold of
`Numlib/Geometry/Triangulation.lean` and `Numlib/Analysis/Sobolev/Triangulation.lean`: a regular
family of triangulations `𝒯 : ι → Triangulation Ω` (Definition 10.3.6, `IsRegularFamily`), a
finite element given by reference nodes and shape functions, its global interpolant
`Triangulation.globalInterp`, and the finite element spaces `Triangulation.polySpace` (`X_h ⊆ H¹`)
and `Triangulation.polySpaceZero` (`V_h ⊆ H¹₀`, the continuous piecewise polynomials vanishing on
`∂Ω`). The membership `V_h ⊆ H¹₀(Ω)` needs no trace theorem: a continuous `H¹` function vanishing
on `∂Ω` lies in `H¹₀(Ω)` on any open set (Brezis's Theorem 9.17, (i) ⇒ (ii)). What a polygon
contributes is that `∂Ω` is a union of element edges (`Triangulation.FrontierSubsetEdges`, a
hypothesis), so that an interpolant vanishing at the boundary nodes vanishes on `∂Ω`.

## Main results

* `theorem_10_4_1` — the error estimate (10.4.4), `‖u − u_h‖_V ≤ c h^k |u|_{k+1,Ω}`, for a
  subspace `V ⊆ H¹(Ω)` with a bounded `V`-elliptic form and Galerkin solutions on subspaces
  `V_h ⊆ V` containing the interpolant `Π_h u`: Céa's inequality with `v_h = Π_h u` and Theorem
  10.3.9 at `m = 1`; `theorem_10_4_1_tendsto` — the convergence `‖u − u_h‖_V → 0` under the
  density of `H^{k+1}(Ω) ∩ C(Ω̄)` in `V` with interpolants in the `V_h`.
* `example_10_4_2` — the Dirichlet problem for the Poisson equation with the `ℙ_k` Lagrange
  element: the weak problem on `H¹₀(Ω)` and its discretization on `V_h` each have a unique
  solution, and `‖u − u_h‖_{1,Ω} ≤ c h^k ‖u‖_{k+1,Ω}`; `poissonForm`, `poissonLoad` are the form
  and the load of the problem.

Theorem 10.4.1 and the error estimate of Example 10.4.2 are restatements of the backbone's
`Numlib/FiniteElement/Triangle.lean` (`FiniteElement.norm_sub_le_of_isGalerkinSolution`,
`FiniteElement.tendsto_norm_sub_of_isGalerkinSolution`,
`FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm`), stated there with the backbone's
`SesqForm` and `IsGalerkinSolution`; the book's `BilinForm` and `GalerkinProblem` are bridged
through `BilinForm.toCLM` (`BilinForm.isBoundedWith_toCLM`,
`BilinForm.isEllipticWith_iff_isCoerciveWith`).
* `DualProblem` — the dual (adjoint) problem (10.4.4) `a(v, φ_g) = (g, ι v)_H`.
* `norm_le_of_dualProblem` — its Lax–Milgram stability estimate `‖φ_g‖ ≤ (‖ι‖/c₀) ‖g‖`, which is
  what makes the supremum in (10.4.5) finite.
* `theorem_10_4_3` — the Aubin–Nitsche lemma (10.4.5).
* `corollary_10_4_4_abstract` — Corollary 10.4.4 with its regularity hypothesis made abstract.
* `exercise_10_4_5_polar` and `exercise_10_4_5_spherical` — Exercise 10.4.5, the Laplacian in
  polar coordinates on `ℝ²` and in spherical coordinates on `ℝ³`.

## Deviations from the book

Theorem 10.4.1's constant `c` depends on the family of triangulations through an upper bound
`H` on its mesh parameters (as in Corollary 10.3.7 and Theorem 10.3.9) and is independent of the
solution `u`; the convergence half takes the density of smooth functions in `V` as a hypothesis
(`theorem_10_4_1_tendsto`), the book's argument, since for `V = H¹(Ω)` it is Theorem 7.3.2 on an
extension domain and a polygon is not yet known to be one (every triangle is,
`isSobolevExtensionDomainAll_referenceTriangle`), while for `V = H¹₀(Ω)` it is the definition.
In Example 10.4.2 the regularity `u ∈ H^{k+1}(Ω)` is read, as in Theorem 10.3.9, on a
representative continuous up to the boundary, and the boundary condition `u = 0` on `Γ` on that
representative: on a `C¹` domain it would follow from `u ∈ H¹₀(Ω)` (Theorem 9.17, (ii) ⇒ (i)), on
a polygon it is a hypothesis. The domain is assumed bounded, `Ω ⊆ B(0, R)`, for Poincaré's
inequality (Example 8.3.5), with `R` entering the ellipticity constant.

## Not formalized here

Corollary 10.4.4 in its stated form, whose hypothesis (10.4.9) is an `H²` elliptic regularity
bound, and (10.4.11): the regularity of the Dirichlet problem on a convex polygon is
`notes/frontier.md` blocker 18 (`Elliptic.regularity_dirichlet` proves it on `C²` domains). The
abstract half of Corollary 10.4.4, in which the approximation power of the dual solutions is a
hypothesis rather than a consequence of regularity, is `corollary_10_4_4_abstract`.

Exercises 10.4.1–4.4 and 10.4.6 all name a domain.

The rest of the chapter is *not* out of scope, and the sections that hold it say what they hold:
`Chapter10.Section01` (the §10.1 algebra), `Chapter10.Section02` (Lemma 10.2.2, the nodal bases,
Proposition 10.2.1, Example 10.2.3, the `ℙ_k` Lagrange element on the principal lattice) and
`Chapter10.Section03` (Theorems 10.3.1, 10.3.3, 10.3.4, 10.3.5, 10.3.9, Corollary 10.3.7, Example
10.3.2, Definition 10.3.6, Example 10.3.8).
-/

open scoped Laplacian

namespace AtkinsonHan

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

/-- The dual problem (10.4.4) for the datum `g ∈ H`: `φ ∈ V` with `a(v, φ) = (g, ι v)_H` for every
`v ∈ V`.  It is the variational problem for the adjoint form, so on a `V`-elliptic `a` it is
uniquely solvable by Lax–Milgram (Theorem 8.3.4) applied to `a(·, ·)ᵀ`. -/
def DualProblem (a : BilinForm V) (ι : V →L[ℝ] H) (g : H) (φ : V) : Prop :=
  ∀ v : V, a v φ = inner ℝ (ι v) g

namespace Chapter10

variable {a : BilinForm V} {ℓ : StrongDual ℝ V} {M c₀ δ : ℝ} {Vh : Submodule ℝ V} {u uh : V}

/-- The infimum over a subspace is bounded below by `0`. -/
private theorem bddBelow_norm_sub (w : V) (K : Submodule ℝ V) :
    BddBelow (Set.range fun v : K => ‖w - (v : V)‖) :=
  ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩

/-- Lax–Milgram stability for the dual problem (10.4.4): a solution `φ_g` of the dual problem for a
`V`-elliptic form satisfies `‖φ_g‖ ≤ (‖ι‖/c₀) ‖g‖`.  This is what bounds the supremum in
(10.4.5). -/
theorem norm_le_of_dualProblem (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) (ι : V →L[ℝ] H) {g : H}
    {φ : V} (hφ : DualProblem a ι g φ) : ‖φ‖ ≤ ‖ι‖ / c₀ * ‖g‖ := by
  have hkey : c₀ * ‖φ‖ ^ 2 ≤ ‖ι‖ * ‖φ‖ * ‖g‖ := by
    refine (ha φ).trans ?_
    rw [hφ φ]
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (ι.le_opNorm φ) (norm_nonneg g))
  rcases eq_or_lt_of_le (norm_nonneg φ) with h0 | h0
  · rw [← h0]
    positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    nlinarith [hkey, h0]

/-- The supremum in (10.4.5) is finite: the dual solutions are approximated from `V_h` at least as
well as by `0`, and their norms are bounded by `(‖ι‖/c₀) ‖g‖`. -/
private theorem bddAbove_dualRatio (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) (ι : V →L[ℝ] H)
    (Vh : Submodule ℝ V) {φ : H → V} (hφ : ∀ g, DualProblem a ι g (φ g)) :
    BddAbove (Set.range fun g : {g : H // g ≠ 0} =>
      (⨅ vh : Vh, ‖φ (g : H) - (vh : V)‖) / ‖(g : H)‖) := by
  refine ⟨‖ι‖ / c₀, Set.forall_mem_range.2 fun g => ?_⟩
  have hg : (0 : ℝ) < ‖(g : H)‖ := norm_pos_iff.mpr g.2
  have hzero : (⨅ vh : Vh, ‖φ (g : H) - (vh : V)‖) ≤ ‖φ (g : H)‖ := by
    refine (ciInf_le (bddBelow_norm_sub _ _) (⟨0, Vh.zero_mem⟩ : Vh)).trans_eq ?_
    simp
  rw [div_le_iff₀ hg]
  exact hzero.trans (norm_le_of_dualProblem hc₀ ha ι (hφ (g : H)))

/-- **Theorem 10.4.3**, the Aubin–Nitsche lemma, (10.4.5).  For a bounded, `V`-elliptic form `a`,
`u` the solution of (10.4.1), `u_h` the Galerkin solution on `V_h ⊆ V`, and `φ_g` a solution of the
dual problem (10.4.4) for each datum `g ∈ H`,

  `‖ι (u − u_h)‖_H ≤ M ‖u − u_h‖_V · sup_{g ≠ 0} (1/‖g‖_H) inf_{v_h ∈ V_h} ‖φ_g − v_h‖_V`.

The duality argument itself is the backbone's `norm_map_sq_le_of_dual`; ellipticity enters only to
make the supremum finite (`bddAbove_dualRatio`). -/
theorem theorem_10_4_3 (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (ι : V →L[ℝ] H) (hu : ∀ v, a u v = ℓ v) (huh : GalerkinProblem a ℓ Vh uh) {φ : H → V}
    (hφ : ∀ g, DualProblem a ι g (φ g)) :
    ‖ι (u - uh)‖ ≤ M * ‖u - uh‖ *
      ⨆ g : {g : H // g ≠ 0}, (⨅ vh : Vh, ‖φ (g : H) - (vh : V)‖) / ‖(g : H)‖ := by
  set e := u - uh with he
  set S := ⨆ g : {g : H // g ≠ 0}, (⨅ vh : Vh, ‖φ (g : H) - (vh : V)‖) / ‖(g : H)‖ with hS
  have hbdd := bddAbove_dualRatio hc₀ ha ι Vh hφ
  have hS0 : 0 ≤ S := by
    refine Real.iSup_nonneg fun g => ?_
    exact div_nonneg (Real.iInf_nonneg fun _ => norm_nonneg _) (norm_nonneg _)
  have hMe : 0 ≤ M * ‖e‖ := by
    rcases eq_or_lt_of_le (norm_nonneg e) with h | h
    · simp [← h]
    · nlinarith [abs_nonneg (a e e), hM e e]
  have horth : ∀ v ∈ Vh, a e v = 0 := fun v hv => Chapter09.galerkin_orthogonality hM hu huh hv
  rcases eq_or_lt_of_le (norm_nonneg (ι e)) with h0 | h0
  · rw [← h0]
    positivity
  -- The pointwise duality bound, for every `v_h ∈ V_h`.
  have hpt : ∀ vh : Vh, ‖ι e‖ ^ 2 ≤ M * ‖e‖ * ‖φ (ι e) - (vh : V)‖ := fun vh =>
    norm_map_sq_le_of_dual (BilinForm.isBoundedWith_toCLM hM) ι horth (hφ (ι e)) vh.2
  have hMe0 : 0 < M * ‖e‖ := by
    rcases eq_or_lt_of_le hMe with h | h
    · exfalso
      have hz := hpt ⟨0, Vh.zero_mem⟩
      rw [← h, zero_mul] at hz
      nlinarith [h0]
    · exact h
  -- Take the infimum on the right.
  have hinf : ‖ι e‖ ^ 2 ≤ M * ‖e‖ * ⨅ vh : Vh, ‖φ (ι e) - (vh : V)‖ := by
    rw [← div_le_iff₀' hMe0]
    refine le_ciInf fun vh => ?_
    rw [div_le_iff₀' hMe0]
    exact hpt vh
  -- and bound that infimum by `S ‖ι e‖`, which is the definition of the supremum.
  have hratio : (⨅ vh : Vh, ‖φ (ι e) - (vh : V)‖) / ‖ι e‖ ≤ S :=
    le_ciSup hbdd (⟨ι e, norm_pos_iff.mp h0⟩ : {g : H // g ≠ 0})
  rw [div_le_iff₀ h0] at hratio
  nlinarith [hinf, hratio, hMe0, h0]

/-- **Corollary 10.4.4**, with its regularity hypothesis made abstract: if the dual solutions can
be approximated from `V_h` to within `δ ‖g‖_H`, then

  `‖ι (u − u_h)‖_H ≤ M δ ‖u − u_h‖_V`.

In the book `δ = c h` follows from the `H²` regularity bound (10.4.9) together with the
interpolation error estimate, neither of which is available here.  The approximation hypothesis is
stated with `Metric.infDist`, the form the backbone's `norm_map_le_of_dual_approx` takes it in;
`AtkinsonHan.Chapter09.iInf_norm_sub_eq_infDist` identifies it with the book's
`inf_{v_h ∈ V_h} ‖φ_g − v_h‖_V`. -/
theorem corollary_10_4_4_abstract (hM : a.IsBoundedWith M) (hδ : 0 ≤ δ) (ι : V →L[ℝ] H)
    (hu : ∀ v, a u v = ℓ v) (huh : GalerkinProblem a ℓ Vh uh)
    (hdual : ∀ g : H, ∃ φ : V, DualProblem a ι g φ ∧
      Metric.infDist φ (Vh : Set V) ≤ δ * ‖g‖) :
    ‖ι (u - uh)‖ ≤ M * δ * ‖u - uh‖ :=
  norm_map_le_of_dual_approx (BilinForm.isBoundedWith_toCLM hM) hδ ι
    (fun _ hv => Chapter09.galerkin_orthogonality hM hu huh hv) hdual


/-! ### Exercise 10.4.5: the Laplacian in polar and in spherical coordinates

The exercise is the chain rule on a `C²` function, not a Sobolev statement.  The plane and
three-space are `EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`, and `Δ` is Mathlib's
`InnerProductSpace.laplacian`; the identities themselves are
`Curvilinear.laplacian_eq_polar` and `Curvilinear.laplacian_eq_spherical` of the backbone,
specialized to the standard orthonormal basis.

The book writes the two identities as identities of operators.  Here they are stated pointwise, at
one point of the domain, with the coordinate derivatives written as derivatives of the composition
of `f` with the coordinate curve through that point — which is what "`∂/∂r`" means. -/

/-- The point of `ℝ²` with polar coordinates `(r, θ)`: `x₁ = r cos θ` and `x₂ = r sin θ`. -/
noncomputable def polarPt (r θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[r * Real.cos θ, r * Real.sin θ]

/-- The book's polar point is the backbone's `Curvilinear.polarPoint` in the standard frame. -/
theorem polarPt_eq (r θ : ℝ) :
    polarPt r θ = Curvilinear.polarPoint (EuclideanSpace.basisFun (Fin 2) ℝ) r θ := by
  ext i
  fin_cases i <;> simp [polarPt, Curvilinear.polarPoint, EuclideanSpace.basisFun_apply]

/-- **Exercise 10.4.5** in `ℝ²`: in polar coordinates `x₁ = r cos θ`, `x₂ = r sin θ` the Laplacian
takes the form

  `Δ = ∂²/∂r² + r⁻¹ ∂/∂r + r⁻² ∂²/∂θ²`. -/
theorem exercise_10_4_5_polar {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ 2 f)
    {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    Δ f (polarPt r θ)
      = deriv (deriv fun s : ℝ => f (polarPt s θ)) r
        + r⁻¹ * deriv (fun s : ℝ => f (polarPt s θ)) r
        + (r ^ 2)⁻¹ * deriv (deriv fun ψ : ℝ => f (polarPt r ψ)) θ := by
  simp only [polarPt_eq]
  simpa using Curvilinear.laplacian_eq_polar _ hf hr θ

/-- The point of `ℝ³` with spherical coordinates `(r, θ, φ)`: `x₁ = r cos θ sin φ`,
`x₂ = r sin θ sin φ` and `x₃ = r cos φ`. -/
noncomputable def sphericalPt (r θ φ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[r * Real.cos θ * Real.sin φ, r * Real.sin θ * Real.sin φ, r * Real.cos φ]

/-- The book's spherical point is the backbone's `Curvilinear.sphericalPoint` in the standard
frame. -/
theorem sphericalPt_eq (r θ φ : ℝ) :
    sphericalPt r θ φ = Curvilinear.sphericalPoint (EuclideanSpace.basisFun (Fin 3) ℝ) r θ φ := by
  ext i
  fin_cases i <;> simp [sphericalPt, Curvilinear.sphericalPoint, EuclideanSpace.basisFun_apply]

/-- **Exercise 10.4.5** in `ℝ³`: in spherical coordinates `x₁ = r cos θ sin φ`,
`x₂ = r sin θ sin φ`, `x₃ = r cos φ` the Laplacian takes the form

  `Δ = ∂²/∂r² + (2/r) ∂/∂r + r⁻² ((sin φ)⁻² ∂²/∂θ² + cot φ ∂/∂φ + ∂²/∂φ²)`. -/
theorem exercise_10_4_5_spherical {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ 2 f)
    {r φ : ℝ} (hr : r ≠ 0) (hφ : Real.sin φ ≠ 0) (θ : ℝ) :
    Δ f (sphericalPt r θ φ)
      = deriv (deriv fun s : ℝ => f (sphericalPt s θ φ)) r
        + (2 / r) * deriv (fun s : ℝ => f (sphericalPt s θ φ)) r
        + (r ^ 2)⁻¹ * ((Real.sin φ ^ 2)⁻¹ * deriv (deriv fun ψ : ℝ => f (sphericalPt r ψ φ)) θ
            + (Real.cos φ / Real.sin φ) * deriv (fun χ : ℝ => f (sphericalPt r θ χ)) φ
            + deriv (deriv fun χ : ℝ => f (sphericalPt r θ χ)) φ) := by
  simp only [sphericalPt_eq]
  simpa using Curvilinear.laplacian_eq_spherical _ hf hr hφ θ


/-! ### Theorem 10.4.1: convergence and error estimate of the finite element method -/

section Theorem1041

open Filter MeasureTheory Set TopologicalSpace EuclideanSpace Topology
open scoped ENNReal

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)
/-- **Theorem 10.4.1**, the error estimate (10.4.4). Let `V ⊆ H¹(Ω)` be a subspace carrying a
bounded, `V`-elliptic bilinear form `a` (the assumptions of the Lax–Milgram lemma), let `{𝒯_h}`
be a regular family of triangulations of `Ω` with mesh parameters at most `H`, and let the
finite element be the reference triangle with nodes `x̂ᵢ ∈ K̂̄`, `C¹` shape functions and the
polynomial invariance `ℙ_k(K̂) ⊆ X̂`, `k ≥ 1`, conforming on every `𝒯_h` — the affine-equivalent
finite element spaces of piecewise polynomials of degree at most `k`. Then there is a constant
`c` such that for every solution `u ∈ V` of (10.4.1) and every family of Galerkin solutions
`u_h ∈ V_h` of (10.4.2) on subspaces `V_h ⊆ V` containing the interpolants `Π_h u`, if
`u ∈ H^{k+1}(Ω)` (read on its representative `ũ`, continuous up to the boundary as in Theorem
10.3.9) then

  `‖u − u_h‖_V ≤ c h^k |u|_{k+1,Ω}`.

The proof is the book's: Céa's inequality (10.4.3) with `v_h = Π_h u`
(`Chapter09.proposition_9_1_3_le`), then the interpolation estimate (10.3.13) at `m = 1`
(`theorem_10_3_9`), with the norm of `V ⊆ H¹(Ω)` compared to the tensor norm `‖·‖_{1,Ω}` of §10.3 by
`FiniteElement.exists_norm_le_sobolevNorm`; it is the backbone's
`FiniteElement.norm_sub_le_of_isGalerkinSolution` for the form `a.toCLM`. The book's "`V_h` is the
finite element space" enters only through `Π_h u ∈ V_h`, which for `V = H¹(Ω)` is automatic
(`V_h = X_h`, the space `Triangulation.polySpace`) and for `V = H¹₀(Ω)` is
`LagrangeElement.exists_mem_polySpaceZero_globalInterp` (Example 10.4.2); the convergence half of
the theorem is `theorem_10_4_1_tendsto`. -/
theorem theorem_10_4_1 {k : ℕ} (hk : 1 ≤ k) {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat)
    {V : Submodule ℝ (SobolevEuclidean 2 1 2 Ω)} {a : BilinForm V} {M c₀ : ℝ}
    (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (ℓ : StrongDual ℝ V) (u : V), (∀ v, a u v = ℓ v) →
      ∀ (Vh : ι → Submodule ℝ V) (uh : ι → V), (∀ i, GalerkinProblem a ℓ (Vh i) (uh i)) →
      ∀ ũ : 𝔼₂ → ℝ,
        SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ →
        MemSobolev ũ (k + 1) 2 Ω volume → ContinuousOn ũ (closure (Ω : Set 𝔼₂)) →
        (∀ i, ∃ w ∈ Vh i, SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω)
          =ᵐ[volume.restrict (Ω : Set 𝔼₂)] (𝒯 i).globalInterp xhat φhat ũ) →
        ∀ i, ‖u - uh i‖
          ≤ c * (𝒯 i).meshSize ^ k * (sobolevSeminorm ũ (k + 1) 2 Ω volume).toReal :=
  FiniteElement.norm_sub_le_of_isGalerkinSolution hk xhat φhat hx hφ hP hreg hH hconf
    (BilinForm.isBoundedWith_toCLM hM) hc₀ ((BilinForm.isEllipticWith_iff_isCoerciveWith hM).1 ha)

/-- **Theorem 10.4.1**, the convergence half: under the assumptions of `theorem_10_4_1`, if the
solution `u ∈ V` can be approximated in `V` by functions in `H^{k+1}(Ω) ∩ C(Ω̄)` whose
interpolants lie in the `V_h` ("smooth functions are dense in `V`", the book's argument), then
the finite element method converges: `‖u − u_h‖_V → 0` as `h → 0` along the family. For
`u ∈ H¹₀(Ω)` the approximants are the test functions, dense by definition; for `V = H¹(Ω)` on
an extension domain they are the `C^∞(Ω̄)` functions of `Chapter07.theorem_7_3_2` (a polygon is
not yet known to be an extension domain, though every triangle is,
`isSobolevExtensionDomainAll_referenceTriangle`). The abstract convergence statement for a
monotone sequence of subspaces with dense union is `Chapter09.corollary_9_1_4`; the family
here is indexed by an arbitrary filter, so the `ε`-argument is redone. -/
theorem theorem_10_4_1_tendsto {k : ℕ} (hk : 1 ≤ k) {I : ℕ} (xhat : Fin I → 𝔼₂)
    (φhat : Fin I → 𝔼₂ → ℝ) (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat)
    {V : Submodule ℝ (SobolevEuclidean 2 1 2 Ω)} {a : BilinForm V} {M c₀ : ℝ}
    (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) {ℓ : StrongDual ℝ V}
    {u : V} (hu : ∀ v, a u v = ℓ v) {Vh : ι → Submodule ℝ V} {uh : ι → V}
    (huh : ∀ i, GalerkinProblem a ℓ (Vh i) (uh i))
    (hdense : ∀ ε > 0, ∃ (w : V) (w' : 𝔼₂ → ℝ), ‖u - w‖ < ε ∧
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] w' ∧
      MemSobolev w' (k + 1) 2 Ω volume ∧ ContinuousOn w' (closure (Ω : Set 𝔼₂)) ∧
      ∀ i, ∃ wh ∈ Vh i, SobolevMultiIndex.fn (wh : SobolevEuclidean 2 1 2 Ω)
        =ᵐ[volume.restrict (Ω : Set 𝔼₂)] (𝒯 i).globalInterp xhat φhat w') :
    Tendsto (fun i ↦ ‖u - uh i‖) l (𝓝 0) :=
  FiniteElement.tendsto_norm_sub_of_isGalerkinSolution hk xhat φhat hx hφ hP hreg hH hconf
    (BilinForm.isBoundedWith_toCLM hM) hc₀ ((BilinForm.isEllipticWith_iff_isCoerciveWith hM).1 ha)
    (ℓ := ℓ) hu huh hdense

end Theorem1041

/-! ### Example 10.4.2: the Dirichlet problem for the Poisson equation

The concrete instance of Theorem 10.4.1 on `V = H¹₀(Ω)` with the `ℙ_k` Lagrange element on the
principal lattice (the backbone's `LagrangeElement.node`, `LagrangeElement.shape`) and the finite
element space `V_h = {v_h ∈ C(Ω̄) : v_h|_K ∈ ℙ_k(K), v_h|_∂Ω = 0}` (`Triangulation.polySpaceZero`).
The two ingredients the book leaves implicit are the backbone's: the lattice element is edge
unisolvent (`LagrangeElement.isEdgeUnisolvent`), so that `Π_h u` vanishes on `∂Ω` when `u` does,
and its shape functions are polynomials of degree at most `k` (`LagrangeElement.shape_eq_eval`),
so that `Π_h u` is piecewise polynomial. -/

section Example1042

open MeasureTheory Set TopologicalSpace EuclideanSpace MvPolynomial
open scoped ENNReal

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)


variable (Ω : Opens 𝔼₂)

/-- **The Dirichlet form of the Poisson problem** on `V = H¹₀(Ω)`, `a(u, v) = ∫_Ω ∇u · ∇v`
(Example 8.3.5's form, as an Atkinson–Han bilinear form): `Chapter08.modelOperator` read as a
form. -/
noncomputable abbrev poissonForm : BilinForm (SobolevEuclideanZero 2 1 2 Ω) :=
  BilinForm.ofCLM (Chapter08.modelOperator (d := 1) Ω)

/-- `a(u, v) = ∫_Ω ∑ᵢ ∂ᵢu ∂ᵢv`. -/
theorem poissonForm_apply (u v : SobolevEuclideanZero 2 1 2 Ω) :
    poissonForm Ω u v = ∫ x in (Ω : Set 𝔼₂),
      ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean 2 1 2 Ω) (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean 2 1 2 Ω) (MultiIndexLE.single i) x :=
  Elliptic.dirichletForm_apply Ω u v

/-- **The load functional** `ℓ(v) = ∫_Ω f v` on `H¹₀(Ω)`, for `f ∈ L²(Ω)`. -/
noncomputable def poissonLoad (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂))) :
    StrongDual ℝ (SobolevEuclideanZero 2 1 2 Ω) :=
  (Elliptic.load Ω f).comp (SobolevEuclideanZero 2 1 2 Ω).subtypeL

/-- `ℓ(v) = ∫_Ω f v`. -/
theorem poissonLoad_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
    (v : SobolevEuclideanZero 2 1 2 Ω) :
    poissonLoad Ω f v = ∫ x in (Ω : Set 𝔼₂),
      f x * SobolevMultiIndex.fn (v : SobolevEuclidean 2 1 2 Ω) x :=
  Elliptic.load_apply Ω f v

/-- The Dirichlet form is bounded with `M = 1`. -/
theorem poissonForm_isBoundedWith : (poissonForm Ω).IsBoundedWith 1 := fun u v ↦ by
  have h := Elliptic.dirichletForm_isBoundedWith Ω u v
  rw [one_mul] at h ⊢
  exact h

/-- The Dirichlet form is `V`-elliptic on `H¹₀(Ω)` with `α = (1 + (2R)²)⁻¹` for
`Ω ⊆ B(0, R)`: Poincaré's inequality. -/
theorem poissonForm_isEllipticWith {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ Metric.ball 0 R) :
    (poissonForm Ω).IsEllipticWith (1 + (2 * R) ^ 2)⁻¹ := fun v ↦
  Elliptic.dirichletForm_restrict_isCoerciveWith (d := 1) Ω hR hΩ v

/-- **Example 10.4.2.** Consider `−Δu = f` in `Ω`, `u = 0` on `Γ = ∂Ω`, on a polygon `Ω ⊆ B(0, R)`
triangulated by a regular family `{𝒯_h}` (mesh parameters at most `H`, `∂Ω` a union of element
edges), with `f ∈ L²(Ω)` and the finite element space

  `V_h = {v_h ∈ C(Ω̄) : v_h|_K ∈ ℙ_k(K) for every K ∈ 𝒯_h, v_h|_∂Ω = 0} ⊆ H¹₀(Ω)`

(`Triangulation.polySpaceZero`, the continuous piecewise polynomials of degree at most `k ≥ 1`
vanishing on the boundary). Then: the variational problem, `u ∈ H¹₀(Ω)` with
`∫_Ω ∇u · ∇v = ∫_Ω f v` for all `v ∈ H¹₀(Ω)`, has a unique solution (Example 8.3.5, Lax–Milgram);
the discrete problem, `u_h ∈ V_h` with `∫_Ω ∇u_h · ∇v_h = ∫_Ω f v_h` for all `v_h ∈ V_h`, has a
unique solution (`V_h` is finite-dimensional, `Triangulation.finiteDimensional_polySpaceZero`);
and there is a constant `c` such that, whenever the solution lies in `H^{k+1}(Ω)` — read on a
representative `ũ` continuous up to the boundary, as in Theorem 10.3.9, with `ũ = 0` on `Γ`, the
boundary condition of the problem — the error is estimated by

  `‖u − u_h‖_{1,Ω} ≤ c h^k ‖u‖_{k+1,Ω}`.

The estimate is `theorem_10_4_1` with the `ℙ_k` Lagrange element on the principal lattice, whose
interpolant `Π_h ũ` lies in `V_h` because the element is conforming, polynomial and edge unisolvent,
so that `Π_h ũ` vanishes on `∂Ω` with `ũ` (`LagrangeElement.exists_mem_polySpaceZero_globalInterp`):
the backbone's `FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm` at `s = k`. It is
stated with the seminorm `|u|_{k+1,Ω}` replaced by the norm `‖u‖_{k+1,Ω}`, as the book writes it.

The hypothesis "`ũ = 0` on `Γ`" is the book's boundary condition; it would follow from
`u ∈ H¹₀(Ω)` and the continuity of `ũ` on a `C¹` domain (Theorem 9.17 (ii) ⇒ (i),
`SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure`), but a polygon is not `C¹`. -/
theorem example_10_4_2 {k : ℕ} (hk : 1 ≤ k) {ι : Type*} {l : Filter ι}
    {𝒯 : ι → Triangulation Ω} (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hedge : ∀ i, (𝒯 i).FrontierSubsetEdges)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ Metric.ball 0 R) :
    (∀ f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)), ∃! u : SobolevEuclideanZero 2 1 2 Ω,
      ∀ v, poissonForm Ω u v = poissonLoad Ω f v) ∧
    (∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂))) (i : ι),
      ∃! uh, GalerkinProblem (poissonForm Ω) (poissonLoad Ω f) ((𝒯 i).polySpaceZero 2 k) uh) ∧
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
      (u : SobolevEuclideanZero 2 1 2 Ω),
      (∀ v, poissonForm Ω u v = poissonLoad Ω f v) →
      ∀ uh : ι → SobolevEuclideanZero 2 1 2 Ω,
        (∀ i, GalerkinProblem (poissonForm Ω) (poissonLoad Ω f) ((𝒯 i).polySpaceZero 2 k) (uh i)) →
        ∀ ũ : 𝔼₂ → ℝ,
          SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ →
          MemSobolev ũ (k + 1) 2 Ω volume → ContinuousOn ũ (closure (Ω : Set 𝔼₂)) →
          EqOn ũ 0 (frontier (Ω : Set 𝔼₂)) →
          ∀ i, ‖u - uh i‖ ≤ c * (𝒯 i).meshSize ^ k * (sobolevNorm ũ (k + 1) 2 Ω volume).toReal := by
  have hk0 : 0 < k := hk
  have hM := poissonForm_isBoundedWith Ω
  have hα := poissonForm_isEllipticWith Ω hR hΩ
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  refine ⟨fun f ↦ ?_, fun f i ↦ ?_, ?_⟩
  · -- the continuous problem: Example 8.3.5
    have h := Chapter08.example_8_3_5 (d := 1) Ω hR hΩ (poissonLoad Ω f)
    refine (existsUnique_congr fun u ↦ forall_congr' fun v ↦ ?_).2 h
    rw [poissonForm_apply]
  · -- the discrete problem: Lax–Milgram on the finite-dimensional `V_h`
    have := LagrangeElement.finiteDimensional_polySpaceZero hk0 (𝒯 i) 2
    exact Chapter09.existsUnique_galerkinProblem hM hpos hα (poissonLoad Ω f)
      ((𝒯 i).polySpaceZero 2 k)
  · -- the error estimate: the backbone's Poisson instance of Theorem 10.4.1
    have h := FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm (k := k) hk le_rfl
      hreg hH hedge hR hΩ
    obtain ⟨C, hC0, hC⟩ := h
    exact ⟨1 / (1 + (2 * R) ^ 2)⁻¹ * C, by positivity, fun f u hu uh huh ↦ hC f u hu uh huh⟩

end Example1042


end Chapter10

end AtkinsonHan
