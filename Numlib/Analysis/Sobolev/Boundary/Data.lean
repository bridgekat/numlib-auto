import Mathlib.Analysis.InnerProductSpace.Trace
import Numlib.Analysis.PDE.Elliptic.Dirichlet

/-!
# Boundary data: the surface measure, the outward normal and the divergence theorem, abstractly

The abstract interface of the boundary round (decision B1 of `notes/boundary/planning-brief.md`):
the divergence `EuclideanSpace.div`, the structure `BoundaryData Ω` — a finite measure `σ` carried
by `∂Ω`, a unit vector field `ν` defined `σ`-a.e., and the divergence theorem
`∫_Ω div F = ∫ ⟪F, ν⟫ dσ` for every field `F` of class `C¹(Ω̄)` — and the structure
`BoundaryData.TraceFamily`: a bounded linear trace `W^{1,p}(Ω) → L^p(σ)` for every
`1 ≤ p < ∞` which restricts continuous representatives, together with Green's formula
`∫_Ω ∂ᵢu v + ∫_Ω u ∂ᵢv = ∫ (Tu)(Tv) νᵢ dσ` at conjugate exponents. Every consumer of the
Atkinson–Han, QSS and Brezis surfaces that mentions `∂Ω` is stated once over these two structures;
the instances are `IsContDiffDomain.boundaryData` / `IsContDiffDomain.traceFamily`
(`Boundary/ContDiffDomain.lean`) and `Triangulation.boundaryData` / `Triangulation.traceFamily`
(`Boundary/Polygon.lean`, `Boundary/PolygonTrace.lean`).

What the structures do *not* contain: a transversal field (a pinched polygon has none; the Nečas
construction that uses one is `Boundary/Trace.lean`), density of smooth functions
(`Boundary/Density.lean`), and any Hausdorff measure (`σ = μH[N−1]⌊∂Ω` is a future node needing
the area formula). Boundedness of `Ω` is a field: every instance of this round is bounded, and it
spares the divergence field a support hypothesis.

Shared vocabulary of the graph modules, placed here so that `GraphMeasure` and `Divergence` can be
written in parallel: the epigraph `EuclideanSpace.epigraph g = {y : g y' < y_N}` of a function of
`d` variables with its closure and frontier for continuous `g` (so that `IsBoundaryGraphAt` reads
`Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' epigraph g`, `EuclideanSpace.isBoundaryGraphAt_iff`), and the
measure preservation of a rigid motion (`AffineIsometryEquiv.measurePreserving`).

Consequences proved here, all from the fields: the classical Green formulas for `C¹(Ω̄)` and
`C²(Ω̄)` functions (Atkinson–Han §7.6 before the density argument,
[brezis2011functional] §9.5 Example 4 Step A), `W_0^{1,p}(Ω) ⊆ ker T`, the `H²` Green formula
with the normal trace `∂_ν u = ∑ νᵢ T(∂ᵢu)` ([brezis2011functional], Comments on chapter 9,
7 (iii)), and the Neumann boundary condition of an `H²` weak solution (the half of
[brezis2011functional] Theorem 9.26 that the trace gives a meaning to).

## Main definitions

* `EuclideanSpace.div F x = ∑ i, fderiv ℝ F x (single i 1) i`, the divergence, with its
  calculus: `div_eq_trace`, the product rule `div_smul_fun`, the affine and rotation
  invariance `div_comp_continuousLinearEquiv`, `div_comp_affineIsometryEquiv`;
* `BoundaryData Ω`: `σ`, `ν`, boundedness of `Ω`, finiteness of `σ`, `σ (∂Ω)ᶜ = 0`,
  measurability and `σ`-a.e. unit length of `ν`, and the divergence identity `integral_div_eq`;
* `BoundaryData.TraceFamily B`: `traceL p hp : W^{1,p}(Ω) →L L^p(σ)`, `traceL_ae_eq`, `green`
  at conjugate exponents, `green_contDiff` against a fixed compactly supported `C¹` test function;
* `BoundaryData.TraceFamily.normalTrace u = ∑ i, ν i • T(∂ᵢu)` for `u ∈ H²(Ω)`;
* `EuclideanSpace.epigraph g`, the open region strictly above the graph of `g`.

## Main statements

* `BoundaryData.integral_fderiv_mul_add_eq`, `BoundaryData.integral_laplacian_mul_add_eq`: the
  classical Green formulas;
* `BoundaryData.TraceFamily.traceL_eq_zero_of_mem_zero`: `W_0^{1,p}(Ω) ⊆ ker T`;
* `BoundaryData.TraceFamily.green_laplacian`: Green's formula for `u ∈ H²`, `v ∈ H¹`;
* `BoundaryData.TraceFamily.normalTrace_eq_zero_of_forall_laplaceForm_eq`: the Neumann condition
  `∂u/∂ν = 0` of an `H²` weak solution of `−Δu + u = f`;
* `EuclideanSpace.closure_epigraph`, `EuclideanSpace.frontier_epigraph`,
  `IsBoundaryGraphAt.frontier_inter_ball`;
* `AffineIsometryEquiv.measurePreserving`.

Conventions: `E := EuclideanSpace ℝ (Fin N)`, `Ω : Opens E`,
`W^{1,p}(Ω) := SobolevEuclidean N 1 p Ω`, `fn := SobolevMultiIndex.fn`,
`∂ᵢ u := SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)`;
"`F ∈ C¹(Ω̄)`" is the pair `ContinuousOn F (closure Ω)`, `ContDiffOnClosure ℝ 1 F Ω`.

## References

[brezis2011functional], §9.5 Example 4, §9.6 (49), Theorem 9.26, Comments on chapter 9, 7;
Atkinson–Han §7.3 (Theorem 7.3.10) and §7.6; Grisvard, *Elliptic Problems in Nonsmooth Domains*,
§1.5 (Theorems 1.5.1.3 and 1.5.3.1).
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Laplacian Topology

noncomputable section

/-! ### The Riesz map of a real Hilbert space, real-linearly -/

section ToDualReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The Riesz isometry of a real Hilbert space as a real-linear isometry equivalence**:
`InnerProductSpace.toDual ℝ E` is typed as conjugate-linear (`≃ₗᵢ⋆[ℝ]`), which over `ℝ` is the
same map; this is that map with the linear type, so that the calculus lemmas stated for
`≃ₗᵢ[𝕜]` (`LinearIsometryEquiv.comp_fderiv`, `contDiff`, `differentiableAt`) apply. Its inverse
is `(toDual ℝ E).symm`, so `gradient f x = (toDualReal E).symm (fderiv ℝ f x)` definitionally. -/
def InnerProductSpace.toDualReal : E ≃ₗᵢ[ℝ] StrongDual ℝ E where
  toFun := InnerProductSpace.toDual ℝ E
  invFun := (InnerProductSpace.toDual ℝ E).symm
  map_add' := map_add _
  map_smul' c x := by
    rw [LinearIsometryEquiv.map_smulₛₗ]
    rfl
  left_inv := (InnerProductSpace.toDual ℝ E).symm_apply_apply
  right_inv := (InnerProductSpace.toDual ℝ E).apply_symm_apply
  norm_map' := (InnerProductSpace.toDual ℝ E).norm_map

variable {E}

@[simp]
theorem InnerProductSpace.toDualReal_apply (x : E) :
    InnerProductSpace.toDualReal E x = InnerProductSpace.toDual ℝ E x := rfl

@[simp]
theorem InnerProductSpace.toDualReal_symm_apply (φ : StrongDual ℝ E) :
    (InnerProductSpace.toDualReal E).symm φ = (InnerProductSpace.toDual ℝ E).symm φ := rfl

/-- The gradient through `toDualReal`. -/
theorem gradient_eq_toDualReal_symm (f : E → ℝ) :
    gradient f = fun x ↦ (InnerProductSpace.toDualReal E).symm (fderiv ℝ f x) := rfl

end ToDualReal

/-! ### The divergence and its calculus -/

namespace EuclideanSpace

variable {N : ℕ}

/-- **The divergence** `div F x = ∑ᵢ ∂ᵢFᵢ(x)` of a vector field `F : ℝ^N → ℝ^N`, in the shape of
Mathlib's box divergence theorem (`∑ i, f' x (e i) i`). -/
def div (F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    ℝ :=
  ∑ i, fderiv ℝ F x (EuclideanSpace.single i 1) i

variable {F G : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {x : EuclideanSpace ℝ (Fin N)}

/-- The divergence of a sum of differentiable fields. -/
@[simp]
theorem div_add (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    div (F + G) x = div F x + div G x := by
  simp only [div, fderiv_add hF hG, add_apply, PiLp.add_apply, Finset.sum_add_distrib]

/-- The divergence of the negative of a field. -/
@[simp]
theorem div_neg : div (-F) x = -div F x := by
  simp only [div, fderiv_neg, neg_apply, PiLp.neg_apply, Finset.sum_neg_distrib]

/-- The divergence of a constant multiple of a field. -/
@[simp]
theorem div_smul (c : ℝ) : div (c • F) x = c * div F x := by
  simp only [div, fderiv_const_smul_field, Pi.smul_apply, smul_apply, PiLp.smul_apply,
    smul_eq_mul, Finset.mul_sum]

/-- **The divergence is the trace of the derivative**, which is what makes it invariant under
changes of frame (`div_comp_continuousLinearEquiv`). -/
theorem div_eq_trace (F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    div F x = LinearMap.trace ℝ _ (fderiv ℝ F x : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] _) := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
  simp only [div, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
    EuclideanSpace.inner_single_left, conj_trivial, one_mul]

/-- **The product rule for the divergence**: `div (φ F) = ⟪∇φ, F⟫ + φ div F` at a point where the
scalar `φ` and the field `F` are differentiable. -/
theorem div_smul_fun {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : DifferentiableAt ℝ φ x)
    (hF : DifferentiableAt ℝ F x) :
    div (fun y ↦ φ y • F y) x = ⟪gradient φ x, F x⟫_ℝ + φ x * div F x := by
  have h : ⟪gradient φ x, F x⟫_ℝ = ∑ i, fderiv ℝ φ x (EuclideanSpace.single i 1) * F x i := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (F x)]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      smul_eq_mul, mul_comm]
  rw [h, div, div, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_fun_smul hφ hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-- The divergence of the field `u e_i` is `∂ᵢu`: the form of the product rule the classical Green
formula `BoundaryData.integral_fderiv_mul_add_eq` uses. -/
theorem div_const_smul_single {u : EuclideanSpace ℝ (Fin N) → ℝ} (hu : DifferentiableAt ℝ u x)
    (i : Fin N) :
    div (fun y ↦ u y • EuclideanSpace.single i 1) x = fderiv ℝ u x (EuclideanSpace.single i 1) := by
  simp only [div, fderiv_smul_const hu, ContinuousLinearMap.smulRight_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- **Affine invariance of the divergence** (the linear Piola identity): conjugating a field by
the affine map `z ↦ M z + b` and its linear inverse does not change the divergence,
`div (M⁻¹ ∘ F ∘ (M · + b)) x = div F (M x + b)`. Through `div_eq_trace`: the derivative of the
conjugate is `M⁻¹ ∘ DF ∘ M`, and the trace is conjugation invariant. -/
theorem div_comp_continuousLinearEquiv
    (M : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) (b : EuclideanSpace ℝ (Fin N))
    (hF : DifferentiableAt ℝ F (M x + b)) :
    div (fun z ↦ M.symm (F (M z + b))) x = div F (M x + b) := by
  have hM : DifferentiableAt ℝ (fun z ↦ M z + b) x := M.differentiableAt.add_const b
  have h1 : fderiv ℝ (fun z ↦ M.symm (F (M z + b))) x
      = (M.symm : _ →L[ℝ] _).comp ((fderiv ℝ F (M x + b)).comp (M : _ →L[ℝ] _)) := by
    have e : (fun z ↦ M.symm (F (M z + b))) = M.symm ∘ (F ∘ fun z ↦ M z + b) := rfl
    rw [e, M.symm.comp_fderiv, fderiv_comp x hF hM, fderiv_add_const, M.fderiv]
  rw [div_eq_trace, div_eq_trace, h1, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  congr 1
  ext y
  simp

/-- **Rotation invariance of the divergence**: for a rigid motion `T`, the field
`z ↦ T.linear (F (T⁻¹ z))` has divergence `div F (T⁻¹ z)`. This is the change of frame of the
divergence theorem on a graph chart. -/
theorem div_comp_affineIsometryEquiv
    (T : EuclideanSpace ℝ (Fin N) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin N)) {y : EuclideanSpace ℝ (Fin N)}
    (hF : DifferentiableAt ℝ F (T.symm y)) :
    div (fun z ↦ T.linearIsometryEquiv (F (T.symm z))) y = div F (T.symm y) := by
  have hs : ∀ z, T.linearIsometryEquiv.symm.toContinuousLinearEquiv z + T.symm 0 = T.symm z :=
    fun z ↦ by
      have := T.symm.map_vadd (0 : EuclideanSpace ℝ (Fin N)) z
      rw [vadd_eq_add, add_zero, vadd_eq_add] at this
      rw [this]
      rfl
  have hLs : ∀ z, T.linearIsometryEquiv.symm.toContinuousLinearEquiv.symm z
      = T.linearIsometryEquiv z := fun z ↦ by
    rw [← LinearIsometryEquiv.toContinuousLinearEquiv_symm, LinearIsometryEquiv.symm_symm]
    rfl
  have key := div_comp_continuousLinearEquiv (F := F) (x := y)
    T.linearIsometryEquiv.symm.toContinuousLinearEquiv (T.symm 0) (by rwa [hs])
  simp only [hs, hLs] at key
  exact key

/-- The Laplacian is the sum of the second derivatives `D²u(eᵢ, eᵢ)` in the standard basis, at
every point (no differentiability assumed: both sides are `0` where `u` is not twice
differentiable). -/
theorem laplacian_eq_sum_fderiv_fderiv_single (u : EuclideanSpace ℝ (Fin N) → ℝ)
    (x : EuclideanSpace ℝ (Fin N)) :
    Δ u x
      = ∑ i, fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin N) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- **The divergence of the gradient is the Laplacian**, at every point. -/
theorem div_gradient_eq_laplacian (u : EuclideanSpace ℝ (Fin N) → ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : div (gradient u) x = Δ u x := by
  rw [laplacian_eq_sum_fderiv_fderiv_single, div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : gradient u
      = (InnerProductSpace.toDualReal (EuclideanSpace ℝ (Fin N))).symm ∘ fderiv ℝ u := rfl
  rw [h, LinearIsometryEquiv.comp_fderiv, ContinuousLinearMap.comp_apply]
  have h2 : ∀ w : EuclideanSpace ℝ (Fin N), w i = ⟪w, EuclideanSpace.single i 1⟫_ℝ := fun w ↦ by
    rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  rw [h2, LinearIsometryEquiv.coe_coe'', InnerProductSpace.toDualReal_symm_apply,
    InnerProductSpace.toDual_symm_apply]

end EuclideanSpace

/-! ### The class `C¹(s̄)` under products -/

section ContDiffOnClosure

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X F : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : X → F} {s : Set X}

/-- The first derivative tensor is the derivative, read through `continuousMultilinearCurryFin1`
(the real case is `iteratedFDeriv_one_eq_symm_fderiv` of
`Numlib/Analysis/Sobolev/Friedrichs.lean`). -/
theorem iteratedFDeriv_one_eq_symm_fderiv' (f : X → F) (x : X) :
    iteratedFDeriv 𝕜 1 f x = (continuousMultilinearCurryFin1 𝕜 X F).symm (fderiv 𝕜 f x) :=
  ContinuousMultilinearMap.ext fun m ↦ by simp

/-- **The class `C¹(s̄)` through the derivative**: `f ∈ C¹(s̄)` iff `f` is `C¹` on `s` and both `f`
and `fderiv 𝕜 f` extend continuously to `closure s`. -/
theorem contDiffOnClosure_one_iff :
    ContDiffOnClosure 𝕜 1 f s ↔ ContDiffOn 𝕜 1 f s ∧
      (∃ g : X → F, ContinuousOn g (closure s) ∧ EqOn g f s) ∧
      ∃ g' : X → X →L[𝕜] F, ContinuousOn g' (closure s) ∧ EqOn g' (fderiv 𝕜 f) s := by
  constructor
  · intro h
    refine ⟨h.1, h.continuousOn_closure, ?_⟩
    obtain ⟨g, hgc, hge⟩ := h.2 1 le_rfl
    refine ⟨fun x ↦ continuousMultilinearCurryFin1 𝕜 X F (g x),
      (continuousMultilinearCurryFin1 𝕜 X F).continuous.comp_continuousOn hgc, fun x hx ↦ ?_⟩
    change continuousMultilinearCurryFin1 𝕜 X F (g x) = fderiv 𝕜 f x
    rw [hge hx, iteratedFDeriv_one_eq_symm_fderiv', LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨h, ⟨g, hgc, hge⟩, ⟨g', hgc', hge'⟩⟩
    refine ⟨h, fun m hm ↦ ?_⟩
    have hm' : m ≤ 1 := by exact_mod_cast hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm' with rfl | rfl
    · refine ⟨fun x ↦ (continuousMultilinearCurryFin0 𝕜 X F).symm (g x),
        (continuousMultilinearCurryFin0 𝕜 X F).symm.continuous.comp_continuousOn hgc,
        fun x hx ↦ ?_⟩
      change (continuousMultilinearCurryFin0 𝕜 X F).symm (g x) = iteratedFDeriv 𝕜 0 f x
      rw [hge hx, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    · refine ⟨fun x ↦ (continuousMultilinearCurryFin1 𝕜 X F).symm (g' x),
        (continuousMultilinearCurryFin1 𝕜 X F).symm.continuous.comp_continuousOn hgc',
        fun x hx ↦ ?_⟩
      change (continuousMultilinearCurryFin1 𝕜 X F).symm (g' x) = iteratedFDeriv 𝕜 1 f x
      rw [hge' hx, iteratedFDeriv_one_eq_symm_fderiv']

/-- The second derivative of a function of class `C²(s̄)` extends continuously to `closure s`. -/
theorem ContDiffOnClosure.exists_continuousOn_fderiv_fderiv (h : ContDiffOnClosure 𝕜 2 f s) :
    ∃ G : X → X →L[𝕜] X →L[𝕜] F, ContinuousOn G (closure s) ∧
      EqOn G (fderiv 𝕜 (fderiv 𝕜 f)) s := by
  obtain ⟨g₂, hc, he⟩ := h.2 2 le_rfl
  let C : (X [×1]→L[𝕜] F) →L[𝕜] (X →L[𝕜] F) :=
    (continuousMultilinearCurryFin1 𝕜 X F : (X [×1]→L[𝕜] F) →L[𝕜] (X →L[𝕜] F))
  let L : (X [×2]→L[𝕜] F) →L[𝕜] (X →L[𝕜] X [×1]→L[𝕜] F) :=
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 ↦ X) F :
      (X [×2]→L[𝕜] F) →L[𝕜] (X →L[𝕜] X [×1]→L[𝕜] F))
  refine ⟨fun x ↦ ContinuousLinearMap.compL 𝕜 X (X [×1]→L[𝕜] F) (X →L[𝕜] F) C (L (g₂ x)), ?_,
    fun x hx ↦ ?_⟩
  · exact ((ContinuousLinearMap.compL 𝕜 X (X [×1]→L[𝕜] F) (X →L[𝕜] F) C).continuous.comp
      L.continuous).comp_continuousOn hc
  · ext w v
    simp only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, he hx]
    change continuousMultilinearCurryFin1 𝕜 X F
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 ↦ X) F (iteratedFDeriv 𝕜 2 f x) w) v
      = _
    rw [continuousMultilinearCurryFin1_apply, continuousMultilinearCurryLeftEquiv_apply,
      iteratedFDeriv_two_apply]
    simp

namespace ContDiffOnClosure

/-- **`C¹(s̄)` is closed under the product of a scalar function with a vector function**, on an
open set `s`: `D(u v) = u Dv + (Du) v` on `s`, and the continuous extensions of `u, v, Du, Dv`
to `closure s` combine into one of `D(u v)`. -/
theorem smul (hs : IsOpen s) {u : X → 𝕜} {v : X → F} (hu : ContDiffOnClosure 𝕜 1 u s)
    (hv : ContDiffOnClosure 𝕜 1 v s) : ContDiffOnClosure 𝕜 1 (fun x ↦ u x • v x) s := by
  rw [contDiffOnClosure_one_iff] at hu hv ⊢
  obtain ⟨hu, ⟨u₁, hu₁c, hu₁e⟩, ⟨u₁', hu₁c', hu₁e'⟩⟩ := hu
  obtain ⟨hv, ⟨v₁, hv₁c, hv₁e⟩, ⟨v₁', hv₁c', hv₁e'⟩⟩ := hv
  refine ⟨hu.smul hv, ⟨fun x ↦ u₁ x • v₁ x, hu₁c.smul hv₁c, fun x hx ↦ by
    simp only [hu₁e hx, hv₁e hx]⟩,
    ⟨fun x ↦ u₁ x • v₁' x + (u₁' x).smulRight (v₁ x), ?_, fun x hx ↦ ?_⟩⟩
  · refine (hu₁c.smul hv₁c').add ?_
    exact (ContinuousLinearMap.smulRightL 𝕜 X F).continuous₂.comp_continuousOn
      (hu₁c'.prodMk hv₁c)
  · have hux : DifferentiableAt 𝕜 u x :=
      (hu.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
    have hvx : DifferentiableAt 𝕜 v x :=
      (hv.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
    simp only [hu₁e hx, hv₁e hx, hu₁e' hx, hv₁e' hx]
    exact (fderiv_fun_smul hux hvx).symm

/-- **`C¹(s̄)` is closed under products of scalar functions**, on an open set `s`. -/
theorem mul (hs : IsOpen s) {u v : X → 𝕜} (hu : ContDiffOnClosure 𝕜 1 u s)
    (hv : ContDiffOnClosure 𝕜 1 v s) : ContDiffOnClosure 𝕜 1 (fun x ↦ u x * v x) s :=
  hu.smul hs hv

/-- A constant function is of class `C¹(s̄)`. -/
theorem const (c : F) : ContDiffOnClosure 𝕜 1 (fun _ : X ↦ c) s := by
  rw [contDiffOnClosure_one_iff]
  exact ⟨contDiffOn_const, ⟨fun _ ↦ c, continuousOn_const, fun _ _ ↦ rfl⟩,
    ⟨fun _ ↦ 0, continuousOn_const, fun x _ ↦ (fderiv_const_apply c).symm⟩⟩

/-- **`C¹(s̄)` is closed under multiplication by a fixed vector**, on an open set `s`. -/
theorem smul_const (hs : IsOpen s) {u : X → 𝕜} (hu : ContDiffOnClosure 𝕜 1 u s) (c : F) :
    ContDiffOnClosure 𝕜 1 (fun x ↦ u x • c) s :=
  hu.smul hs (const c)

end ContDiffOnClosure

section Gradient

variable {N : ℕ} {s : Set (EuclideanSpace ℝ (Fin N))}

/-- The inverse Riesz map of `ℝ^N`, `(toDualReal _).symm`, locally. -/
local notation "𝓡⁻¹" =>
  LinearIsometryEquiv.symm (InnerProductSpace.toDualReal (EuclideanSpace ℝ (Fin N)))

/-- **The gradient of a `C²(s̄)` function, read through a continuous extension `g` of its
derivative, is of class `C¹(s̄)`** on an open `s`: `x ↦ (toDual)⁻¹ (g x)` agrees with `∇u` on `s`,
and its derivative `(toDual)⁻¹ ∘ D²u` extends continuously by the order-two clause. -/
theorem ContDiffOnClosure.toDual_symm_of_eqOn_fderiv {u : EuclideanSpace ℝ (Fin N) → ℝ}
    (hs : IsOpen s) (hu : ContDiffOnClosure ℝ 2 u s)
    {g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hgc : ContinuousOn g (closure s)) (hge : EqOn g (fderiv ℝ u) s) :
    ContDiffOnClosure ℝ 1 (fun x ↦ 𝓡⁻¹ (g x)) s := by
  obtain ⟨G, hGc, hGe⟩ := hu.exists_continuousOn_fderiv_fderiv
  rw [contDiffOnClosure_one_iff]
  refine ⟨?_, ⟨_, 𝓡⁻¹.continuous.comp_continuousOn hgc,
    fun _ _ ↦ rfl⟩, ⟨fun x ↦ (𝓡⁻¹ :
      (EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin N)).comp (G x), ?_,
    fun x hx ↦ ?_⟩⟩
  · have h1 : ContDiffOn ℝ 1 (fderiv ℝ u) s := hu.1.fderiv_of_isOpen hs (by norm_num)
    refine (𝓡⁻¹.contDiff.comp_contDiffOn h1).congr
      fun x hx ↦ ?_
    simp only [Function.comp, hge hx]
  · exact (ContinuousLinearMap.compL ℝ _ _ _ _).continuous.comp_continuousOn hGc
  · have heq : (fun y ↦ 𝓡⁻¹ (g y))
        =ᶠ[𝓝 x] fun y ↦ 𝓡⁻¹ (fderiv ℝ u y) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      rw [hge hy]
    change _ ∘L G x = _
    rw [heq.fderiv_eq, hGe hx]
    exact (𝓡⁻¹.comp_fderiv).symm

end Gradient

end ContDiffOnClosure

/-! ### The boundary data of an open set -/

/-- **The boundary data of an open set `Ω ⊆ ℝ^N`**: a surface measure `σ` on the ambient space
carried by `∂Ω` (decision B8: no subtype, `L^p(∂Ω)` is `Lp ℝ p σ`), an outward unit normal `ν`
meaningful `σ`-almost everywhere, boundedness of `Ω`, and the divergence theorem (Gauss–Green)
`∫_Ω div F = ∫ ⟪F, ν⟫ dσ` for every field of class `C¹(Ω̄)` — `C¹` on `Ω` with the derivative
extending continuously to `Ω̄` (`ContDiffOnClosure`), and `F` itself continuous on `Ω̄`. This is
the regularity the books state (Atkinson–Han §7.6, QSS (12.95), [brezis2011functional] §9.5
Example 4); `C¹` fields on `ℝ^N` are the corollary `BoundaryData.integral_div_eq_of_contDiff`.

Instances: `IsContDiffDomain.boundaryData` (bounded `C¹` graph domains),
`Triangulation.boundaryData` (triangulated plane domains), `EuclideanSpace.triangleBoundaryData`
(a single triangle). Not a class: a domain may carry several descriptions, and the consumers take
the data explicitly. -/
structure BoundaryData {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N))) where
  /-- The surface measure, a measure on the ambient space carried by `∂Ω`. -/
  σ : Measure (EuclideanSpace ℝ (Fin N))
  /-- The outward unit normal, a function on the ambient space meaningful `σ`-a.e. -/
  ν : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)
  /-- `Ω` is bounded. -/
  isBounded : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))
  /-- The surface measure is finite. -/
  isFiniteMeasure : IsFiniteMeasure σ
  /-- The surface measure is carried by `∂Ω`. -/
  measure_compl_frontier : σ (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))ᶜ = 0
  /-- The normal is measurable. -/
  aestronglyMeasurable_ν : AEStronglyMeasurable ν σ
  /-- The normal has unit length `σ`-a.e. -/
  ae_norm_ν : ∀ᵐ x ∂σ, ‖ν x‖ = 1
  /-- **The divergence theorem** for fields of class `C¹(Ω̄)`. -/
  integral_div_eq : ∀ F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N),
    ContinuousOn F (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
    ContDiffOnClosure ℝ 1 F (Ω : Set (EuclideanSpace ℝ (Fin N))) →
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), EuclideanSpace.div F x = ∫ x, ⟪F x, ν x⟫_ℝ ∂σ

namespace BoundaryData

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω)

/-- The surface measure of a `BoundaryData` is finite. -/
instance instIsFiniteMeasure : IsFiniteMeasure B.σ := B.isFiniteMeasure

/-- `σ`-almost every point lies on `∂Ω`. -/
theorem ae_mem_frontier : ∀ᵐ x ∂B.σ, x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
  ae_iff.2 B.measure_compl_frontier

/-- `σ`-almost every point lies outside `Ω`. -/
theorem ae_notMem : ∀ᵐ x ∂B.σ, x ∉ (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
  B.ae_mem_frontier.mono fun x hx hxΩ ↦ hx.2 (by rwa [Ω.isOpen.interior_eq])

/-- The coordinates of the normal are bounded by one `σ`-a.e. -/
theorem ae_abs_ν_apply_le (i : Fin N) : ∀ᵐ x ∂B.σ, |B.ν x i| ≤ 1 :=
  B.ae_norm_ν.mono fun x hx ↦ by
    rw [← Real.norm_eq_abs, ← hx]; exact PiLp.norm_apply_le _ i

/-- The coordinates of the normal are measurable. -/
theorem aestronglyMeasurable_ν_apply (i : Fin N) :
    AEStronglyMeasurable (fun x ↦ B.ν x i) B.σ :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_aestronglyMeasurable B.aestronglyMeasurable_ν

/-- Multiplying an `L^p(σ)` function by a coordinate of the normal keeps it in `L^p(σ)`. -/
theorem memLp_ν_apply_mul {p : ℝ≥0∞} {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : MemLp f p B.σ)
    (i : Fin N) : MemLp (fun x ↦ B.ν x i * f x) p B.σ :=
  hf.of_le ((B.aestronglyMeasurable_ν_apply i).mul hf.aestronglyMeasurable) <|
    (B.ae_abs_ν_apply_le i).mono fun x hx ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hx

/-- **The divergence theorem for `C¹` fields on `ℝ^N`**: `∫_Ω div F = ∫ ⟪F, ν⟫ dσ`. -/
theorem integral_div_eq_of_contDiff {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (hF : ContDiff ℝ 1 F) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), EuclideanSpace.div F x
      = ∫ x, ⟪F x, B.ν x⟫_ℝ ∂B.σ :=
  B.integral_div_eq F hF.continuous.continuousOn (hF.contDiffOn.contDiffOnClosure Ω.isOpen)

include B in
/-- A function continuous on `closure Ω` is integrable on the bounded `Ω`. -/
theorem integrableOn_of_continuousOn {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : EuclideanSpace ℝ (Fin N) → G}
    (hf : ContinuousOn f (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    IntegrableOn f (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
  (hf.integrableOn_compact (Bornology.IsBounded.isCompact_closure B.isBounded)).mono_set
    subset_closure

/-- **The classical Green formula** (Atkinson–Han §7.6, [brezis2011functional] §9.5 Example 4
Step A) for functions `u, v ∈ C¹(Ω̄)`:
`∫_Ω ∂ᵢu v + ∫_Ω u ∂ᵢv = ∫ u v νᵢ dσ`. The divergence theorem for the field `(u v) e_i`. -/
theorem integral_fderiv_mul_add_eq {u v : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hu' : ContDiffOnClosure ℝ 1 u (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hv : ContinuousOn v (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hv' : ContDiffOnClosure ℝ 1 v (Ω : Set (EuclideanSpace ℝ (Fin N)))) (i : Fin N) :
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), fderiv ℝ u x (EuclideanSpace.single i 1) * v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * fderiv ℝ v x (EuclideanSpace.single i 1)
      = ∫ x, u x * v x * B.ν x i ∂B.σ := by
  have hΩ := Ω.isOpen
  have hdiv := B.integral_div_eq (fun x ↦ (u x * v x) • EuclideanSpace.single i 1)
    ((hu.mul hv).smul continuousOn_const) ((hu'.mul hΩ hv').smul_const hΩ _)
  -- the boundary term
  have hR : ∫ x, ⟪(u x * v x) • EuclideanSpace.single i (1 : ℝ), B.ν x⟫_ℝ ∂B.σ
      = ∫ x, u x * v x * B.ν x i ∂B.σ := by
    congr 1
    ext x
    rw [real_inner_smul_left, EuclideanSpace.inner_single_left, conj_trivial, one_mul]
  -- the interior term
  obtain ⟨hu₁, -, ⟨u', hu'c, hu'e⟩⟩ := contDiffOnClosure_one_iff.1 hu'
  obtain ⟨hv₁, -, ⟨v', hv'c, hv'e⟩⟩ := contDiffOnClosure_one_iff.1 hv'
  have hE₁ : EqOn (fun x ↦ u' x (EuclideanSpace.single i 1) * v x)
      (fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1) * v x)
      (Ω : Set (EuclideanSpace ℝ (Fin N))) := fun x hx ↦ by
    simp only [hu'e hx]
  have hE₂ : EqOn (fun x ↦ u x * v' x (EuclideanSpace.single i 1))
      (fun x ↦ u x * fderiv ℝ v x (EuclideanSpace.single i 1))
      (Ω : Set (EuclideanSpace ℝ (Fin N))) := fun x hx ↦ by
    simp only [hv'e hx]
  have hI₁ : IntegrableOn (fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1) * v x)
      (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
    (B.integrableOn_of_continuousOn ((hu'c.clm_apply continuousOn_const).mul hv)).congr_fun hE₁
      hΩ.measurableSet
  have hI₂ : IntegrableOn (fun x ↦ u x * fderiv ℝ v x (EuclideanSpace.single i 1))
      (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
    (B.integrableOn_of_continuousOn (hu.mul (hv'c.clm_apply continuousOn_const))).congr_fun hE₂
      hΩ.measurableSet
  have hL : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      EuclideanSpace.div (fun x ↦ (u x * v x) • EuclideanSpace.single i (1 : ℝ)) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (fderiv ℝ u x (EuclideanSpace.single i 1) * v x
          + u x * fderiv ℝ v x (EuclideanSpace.single i 1)) := by
    refine setIntegral_congr_fun hΩ.measurableSet fun x hx ↦ ?_
    have hux : DifferentiableAt ℝ u x :=
      (hu₁.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hx)
    have hvx : DifferentiableAt ℝ v x :=
      (hv₁.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hx)
    rw [EuclideanSpace.div_const_smul_single (u := fun y ↦ u y * v y) (hux.mul hvx),
      fderiv_fun_mul hux hvx]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hR, hL, integral_add hI₁ hI₂] at hdiv
  exact hdiv

/-- The inverse Riesz map of `ℝ^N`, `(toDualReal _).symm`, locally. -/
local notation "𝓡⁻¹" =>
  LinearIsometryEquiv.symm (InnerProductSpace.toDualReal (EuclideanSpace ℝ (Fin N)))

/-- **Green's second-order formula for classical functions** ([brezis2011functional] §9.5
Example 4 Step A; QSS (12.95); Atkinson–Han §7.6): for `u ∈ C²(Ω̄)` whose derivative extends
continuously to `Ω̄` as `g`, and `v ∈ C¹(Ω̄)`,
`∫_Ω Δu v + ∫_Ω ⟪∇u, ∇v⟫ = ∫ g(ν) v dσ`. The divergence theorem for `F = v (toDual)⁻¹ g`, which
is `v ∇u` on `Ω`. The boundary values of `∇u` are those of the extension `g`: a function of class
`C²(Ω̄)` in the sense of `ContDiffOnClosure` has no derivative of its own on `∂Ω`. -/
theorem integral_laplacian_mul_add_eq {u v : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu' : ContDiffOnClosure ℝ 2 u (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hg : ContinuousOn g (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hge : EqOn g (fderiv ℝ u) (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hv : ContinuousOn v (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hv' : ContDiffOnClosure ℝ 1 v (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), Δ u x * v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ⟪gradient u x, gradient v x⟫_ℝ
      = ∫ x, g x (B.ν x) * v x ∂B.σ := by
  have hΩ := Ω.isOpen
  have hF : ContDiffOnClosure ℝ 1
      (fun x ↦ v x • 𝓡⁻¹ (g x)) (Ω : Set _) :=
    hv'.smul hΩ (hu'.toDual_symm_of_eqOn_fderiv hΩ hg hge)
  have hFc : ContinuousOn (fun x ↦ v x • 𝓡⁻¹ (g x))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    hv.smul (𝓡⁻¹.continuous.comp_continuousOn hg)
  have hdiv := B.integral_div_eq _ hFc hF
  -- the boundary term
  have hR : ∫ x, ⟪v x • 𝓡⁻¹ (g x), B.ν x⟫_ℝ ∂B.σ
      = ∫ x, g x (B.ν x) * v x ∂B.σ := by
    congr 1
    ext x
    rw [real_inner_smul_left, InnerProductSpace.toDualReal_symm_apply,
      InnerProductSpace.toDual_symm_apply, mul_comm]
  -- the interior term, pointwise
  obtain ⟨hu₁, -, ⟨u', hu'c, hu'e⟩⟩ := contDiffOnClosure_one_iff.1 (hu'.of_le (by norm_num))
  obtain ⟨hv₁, -, ⟨v', hv'c, hv'e⟩⟩ := contDiffOnClosure_one_iff.1 hv'
  obtain ⟨G, hGc, hGe⟩ := hu'.exists_continuousOn_fderiv_fderiv
  have hgrad : gradient u = fun y ↦ 𝓡⁻¹ (fderiv ℝ u y) := rfl
  have hgradv : gradient v = fun y ↦ 𝓡⁻¹ (fderiv ℝ v y) := rfl
  have hL : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      EuclideanSpace.div (fun x ↦ v x • 𝓡⁻¹ (g x)) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (Δ u x * v x + ⟪gradient u x, gradient v x⟫_ℝ) := by
    refine setIntegral_congr_fun hΩ.measurableSet fun x hx ↦ ?_
    have hvx : DifferentiableAt ℝ v x :=
      (hv₁.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hx)
    have hdx : DifferentiableAt ℝ (fderiv ℝ u) x :=
      ((hu'.1.fderiv_of_isOpen hΩ (by norm_num)).differentiableOn one_ne_zero).differentiableAt
        (hΩ.mem_nhds hx)
    have hgx : DifferentiableAt ℝ (gradient u) x := by
      rw [hgrad]
      exact 𝓡⁻¹.toContinuousLinearEquiv.differentiableAt.comp x
        hdx
    have heq : (fun y ↦ v y • 𝓡⁻¹ (g y))
        =ᶠ[𝓝 x] fun y ↦ v y • gradient u y := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      rw [hge hy, hgrad]
    have h1 : EuclideanSpace.div (fun y ↦ v y • 𝓡⁻¹ (g y)) x
        = EuclideanSpace.div (fun y ↦ v y • gradient u y) x := by
      simp only [EuclideanSpace.div, heq.fderiv_eq]
    rw [h1, EuclideanSpace.div_smul_fun hvx hgx, EuclideanSpace.div_gradient_eq_laplacian,
      real_inner_comm]
    ring
  -- integrability of the two summands
  have hI₁ : IntegrableOn (fun x ↦ Δ u x * v x) (Ω : Set (EuclideanSpace ℝ (Fin N))) := by
    have hc : ContinuousOn (fun x ↦ (∑ i, G x (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)) * v x) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      (continuousOn_finsetSum _ fun i _ ↦
        (hGc.clm_apply continuousOn_const).clm_apply continuousOn_const).mul hv
    refine (B.integrableOn_of_continuousOn hc).congr_fun (fun x hx ↦ ?_) hΩ.measurableSet
    simp only [EuclideanSpace.laplacian_eq_sum_fderiv_fderiv_single, hGe hx]
  have hI₂ : IntegrableOn (fun x ↦ ⟪gradient u x, gradient v x⟫_ℝ)
      (Ω : Set (EuclideanSpace ℝ (Fin N))) := by
    have hc : ContinuousOn (fun x ↦ ⟪𝓡⁻¹ (g x),
        𝓡⁻¹ (v' x)⟫_ℝ)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      (𝓡⁻¹.continuous.comp_continuousOn hg).inner
        (𝓡⁻¹.continuous.comp_continuousOn hv'c)
    refine (B.integrableOn_of_continuousOn hc).congr_fun (fun x hx ↦ ?_) hΩ.measurableSet
    simp only [hgrad, hgradv, hge hx, hv'e hx]
  rw [hR, hL, integral_add hI₁ hI₂] at hdiv
  exact hdiv

/-- Green's second-order formula in the form of the books, for `u ∈ C²(Ω̄)` whose derivative is
continuous on `Ω̄`: `∫_Ω Δu v + ∫_Ω ⟪∇u, ∇v⟫ = ∫ ⟪∇u, ν⟫ v dσ`. -/
theorem integral_laplacian_mul_add_eq_of_continuousOn_fderiv {u v : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : ContinuousOn (fderiv ℝ u) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hu' : ContDiffOnClosure ℝ 2 u (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hv : ContinuousOn v (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hv' : ContDiffOnClosure ℝ 1 v (Ω : Set (EuclideanSpace ℝ (Fin N)))) :
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), Δ u x * v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ⟪gradient u x, gradient v x⟫_ℝ
      = ∫ x, ⟪gradient u x, B.ν x⟫_ℝ * v x ∂B.σ := by
  rw [B.integral_laplacian_mul_add_eq hu' hu (fun _ _ ↦ rfl) hv hv']
  congr 1
  ext x
  rw [gradient, InnerProductSpace.toDual_symm_apply]

end BoundaryData

/-! ### The weak Laplacian of an `H²` weak solution -/

namespace Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The standard basis of `ℝ^N`, locally. -/
local notation "𝔅" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **The form of `−Δ + 1` on an `H²` function against a test function is the integral of
`(−Δ_w u + u) φ`**, where `Δ_w u = ∑ᵢ ∂ᵢ(∂ᵢu)` is the weak Laplacian (the twin of
`Elliptic.laplaceForm_eq_integral_of_contDiffOn` for `u ∈ H²(Ω)` rather than `u ∈ C²(Ω)`):
integration by parts of `∂ᵢu ∈ H¹(Ω)` against `φ`. -/
theorem laplaceForm_toLowerOrderL_eq_integral (u : SobolevEuclidean N 2 2 Ω)
    {V : SobolevEuclidean N 1 2 Ω} {φ : 𝓓(Ω, ℝ)}
    (hV : SobolevMultiIndex.fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) :
    laplaceForm Ω (SobolevMultiIndex.toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num) u) V
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-(∑ i, (SobolevMultiIndex.weakDeriv
          (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
            EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x) * φ x := by
  have hUi : ∀ i : Fin N, (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) u)
        (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      = SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) := fun i ↦ rfl
  have hU0 : (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) u) 0 :
        EuclideanSpace ℝ (Fin N) → ℝ) = SobolevMultiIndex.fn u := rfl
  rw [laplaceForm_apply_inner]
  simp only [L2.inner_eq_integral_mul, hUi, hU0]
  -- `∂ᵢV = ∂ᵢφ` a.e., and integration by parts of `∂ᵢu ∈ H¹` against `φ`
  have hVd : ∀ i : Fin N, (SobolevMultiIndex.weakDeriv V (MultiIndexLE.single i) :
      EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) := fun i ↦ by
    have := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hV i
    rwa [EuclideanSpace.basisFun_toBasis_apply] at this
  have hibp : ∀ i : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) : EuclideanSpace ℝ (Fin N) → ℝ) x
        * (SobolevMultiIndex.weakDeriv V (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x * (SobolevMultiIndex.weakDeriv
          (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
            EuclideanSpace ℝ (Fin N) → ℝ) x := fun i ↦ by
    have h := (SobolevMultiIndex.hasWeakIteratedLineDerivOn_single
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) i).integral_smul_eq φ
    rw [SobolevMultiIndex.partialDerivL_apply, SobolevMultiIndex.fn_partialDeriv] at h
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one,
      neg_one_mul, EuclideanSpace.basisFun_toBasis_apply] at h
    rw [← SobolevMultiIndex.partialDerivL_apply] at h
    have h' : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), fderiv ℝ φ x (EuclideanSpace.single i 1)
        * (SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) :
            EuclideanSpace ℝ (Fin N) → ℝ) x
        = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x * (SobolevMultiIndex.weakDeriv
            (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
              EuclideanSpace ℝ (Fin N) → ℝ) x := h
    rw [← h']
    refine integral_congr_ae ?_
    filter_upwards [hVd i] with x hx
    rw [hx, mul_comm]
  -- integrability of the pieces
  have hφ2 : MemLp (φ : EuclideanSpace ℝ (Fin N) → ℝ) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).restrict _
  have hI1 : ∀ i : Fin N, Integrable (fun x ↦ φ x * (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    hφ2.integrable_mul (Lp.memLp _)
  have hI2 : Integrable (fun x ↦ φ x * SobolevMultiIndex.fn u x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    hφ2.integrable_mul (Lp.memLp (SobolevMultiIndex.weakDeriv u 0))
  have hIneg : Integrable (fun x ↦ -(∑ i, φ x * (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (integrable_finsetSum _ fun i _ ↦ hI1 i).neg
  -- assemble
  have e2 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), SobolevMultiIndex.fn u x
      * (SobolevMultiIndex.weakDeriv V 0 : EuclideanSpace ℝ (Fin N) → ℝ) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x * SobolevMultiIndex.fn u x := by
    refine integral_congr_ae ?_
    filter_upwards [hV] with x hx
    rw [SobolevMultiIndex.weakDeriv_zero, hx, mul_comm]
  have e3 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-(∑ i, (SobolevMultiIndex.weakDeriv
        (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
          EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x) * φ x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-(∑ i, φ x * (SobolevMultiIndex.weakDeriv
          (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
            EuclideanSpace ℝ (Fin N) → ℝ) x) + φ x * SobolevMultiIndex.fn u x) := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [add_mul, neg_mul, Finset.sum_mul]
    simp only [mul_comm _ (φ x)]
  simp_rw [hibp]
  rw [e2, e3, integral_add hIneg hI2, integral_neg, integral_finsetSum _ fun i _ ↦ hI1 i]
  simp only [Finset.sum_neg_distrib]

/-- **An `H²` weak solution of `−Δu + u = f` satisfies the equation almost everywhere**, with the
weak Laplacian `Δ_w u = ∑ᵢ ∂ᵢ(∂ᵢu)`: if `∫_Ω ∇u·∇φ + ∫_Ω u φ = ∫_Ω f φ` for every test
function `φ`, then `−Δ_w u + u = f` a.e. on `Ω` (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`
on the residual, which lies in `L²(Ω)`). -/
theorem neg_weakLaplacian_add_ae_eq_of_forall_laplaceForm_eq (u : SobolevEuclidean N 2 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hu : ∀ φ ∈ SobolevMultiIndex.testFunctions ℝ 𝔅 1 2 Ω volume, laplaceForm Ω
      (SobolevMultiIndex.toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num) u) φ = load Ω f φ) :
    (fun x ↦ -(∑ i, (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] f := by
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hLw : MemLp (fun x ↦ ∑ i, (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    memLp_finsetSum _ fun i _ ↦ Lp.memLp _
  have hres : MemLp (fun x ↦ -(∑ i, (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x - f x) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (hLw.neg.add (Lp.memLp (SobolevMultiIndex.weakDeriv u 0))).sub (Lp.memLp f)
  have hloc := hres.locallyIntegrableOn (by norm_num)
  have key := hΩo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc
    fun g hg hgc hgs ↦ ?_
  · have h := (ae_restrict_iff' hΩm).2 key
    filter_upwards [h] with x hx
    exact sub_eq_zero.1 hx
  obtain ⟨φ, hφg⟩ : ∃ φ : 𝓓(Ω, ℝ), (φ : EuclideanSpace ℝ (Fin N) → ℝ) = g :=
    ⟨⟨g, hg, hgc, hgs⟩, rfl⟩
  obtain ⟨V, hVT, hV⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := 𝔅) (k := 1) (p := 2) (μ := volume)
  have h1 := hu V hVT
  rw [laplaceForm_toLowerOrderL_eq_integral u hV, load_apply] at h1
  have hg0 : ∀ x, x ∉ (Ω : Set (EuclideanSpace ℝ (Fin N))) → g x = 0 := fun x hx ↦ by
    rw [← hφg]
    exact φ.eq_zero_of_notMem hx
  have e4 := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (f := fun x ↦ g x • (-(∑ i, (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x - f x))
    (fun x hx ↦ by simp only [hg0 x hx, zero_smul])
  have hφ2 : MemLp (φ : EuclideanSpace ℝ (Fin N) → ℝ) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).restrict _
  have hI1 : Integrable (fun x ↦ (-(∑ i, (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x) * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (hLw.neg.add (Lp.memLp (SobolevMultiIndex.weakDeriv u 0))).integrable_mul hφ2
  have hI2 : Integrable (fun x ↦ f x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (Lp.memLp f).integrable_mul hφ2
  have e5 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x • (-(∑ i,
      (SobolevMultiIndex.weakDeriv (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u)
        (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x)
        + SobolevMultiIndex.fn u x - f x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ((-(∑ i, (SobolevMultiIndex.weakDeriv
          (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
            EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x) * φ x - f x * φ x) := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [smul_eq_mul, ← hφg]
    ring
  have e6 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn V x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * φ x :=
    integral_congr_ae (hV.mono fun x hx ↦ by simp only [hx])
  rw [e6] at h1
  rw [← e4, e5, integral_sub hI1 hI2, h1, sub_self]

end Elliptic

/-! ### The trace and Green's formula, as a structure -/

namespace BoundaryData

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The trace theorem and Green's formula on `Ω`**, as a structure over `B : BoundaryData Ω` —
the shape every consumer of a trace uses; the two instances are `IsContDiffDomain.traceFamily` and
`Triangulation.traceFamily`:

* `traceL p hp : W^{1,p}(Ω) →L L^p(σ)`, the trace operator at every finite exponent
  (Atkinson–Han Theorem 7.3.10 (b), Grisvard Theorem 1.5.1.3 with target `L^p(Γ)`);
* `traceL_ae_eq`: the trace of a function continuous up to the boundary is its restriction
  (Theorem 7.3.10 (a));
* `green`: Green's formula `∫_Ω ∂ᵢu v + ∫_Ω u ∂ᵢv = ∫ (Tu)(Tv) νᵢ dσ` at conjugate exponents
  `1 < p, q < ∞` (Grisvard Theorem 1.5.3.1, Atkinson–Han (7.6.1) and (7.6.3),
  [brezis2011functional] Comments on chapter 9, 7 (iii));
* `green_contDiff`: Green's formula against a fixed compactly supported `C¹` test function, valid
  at `p = 1` too, the form the piecewise-Sobolev membership theorem (Atkinson–Han Example 7.2.7)
  uses.

Green's formula is a field rather than a theorem because on a polygon it is proved by summing over
the triangles (`Triangulation.green`), not by density on `Ω`. -/
structure TraceFamily (B : BoundaryData Ω) where
  /-- The trace operator at every finite exponent `1 ≤ p < ∞`. -/
  traceL : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → (SobolevEuclidean N 1 p Ω →L[ℝ] Lp ℝ p B.σ)
  /-- The trace of a function continuous up to the boundary is its restriction. -/
  traceL_ae_eq : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p Ω)
    (ũ : EuclideanSpace ℝ (Fin N) → ℝ),
    SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ →
    ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
    (traceL p hp u : EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[B.σ] ũ
  /-- Green's formula for Sobolev functions at conjugate exponents. -/
  green : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (u : SobolevEuclidean N 1 p Ω) (v : SobolevEuclidean N 1 q Ω)
    (i : Fin N),
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x
          * SobolevMultiIndex.fn v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), SobolevMultiIndex.fn u x
          * (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x
      = ∫ x, (traceL p hp u : EuclideanSpace ℝ (Fin N) → ℝ) x
          * (traceL q hq v : EuclideanSpace ℝ (Fin N) → ℝ) x * B.ν x i ∂B.σ
  /-- Green's formula against a fixed compactly supported `C¹` test function, at every
  `1 ≤ p < ∞`. -/
  green_contDiff : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p Ω)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ i : Fin N,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x
          * φ x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), SobolevMultiIndex.fn u x
          * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (traceL p hp u : EuclideanSpace ℝ (Fin N) → ℝ) x * φ x * B.ν x i ∂B.σ

namespace TraceFamily

variable {B : BoundaryData Ω} (𝒯 : B.TraceFamily)

/-- **`W_0^{1,p}(Ω) ⊆ ker T`**: the trace of an element of `W_0^{1,p}(Ω)`, `1 ≤ p < ∞`, vanishes
(the easy half of [brezis2011functional] Comments on chapter 9, 7 (ii); the converse is
`Boundary/Kernel.lean`). A test function vanishes on `∂Ω`, so its trace is zero by `traceL_ae_eq`,
and the trace is continuous on the closure `W_0^{1,p}(Ω)` of the test functions. -/
theorem traceL_eq_zero_of_mem_zero {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : SobolevEuclidean N 1 p Ω} (hu : u ∈ SobolevEuclideanZero N 1 p Ω) :
    𝒯.traceL p hp u = 0 := by
  refine SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions (f := fun u ↦ 𝒯.traceL p hp u)
    (g := fun _ ↦ 0) (𝒯.traceL p hp).continuous continuous_const (fun v ⟨φ, hφ⟩ ↦ ?_) hu
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  have h := 𝒯.traceL_ae_eq p hp v φ hφ φ.continuous.continuousOn
  filter_upwards [h, B.ae_notMem] with x hx hxΩ
  rw [hx, Pi.zero_apply]
  exact φ.zero_on_compl hxΩ

/-- **The normal derivative of an `H²` function on the boundary**,
[brezis2011functional] Comments on chapter 9, 7 (iii): `∂u/∂ν := ∑ᵢ νᵢ T(∂ᵢu)` with
`∂ᵢu ∈ H¹(Ω)` the typed partial derivative `SobolevMultiIndex.partialDerivL`. -/
def normalTrace (u : SobolevEuclidean N 2 2 Ω) : EuclideanSpace ℝ (Fin N) → ℝ :=
  fun x ↦ ∑ i, B.ν x i * (𝒯.traceL 2 ENNReal.ofNat_ne_top
    (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i u) :
      EuclideanSpace ℝ (Fin N) → ℝ) x

/-- The normal derivative of an `H²` function lies in `L²(σ)`. -/
theorem memLp_normalTrace (u : SobolevEuclidean N 2 2 Ω) : MemLp (𝒯.normalTrace u) 2 B.σ :=
  memLp_finsetSum _ fun i _ ↦ B.memLp_ν_apply_mul (Lp.memLp _) i

/-- The normal derivative is additive, `σ`-a.e. -/
theorem normalTrace_add (u v : SobolevEuclidean N 2 2 Ω) :
    𝒯.normalTrace (u + v) =ᵐ[B.σ] 𝒯.normalTrace u + 𝒯.normalTrace v := by
  have h : ∀ i : Fin N, ∀ᵐ x ∂B.σ, (𝒯.traceL 2 ENNReal.ofNat_ne_top
      (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i
        (u + v)) : EuclideanSpace ℝ (Fin N) → ℝ) x
      = (𝒯.traceL 2 ENNReal.ofNat_ne_top (SobolevMultiIndex.partialDerivL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i u) :
            EuclideanSpace ℝ (Fin N) → ℝ) x
        + (𝒯.traceL 2 ENNReal.ofNat_ne_top (SobolevMultiIndex.partialDerivL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i v) :
            EuclideanSpace ℝ (Fin N) → ℝ) x := fun i ↦ by
    rw [map_add, map_add]
    exact Lp.coeFn_add _ _
  filter_upwards [ae_all_iff.2 h] with x hx
  simp only [normalTrace, Pi.add_apply, hx, mul_add, Finset.sum_add_distrib]

/-- The normal derivative is homogeneous, `σ`-a.e. -/
theorem normalTrace_smul (c : ℝ) (u : SobolevEuclidean N 2 2 Ω) :
    𝒯.normalTrace (c • u) =ᵐ[B.σ] c • 𝒯.normalTrace u := by
  have h : ∀ i : Fin N, ∀ᵐ x ∂B.σ, (𝒯.traceL 2 ENNReal.ofNat_ne_top
      (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i
        (c • u)) : EuclideanSpace ℝ (Fin N) → ℝ) x
      = c * (𝒯.traceL 2 ENNReal.ofNat_ne_top (SobolevMultiIndex.partialDerivL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i u) :
            EuclideanSpace ℝ (Fin N) → ℝ) x := fun i ↦ by
    rw [map_smul, map_smul]
    exact (Lp.coeFn_smul _ _).mono fun x hx ↦ by rw [hx]; rfl
  filter_upwards [ae_all_iff.2 h] with x hx
  simp only [normalTrace, Pi.smul_apply, hx, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Green's formula for `u ∈ H²(Ω)`, `v ∈ H¹(Ω)`** ([brezis2011functional] Comments on
chapter 9, 7 (iii); Atkinson–Han (7.6.4)):
`∫_Ω (∑ᵢ ∂ᵢ∂ᵢu) v + ∫_Ω ∑ᵢ ∂ᵢu ∂ᵢv = ∫ (∂u/∂ν) (Tv) dσ`, the first integrand being the weak
Laplacian. Green's formula `green` at `p = q = 2` for each `∂ᵢu` and `v`, summed over `i`. -/
theorem green_laplacian (u : SobolevEuclidean N 2 2 Ω) (v : SobolevEuclidean N 1 2 Ω) :
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (∑ i, (SobolevMultiIndex.weakDeriv
        (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume
          i u) (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x)
        * SobolevMultiIndex.fn v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i,
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) : EuclideanSpace ℝ (Fin N) → ℝ) x
          * (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) :
              EuclideanSpace ℝ (Fin N) → ℝ) x
      = ∫ x, 𝒯.normalTrace u x
          * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : EuclideanSpace ℝ (Fin N) → ℝ) x ∂B.σ := by
  have hg : ∀ i : Fin N, (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (SobolevMultiIndex.weakDeriv (SobolevMultiIndex.partialDerivL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i u) (MultiIndexLE.single i) :
          EuclideanSpace ℝ (Fin N) → ℝ) x * SobolevMultiIndex.fn v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) : EuclideanSpace ℝ (Fin N) → ℝ) x
          * (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) :
              EuclideanSpace ℝ (Fin N) → ℝ) x
      = ∫ x, B.ν x i * (𝒯.traceL 2 ENNReal.ofNat_ne_top (SobolevMultiIndex.partialDerivL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i u) :
            EuclideanSpace ℝ (Fin N) → ℝ) x
          * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : EuclideanSpace ℝ (Fin N) → ℝ) x ∂B.σ := fun i ↦ by
    have h := 𝒯.green 2 2 ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top
      (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume
        i u) v i
    have h2 : SobolevMultiIndex.fn (SobolevMultiIndex.partialDerivL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i u)
        = SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) :=
      SobolevMultiIndex.fn_partialDeriv i u
    rw [h2] at h
    refine h.trans (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))
    ring
  -- integrability of the summands
  have hI₁ : ∀ i : Fin N, Integrable (fun x ↦ (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume
        i u) (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x * SobolevMultiIndex.fn v x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    (Lp.memLp _).integrable_mul (Lp.memLp (SobolevMultiIndex.weakDeriv v 0))
  have hI₂ : ∀ i : Fin N, Integrable (fun x ↦
      (SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) : EuclideanSpace ℝ (Fin N) → ℝ) x
        * (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) :
            EuclideanSpace ℝ (Fin N) → ℝ) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hI₃ : ∀ i : Fin N, Integrable (fun x ↦ B.ν x i * (𝒯.traceL 2 ENNReal.ofNat_ne_top
      (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume
        i u) : EuclideanSpace ℝ (Fin N) → ℝ) x
      * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : EuclideanSpace ℝ (Fin N) → ℝ) x) B.σ := fun i ↦
    (B.memLp_ν_apply_mul (Lp.memLp _) i).integrable_mul (Lp.memLp _)
  calc (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (∑ i, (SobolevMultiIndex.weakDeriv
        (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume
          i u) (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x)
        * SobolevMultiIndex.fn v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i,
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) : EuclideanSpace ℝ (Fin N) → ℝ) x
          * (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) :
              EuclideanSpace ℝ (Fin N) → ℝ) x
      = ∑ i, ((∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (SobolevMultiIndex.weakDeriv
          (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω
            volume i u) (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x
          * SobolevMultiIndex.fn v x)
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          (SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) :
            EuclideanSpace ℝ (Fin N) → ℝ) x
            * (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) :
                EuclideanSpace ℝ (Fin N) → ℝ) x) := by
        simp_rw [Finset.sum_mul]
        rw [integral_finsetSum _ fun i _ ↦ hI₁ i, integral_finsetSum _ fun i _ ↦ hI₂ i,
          Finset.sum_add_distrib]
    _ = ∑ i, ∫ x, B.ν x i * (𝒯.traceL 2 ENNReal.ofNat_ne_top (SobolevMultiIndex.partialDerivL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i u) :
            EuclideanSpace ℝ (Fin N) → ℝ) x
          * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : EuclideanSpace ℝ (Fin N) → ℝ) x ∂B.σ :=
        Finset.sum_congr rfl fun i _ ↦ hg i
    _ = ∫ x, 𝒯.normalTrace u x
          * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : EuclideanSpace ℝ (Fin N) → ℝ) x ∂B.σ := by
        rw [← integral_finsetSum _ fun i _ ↦ hI₃ i]
        congr 1
        ext x
        simp only [normalTrace, Finset.sum_mul]

/-- The standard basis of `ℝ^N`, locally. -/
local notation "𝔅" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **The Neumann boundary condition of an `H²` weak solution** — the clause of
[brezis2011functional] Theorem 9.26 that has no meaning without a trace: if `u ∈ H²(Ω)` is a
weak solution of the Neumann problem `−Δu + u = f` ((49) of §9.6, read on its `H¹` shadow:
`∫_Ω ∇u·∇φ + ∫_Ω u φ = ∫_Ω f φ` for every `φ ∈ H¹(Ω)`), then `∂u/∂ν = 0` `σ`-a.e. Against test
functions the weak equation says `−Δ_w u + u = f` a.e. on `Ω`
(`Elliptic.neg_weakLaplacian_add_ae_eq_of_forall_laplaceForm_eq`); against `φ ∈ C_c^∞(ℝ^N)`,
Green's formula `green_laplacian` then leaves `∫ (∂u/∂ν) φ dσ = 0`, and `∂u/∂ν ∈ L²(σ)` vanishes
a.e. (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem normalTrace_eq_zero_of_forall_laplaceForm_eq (u : SobolevEuclidean N 2 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hu : ∀ φ : SobolevEuclidean N 1 2 Ω, Elliptic.laplaceForm Ω
      (SobolevMultiIndex.toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num) u) φ = Elliptic.load Ω f φ) :
    𝒯.normalTrace u =ᵐ[B.σ] 0 := by
  have hUi : ∀ i : Fin N, (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) u)
        (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      = SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) := fun i ↦ rfl
  have hU0 : SobolevMultiIndex.fn
      (SobolevMultiIndex.toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) u)
      = SobolevMultiIndex.fn u := rfl
  have hLw : MemLp (fun x ↦ ∑ i, (SobolevMultiIndex.weakDeriv
      (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    memLp_finsetSum _ fun i _ ↦ Lp.memLp _
  have hzero := Elliptic.neg_weakLaplacian_add_ae_eq_of_forall_laplaceForm_eq u f fun φ _ ↦ hu φ
  -- Green's formula against a smooth compactly supported `ψ`
  have hgreen : ∀ ψ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      HasCompactSupport ψ →
      ∫ x, ψ x • 𝒯.normalTrace u x ∂B.σ = 0 := by
    intro ψ hψ hψc
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    obtain ⟨W, hW⟩ := hψ1.exists_sobolevMultiIndex_of_hasCompactSupport'
      (b := 𝔅) (p := 2) (Ω := Ω) (μ := volume) hψc
    have hG := 𝒯.green_laplacian u W
    have h1 := hu W
    rw [Elliptic.laplaceForm_apply, Elliptic.load_apply] at h1
    simp only [hUi, hU0] at h1
    have hT := 𝒯.traceL_ae_eq 2 ENNReal.ofNat_ne_top W ψ hW hψ.continuous.continuousOn
    -- integrability
    have hI1 : Integrable (fun x ↦ (∑ i, (SobolevMultiIndex.weakDeriv
        (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
          EuclideanSpace ℝ (Fin N) → ℝ) x) * SobolevMultiIndex.fn W x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      hLw.integrable_mul (Lp.memLp (SobolevMultiIndex.weakDeriv W 0))
    have hI2 : Integrable (fun x ↦ ∑ i, (SobolevMultiIndex.weakDeriv u (MultiIndexLE.singleLE i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x * (SobolevMultiIndex.weakDeriv W (MultiIndexLE.single i) :
          EuclideanSpace ℝ (Fin N) → ℝ) x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      integrable_finsetSum _ fun i _ ↦ (Lp.memLp _).integrable_mul (Lp.memLp _)
    have hI3 : Integrable (fun x ↦ SobolevMultiIndex.fn u x * SobolevMultiIndex.fn W x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      (Lp.memLp (SobolevMultiIndex.weakDeriv u 0)).integrable_mul
        (Lp.memLp (SobolevMultiIndex.weakDeriv W 0))
    rw [integral_add hI2 hI3] at h1
    -- the equation `−Δ_w u + u = f`, integrated against `fn W`
    have hres : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-(∑ i, (SobolevMultiIndex.weakDeriv
        (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
          EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x) * SobolevMultiIndex.fn W x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn W x := by
      refine integral_congr_ae ?_
      filter_upwards [hzero] with x hx
      rw [hx]
    have hIneg : Integrable (fun x ↦ -((∑ i, (SobolevMultiIndex.weakDeriv
        (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
          EuclideanSpace ℝ (Fin N) → ℝ) x) * SobolevMultiIndex.fn W x))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := hI1.neg
    have e : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-(∑ i, (SobolevMultiIndex.weakDeriv
        (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
          EuclideanSpace ℝ (Fin N) → ℝ) x) + SobolevMultiIndex.fn u x) * SobolevMultiIndex.fn W x
        = -(∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (∑ i, (SobolevMultiIndex.weakDeriv
            (SobolevMultiIndex.partialDerivL ℝ 𝔅 2 Ω volume i u) (MultiIndexLE.single i) :
              EuclideanSpace ℝ (Fin N) → ℝ) x) * SobolevMultiIndex.fn W x)
          + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            SobolevMultiIndex.fn u x * SobolevMultiIndex.fn W x := by
      rw [← integral_neg, ← integral_add hIneg hI3]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      ring
    have hzero' : ∫ x, 𝒯.normalTrace u x
        * (𝒯.traceL 2 ENNReal.ofNat_ne_top W : EuclideanSpace ℝ (Fin N) → ℝ) x ∂B.σ = 0 := by
      rw [← hG]
      linarith
    rw [← hzero']
    refine integral_congr_ae ?_
    filter_upwards [hT] with x hx
    rw [hx, smul_eq_mul, mul_comm]
  -- conclude
  have hloc : LocallyIntegrable (𝒯.normalTrace u) B.σ :=
    ((𝒯.memLp_normalTrace u).integrable (by norm_num)).locallyIntegrable
  exact ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hgreen


end TraceFamily

end BoundaryData

/-! ### The epigraph of a function of `d` variables -/

namespace EuclideanSpace

variable {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **The epigraph** `{y : g y' < y_N}` of `g : ℝ^d → ℝ`: the open region strictly above the graph
of `g`, in the coordinate convention of `IsBoundaryGraphAt` (the last coordinate is the one the
boundary is a graph over). -/
def epigraph (g : EuclideanSpace ℝ (Fin d) → ℝ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {y | g (init y) < y (Fin.last d)}

/-- Membership of the epigraph. -/
theorem mem_epigraph {y : EuclideanSpace ℝ (Fin (d + 1))} :
    y ∈ epigraph g ↔ g (init y) < y (Fin.last d) :=
  Iff.rfl

/-- The point `(x', t)` lies in the epigraph iff `g x' < t`. -/
@[simp]
theorem snocLast_mem_epigraph (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    snocLast x' t ∈ epigraph g ↔ g x' < t := by
  simp [mem_epigraph]

/-- The vertical line through `x'` meets the epigraph in the open half-line above `g x'`. -/
theorem epigraph_preimage_snocLast (x' : EuclideanSpace ℝ (Fin d)) :
    (fun t ↦ snocLast x' t) ⁻¹' epigraph g = Ioi (g x') := by
  ext t
  simp

/-- The upper half space is the epigraph of the zero function. -/
theorem upperHalfSpace_eq_epigraph_zero : upperHalfSpace d = epigraph 0 := rfl

/-- **`IsBoundaryGraphAt` in terms of the epigraph**: `Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' epigraph g`
for some rigid motion `T` and some `g ∈ V`. -/
theorem isBoundaryGraphAt_iff {V : Set (EuclideanSpace ℝ (Fin d) → ℝ)}
    {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ} :
    IsBoundaryGraphAt V Ω x₀ r ↔
      ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)), ∃ g ∈ V,
        Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' epigraph g :=
  Iff.rfl

/-- The epigraph of a continuous function is open. -/
theorem isOpen_epigraph (hg : Continuous g) : IsOpen (epigraph g) :=
  isOpen_lt (hg.comp continuous_init) continuous_apply_last

/-- **The closure of the epigraph** of a continuous function is the closed region on or above the
graph: a point on the graph is the limit of the points `(y', y_N + 1/(n+1))` of the epigraph. -/
theorem closure_epigraph (hg : Continuous g) :
    closure (epigraph g) = {y | g (init y) ≤ y (Fin.last d)} := by
  refine Subset.antisymm (closure_lt_subset_le (hg.comp continuous_init) continuous_apply_last)
    fun y (hy : g (init y) ≤ y (Fin.last d)) ↦ ?_
  have ht : Tendsto (fun n : ℕ ↦ snocLast (init y) (y (Fin.last d) + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 y) := by
    have h1 : Tendsto (fun n : ℕ ↦ y (Fin.last d) + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (y (Fin.last d) + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h1
    have h2 : Continuous fun t : ℝ ↦ snocLast (init y) t := by
      change Continuous fun t : ℝ ↦ (lastInitL d).symm (t, init y)
      fun_prop
    have h3 := (h2.tendsto (y (Fin.last d))).comp h1
    rw [snocLast_init_last] at h3
    exact h3
  refine mem_closure_of_tendsto ht (Eventually.of_forall fun n ↦ ?_)
  rw [snocLast_mem_epigraph]
  exact hy.trans_lt (lt_add_of_pos_right _ (by positivity))

/-- The closure of `Ω` near a graph chart lies on or above the graph: if
`Ω ∩ B = B ∩ T ⁻¹' epigraph g` for an open `B`, then `closure Ω ∩ B ⊆ T ⁻¹' {y | g y' ≤ y_N}`. -/
theorem closure_inter_subset_of_inter_eq (hg : Continuous g)
    {T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
    {Ω B : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hB : IsOpen B)
    (h : Ω ∩ B = B ∩ T ⁻¹' epigraph g) :
    closure Ω ∩ B ⊆ T ⁻¹' {y | g (init y) ≤ y (Fin.last d)} := by
  intro x ⟨hx, hxB⟩
  have h1 : x ∈ closure (Ω ∩ B) := hB.closure_inter ⟨hx, hxB⟩
  rw [h] at h1
  have h2 : closure (B ∩ T ⁻¹' epigraph g) ⊆ closure (T ⁻¹' epigraph g) :=
    closure_mono inter_subset_right
  have h3 := h2 h1
  have h4 := T.toHomeomorph.preimage_closure (epigraph g)
  rw [AffineIsometryEquiv.coe_toHomeomorph] at h4
  rw [← h4, closure_epigraph hg] at h3
  exact h3

/-- **The frontier of the epigraph** of a continuous function is the graph of `g`. -/
theorem frontier_epigraph (hg : Continuous g) :
    frontier (epigraph g) = {y | y (Fin.last d) = g (init y)} := by
  rw [(isOpen_epigraph hg).frontier_eq, closure_epigraph hg]
  ext y
  simp only [Set.mem_sdiff, mem_ofPred_eq, mem_epigraph, not_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨h.ge, h.le⟩

/-- The frontier of a rotated epigraph is the rotated graph. -/
theorem frontier_preimage_epigraph (hg : Continuous g)
    (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    frontier (T ⁻¹' epigraph g) = T ⁻¹' {y | y (Fin.last d) = g (init y)} := by
  have h := T.toHomeomorph.preimage_frontier (epigraph g)
  rw [AffineIsometryEquiv.coe_toHomeomorph] at h
  rw [← h, frontier_epigraph hg]

end EuclideanSpace

/-- **The boundary of a locally graphical set is the graph, inside the ball**: if
`Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' epigraph g` with `g` continuous, then
`frontier Ω ∩ B(x₀, r) = B(x₀, r) ∩ T ⁻¹' {y | y_N = g y'}`. The pointwise `⊆` direction is
`IsBoundaryGraphAt.last_eq_of_mem_frontier` of `Chart.lean`. -/
theorem IsBoundaryGraphAt.frontier_inter_ball {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Continuous g) {T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
    {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    frontier Ω ∩ Metric.ball x₀ r
      = Metric.ball x₀ r ∩ T ⁻¹' {y | y (Fin.last d) = g (EuclideanSpace.init y)} := by
  rw [← frontier_inter_open_inter Metric.isOpen_ball, h, inter_comm (Metric.ball x₀ r),
    frontier_inter_open_inter Metric.isOpen_ball, EuclideanSpace.frontier_preimage_epigraph hg,
    inter_comm]

/-! ### Rigid motions preserve Lebesgue measure -/

section AffineIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **A rigid motion preserves Lebesgue measure**: `T x = T.linear x + T 0` is a linear isometry
followed by a translation. -/
theorem AffineIsometryEquiv.measurePreserving (T : E ≃ᵃⁱ[ℝ] F) :
    MeasurePreserving T volume volume := by
  have h : (T : E → F) = fun x ↦ T.linearIsometryEquiv x + T 0 := by
    funext x
    have := T.map_vadd (0 : E) x
    rwa [vadd_eq_add, add_zero, vadd_eq_add] at this
  rw [h]
  exact (measurePreserving_add_right volume (T 0)).comp T.linearIsometryEquiv.measurePreserving

/-- Integrals are invariant under a rigid motion: `∫ f (T x) = ∫ f`. -/
theorem AffineIsometryEquiv.integral_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E ≃ᵃⁱ[ℝ] F) (f : F → G) : ∫ x, f (T x) = ∫ y, f y :=
  T.measurePreserving.integral_comp T.toHomeomorph.measurableEmbedding f

/-- Set integrals are invariant under a rigid motion: `∫_{T ⁻¹' s} f (T x) = ∫_s f`. -/
theorem AffineIsometryEquiv.setIntegral_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E ≃ᵃⁱ[ℝ] F) (f : F → G) (s : Set F) :
    ∫ x in T ⁻¹' s, f (T x) = ∫ y in s, f y :=
  T.measurePreserving.setIntegral_preimage_emb T.toHomeomorph.measurableEmbedding f s

end AffineIsometryEquiv

end
