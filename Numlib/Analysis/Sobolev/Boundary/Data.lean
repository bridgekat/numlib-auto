/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Trace
import Numlib.Analysis.PDE.Elliptic.Dirichlet
import Numlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Boundary data: the surface measure, the outward normal and the divergence theorem

This module gives an abstract interface for the boundary $\partial\Omega$ of an open set
$\Omega \subseteq \mathbb{R}^N$. It defines the divergence
$\operatorname{div} F = \sum_i \partial_i F_i$ of a vector field and the structure `BoundaryData`: a
finite measure $\sigma$ carried by $\partial\Omega$, a unit vector field $\nu$ defined
$\sigma$-almost everywhere, and the divergence theorem
$$\int_\Omega \operatorname{div} F \, dx = \int \langle F, \nu \rangle \, d\sigma$$
for every field $F$ of class $C^1(\overline{\Omega})$. It also defines the structure
`BoundaryData.TraceFamily`: a bounded linear trace $T \colon W^{1,p}(\Omega) \to L^p(\sigma)$ for
every $1 \le p < \infty$ that maps a function continuous on $\overline{\Omega}$ to its restriction,
together with Green's formula
$$\int_\Omega \partial_i u \, v \, dx + \int_\Omega u \, \partial_i v \, dx = \int (Tu)(Tv) \, \nu_i
  \, d\sigma$$
at conjugate exponents. Every result about $\partial\Omega$ in the surface libraries of
[han2009theoretical], [quarteroni2000numerical] and [brezis2011functional] is stated once over these
two structures. The instances are `IsContDiffDomain.boundaryData` and `IsContDiffDomain.traceFamily`
for bounded $C^1$ domains (`Numlib.Analysis.Sobolev.Boundary.ContDiffDomain`), and
`Triangulation.boundaryData` and `Triangulation.traceFamily` for triangulated plane domains
(`Numlib.Analysis.Sobolev.Boundary.Polygon`, `Numlib.Analysis.Sobolev.Boundary.PolygonTrace`).

From the fields alone, the module proves the classical Green formulas for functions in
$C^1(\overline{\Omega})$ and $C^2(\overline{\Omega})$ ([han2009theoretical], §7.6, before the
density argument; [brezis2011functional], §9.5, Example 4, Step A), the inclusion of
$W_0^{1,p}(\Omega)$ in the kernel of the trace, Green's formula for $u \in H^2(\Omega)$ with the
normal derivative $\partial_\nu u = \sum_i \nu_i T(\partial_i u)$ (item 7(iii) of the Comments on
Chapter 9 of [brezis2011functional]), and the Neumann boundary condition of an $H^2$ weak solution
(the part of Theorem 9.26 of [brezis2011functional] that needs a trace). It also defines the
epigraph $\{y : g(y') < y_N\}$ of a function $g$ of $d$ variables, which the graph modules use. The
trace theorems follow [han2009theoretical], §7.3 (Theorem 7.3.10), and [grisvard2011elliptic], §1.5
(Theorems 1.5.1.3 and 1.5.3.1).

## Main definitions

* `EuclideanSpace.div`: the divergence $\operatorname{div} F(x) = \sum_i \partial_i F_i(x)$ of a
  vector field on $\mathbb{R}^N$.
* `BoundaryData`: a surface measure $\sigma$ and a normal $\nu$ with $\Omega$ bounded, $\sigma$
  finite, $\sigma((\partial\Omega)^c) = 0$, $\nu$ measurable with $|\nu| = 1$ $\sigma$-almost
  everywhere, and the divergence theorem.
* `BoundaryData.TraceFamily`: the trace $W^{1,p}(\Omega) \to L^p(\sigma)$ for $1 \le p < \infty$,
  its value on functions continuous on $\overline{\Omega}$, Green's formula at conjugate exponents,
  and Green's formula against a compactly supported $C^1$ test function.
* `BoundaryData.TraceFamily.normalTrace`: the normal derivative
  $\partial_\nu u = \sum_i \nu_i T(\partial_i u)$ of $u \in H^2(\Omega)$.
* `EuclideanSpace.epigraph`: the open region $\{y : g(y') < y_N\}$ strictly above the graph of $g$.

## Main results

* `EuclideanSpace.div_eq_trace`, `EuclideanSpace.div_smul_fun`,
  `EuclideanSpace.div_comp_continuousLinearEquiv`, `EuclideanSpace.div_comp_affineIsometryEquiv`:
  the divergence is the trace of the derivative, satisfies the product rule, and is invariant under
  affine changes of frame.
* `BoundaryData.integral_fderiv_mul_add_eq`, `BoundaryData.integral_laplacian_mul_add_eq`: the
  classical Green formulas.
* `BoundaryData.TraceFamily.traceL_eq_zero_of_mem_zero`: the trace vanishes on $W_0^{1,p}(\Omega)$.
* `BoundaryData.TraceFamily.green_laplacian`: Green's formula for $u \in H^2(\Omega)$ and
  $v \in H^1(\Omega)$.
* `BoundaryData.TraceFamily.normalTrace_eq_zero_of_forall_laplaceForm_eq`: an $H^2$ weak solution of
  the Neumann problem $-\Delta u + u = f$ has $\partial u/\partial\nu = 0$.
* `EuclideanSpace.closure_epigraph`, `EuclideanSpace.frontier_epigraph`,
  `IsBoundaryGraphAt.frontier_inter_ball`: the closure and the boundary of the epigraph of a
  continuous function, and the boundary of a set that is an epigraph inside a ball.

## Implementation notes

* The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)`.
* The open set $\Omega$ is an element of `Opens`.
* The space $W^{1,p}(\Omega)$ is `SobolevEuclidean N 1 p Ω`.
* The function of $u \in W^{1,p}(\Omega)$ is `SobolevMultiIndex.fn u`.
* The weak derivative $\partial_i u$ is `SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)`.
* "$F \in C^1(\overline{\Omega})$" is the pair of hypotheses `ContinuousOn F (closure Ω)` and
  `ContDiffOnClosure ℝ 1 F Ω`.
* The surface measure is a measure on the ambient space, not on a subtype, so $L^p(\partial\Omega)$
  is `Lp ℝ p σ`.
* The structures do not contain a transversal field, because a pinched polygon has none; the trace
  construction of Nečas that uses one is in `Numlib.Analysis.Sobolev.Boundary.Trace`. They do not
  contain the density of smooth functions (`Numlib.Analysis.Sobolev.Boundary.Density`). They contain
  no Hausdorff measure: identifying $\sigma$ with the $(N-1)$-dimensional Hausdorff measure on
  $\partial\Omega$ would need the area formula.
* Boundedness of $\Omega$ is a field: every instance is bounded, and the field spares the divergence
  theorem a hypothesis on the support of $F$.
* The measure preservation of a rigid motion is `AffineIsometryEquiv.measurePreserving` of
  `Numlib.MeasureTheory.Measure.Haar.InnerProductSpace`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Laplacian Topology

noncomputable section

/-! ### The divergence and its calculus -/

namespace EuclideanSpace

variable {N : ℕ}

/-- **The divergence** of a vector field $F \colon \mathbb{R}^N \to \mathbb{R}^N$ at $x$:
$$\operatorname{div} F(x) = \sum_i \partial_i F_i(x) = \sum_i DF(x)(e_i)_i.$$

The form `∑ i, fderiv ℝ F x (single i 1) i` is the form of Mathlib's divergence theorem on a
box. At a point where $F$ is not differentiable, `fderiv` is $0$, so the divergence is $0$. -/
def div (F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    ℝ :=
  ∑ i, fderiv ℝ F x (EuclideanSpace.single i 1) i

variable {F G : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {x : EuclideanSpace ℝ (Fin N)}

/-- If $F$ and $G$ are differentiable at $x$, then $\operatorname{div}(F + G)(x) =
\operatorname{div} F(x) + \operatorname{div} G(x)$. -/
@[simp]
theorem div_add (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    div (F + G) x = div F x + div G x := by
  simp only [div, fderiv_add hF hG, add_apply, PiLp.add_apply, Finset.sum_add_distrib]

/-- $\operatorname{div}(-F)(x) = -\operatorname{div} F(x)$. -/
@[simp]
theorem div_neg : div (-F) x = -div F x := by
  simp only [div, fderiv_neg, neg_apply, PiLp.neg_apply, Finset.sum_neg_distrib]

/-- For $c \in \mathbb{R}$, $\operatorname{div}(cF)(x) = c \operatorname{div} F(x)$. -/
@[simp]
theorem div_smul (c : ℝ) : div (c • F) x = c * div F x := by
  simp only [div, fderiv_const_smul_field, Pi.smul_apply, smul_apply, PiLp.smul_apply,
    smul_eq_mul, Finset.mul_sum]

/-- **The divergence is the trace of the derivative**: $\operatorname{div} F(x) = \operatorname{tr}
DF(x)$. This makes the divergence invariant under changes of frame
(`EuclideanSpace.div_comp_continuousLinearEquiv`). -/
theorem div_eq_trace (F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    div F x = LinearMap.trace ℝ _ (fderiv ℝ F x : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] _) := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
  simp only [div, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
    EuclideanSpace.inner_single_left, conj_trivial, one_mul]

/-- **The product rule for the divergence.** If $\varphi \colon \mathbb{R}^N \to \mathbb{R}$ and
$F \colon \mathbb{R}^N \to \mathbb{R}^N$ are differentiable at $x$, then
$$\operatorname{div}(\varphi F)(x) = \langle \nabla \varphi(x), F(x) \rangle + \varphi(x)
  \operatorname{div} F(x).$$
-/
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

/-- If $u \colon \mathbb{R}^N \to \mathbb{R}$ is differentiable at $x$, then the field $u e_i$ has
divergence $\operatorname{div}(u e_i)(x) = \partial_i u(x)$. This is the form of the product
rule that the classical Green formula `BoundaryData.integral_fderiv_mul_add_eq` uses. -/
theorem div_const_smul_single {u : EuclideanSpace ℝ (Fin N) → ℝ} (hu : DifferentiableAt ℝ u x)
    (i : Fin N) :
    div (fun y ↦ u y • EuclideanSpace.single i 1) x = fderiv ℝ u x (EuclideanSpace.single i 1) := by
  simp only [div, fderiv_smul_const hu, ContinuousLinearMap.smulRight_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- **Affine invariance of the divergence** (the linear Piola identity). Let $M$ be a continuous
linear bijection of $\mathbb{R}^N$, let $b \in \mathbb{R}^N$, and let $F$ be differentiable at
$Mx + b$. Then
$$\operatorname{div}\bigl(z \mapsto M^{-1} F(Mz + b)\bigr)(x) = \operatorname{div} F(Mx + b).$$

By `EuclideanSpace.div_eq_trace`: the derivative of the conjugated field is
$M^{-1} \circ DF \circ M$, and the trace is invariant under conjugation. -/
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

/-- **Rotation invariance of the divergence.** Let $T$ be a rigid motion of $\mathbb{R}^N$ with
linear part $L$, and let $F$ be differentiable at $T^{-1} y$. Then
$$\operatorname{div}\bigl(z \mapsto L F(T^{-1} z)\bigr)(y) = \operatorname{div} F(T^{-1} y).$$
This is the change of frame in the divergence theorem on a graph chart. -/
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

/-- **The divergence of the gradient is the Laplacian**:
$\operatorname{div}(\nabla u)(x) = \Delta u(x)$ for every $u \colon \mathbb{R}^N \to \mathbb{R}$
and every $x$, with no hypothesis of differentiability. -/
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

/-- If the fields $G_i$, $i \in s$, are differentiable at $x$ for a finite set $s$, then
$$\operatorname{div}\Bigl(\sum_{i \in s} G_i\Bigr)(x) = \sum_{i \in s} \operatorname{div}
  G_i(x).$$
-/
theorem div_finset_sum {ι : Type*} (s : Finset ι)
    {G : ι → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {x : EuclideanSpace ℝ (Fin N)}
    (hG : ∀ i ∈ s, DifferentiableAt ℝ (G i) x) :
    div (fun y ↦ ∑ i ∈ s, G i y) x = ∑ i ∈ s, div (G i) x := by
  simp only [div, fderiv_fun_sum hG, sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_comm

/-- For every field $F \colon \mathbb{R}^N \to \mathbb{R}^N$, every vector $v$ and every coordinate
$i$, the function $z \mapsto (DF(z) v)_i$ is measurable. No differentiability of $F$ is assumed. -/
theorem measurable_fderiv_apply_apply (F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    Measurable fun z ↦ fderiv ℝ F z v i :=
  (EuclideanSpace.proj i).continuous.measurable.comp
    ((measurable_fderiv ℝ F).apply_continuousLinearMap v)

/-- The divergence of every field $G \colon \mathbb{R}^N \to \mathbb{R}^N$ is measurable, since
`fderiv` is measurable with no hypothesis. -/
theorem measurable_div (G : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
    Measurable (div G) :=
  Finset.measurable_sum _ fun i _ ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp
      (measurable_fderiv_apply_const ℝ G (EuclideanSpace.single i 1))

/-- If $\|DF(z)\| \le C$, then every partial derivative satisfies $|\partial_i F_j(z)| \le C$. -/
theorem norm_fderiv_apply_apply_le {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {z : EuclideanSpace ℝ (Fin N)} {C : ℝ} (hC : ‖fderiv ℝ F z‖ ≤ C) (i j : Fin N) :
    ‖fderiv ℝ F z (EuclideanSpace.single i 1) j‖ ≤ C :=
  calc ‖fderiv ℝ F z (EuclideanSpace.single i 1) j‖
      ≤ ‖fderiv ℝ F z (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖fderiv ℝ F z‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C := by simpa using hC

/-- For every field $w \colon \mathbb{R}^N \to \mathbb{R}^N$ and every $x$,
$|\operatorname{div} w(x)| \le N \|Dw(x)\|$. -/
theorem abs_div_le (w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) : |EuclideanSpace.div w x| ≤ N * ‖fderiv ℝ w x‖ := by
  unfold EuclideanSpace.div
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ i : Fin N, |fderiv ℝ w x (EuclideanSpace.single i 1) i| ≤ ‖fderiv ℝ w x‖ := fun i ↦ by
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le _ i).trans ?_
    refine ((fderiv ℝ w x).le_opNorm _).trans ?_
    simp
  refine (Finset.sum_le_sum fun i _ ↦ h i).trans ?_
  simp

/-- Let $s \subseteq \mathbb{R}^N$ be bounded and measurable, and let $F$ be of class
$C^1(\overline{s})$ in the sense of `ContDiffOnClosure`. Then every partial derivative
$\partial_i F_j$ is integrable on $s$. -/
theorem integrableOn_fderiv_apply_apply
    {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {s : Set (EuclideanSpace ℝ (Fin N))}
    (hF : ContDiffOnClosure ℝ 1 F s) (hs : Bornology.IsBounded s) (hsm : MeasurableSet s)
    (i j : Fin N) : IntegrableOn (fun z ↦ fderiv ℝ F z (EuclideanSpace.single i 1) j) s := by
  obtain ⟨C, hC⟩ := hF.exists_norm_fderiv_le hs
  refine Measure.integrableOn_of_bounded (M := C) hs.measure_lt_top.ne
    (measurable_fderiv_apply_apply F _ j).aestronglyMeasurable ?_
  rw [ae_restrict_iff' hsm]
  exact Filter.Eventually.of_forall fun z hz ↦ norm_fderiv_apply_apply_le (hC z hz) i j

/-- Let $s \subseteq \mathbb{R}^N$ be bounded and measurable, and let $F$ be of class
$C^1(\overline{s})$ in the sense of `ContDiffOnClosure`. Then $\operatorname{div} F$ is
integrable on $s$. -/
theorem integrableOn_div {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s : Set (EuclideanSpace ℝ (Fin N))} (hF : ContDiffOnClosure ℝ 1 F s)
    (hs : Bornology.IsBounded s) (hsm : MeasurableSet s) : IntegrableOn (div F) s := by
  have : div F = fun z ↦ ∑ i, fderiv ℝ F z (EuclideanSpace.single i 1) i := rfl
  rw [this]
  exact integrable_finsetSum _ fun i _ ↦ integrableOn_fderiv_apply_apply hF hs hsm i i
end EuclideanSpace

/-- **The divergence of a $C^1(\overline{\Omega})$ field is integrable.** Let
$\Omega \subseteq \mathbb{R}^N$ be open and bounded, and let $F$ be of class
$C^1(\overline{\Omega})$ in the sense of `ContDiffOnClosure`. Then $\operatorname{div} F$ is
integrable on $\Omega$. This is `EuclideanSpace.integrableOn_div` for an open set. -/
theorem ContDiffOnClosure.integrableOn_div {N : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin N))}
    {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (hF : ContDiffOnClosure ℝ 1 F Ω) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    IntegrableOn (EuclideanSpace.div F) Ω :=
  EuclideanSpace.integrableOn_div hF hb hΩ.measurableSet

/-! ### The gradient of a $C^2(\overline{s})$ function -/

section Gradient

variable {N : ℕ} {s : Set (EuclideanSpace ℝ (Fin N))}

/-- Local notation for the inverse Riesz map $(\mathbb{R}^N)^* \to \mathbb{R}^N$,
`(InnerProductSpace.toDualReal _).symm`. -/
local notation "𝓡⁻¹" =>
  LinearIsometryEquiv.symm (InnerProductSpace.toDualReal (EuclideanSpace ℝ (Fin N)))

/-- **The gradient of a $C^2(\overline{s})$ function is of class $C^1(\overline{s})$.** Let
$s \subseteq \mathbb{R}^N$ be open, let $u$ be of class $C^2(\overline{s})$ in the sense of
`ContDiffOnClosure`, and let $g$ be continuous on $\overline{s}$ with $g = Du$ on $s$. Then the
vector field $x \mapsto R^{-1}(g(x))$ is of class $C^1(\overline{s})$, where $R^{-1}$ is the
inverse Riesz map of $\mathbb{R}^N$.

On $s$ this field is $\nabla u$. Its derivative $R^{-1} \circ D^2 u$ extends continuously to
$\overline{s}$ by the clause of order $2$ of `ContDiffOnClosure`. -/
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

/-! ### The boundary data of an open set -/

/-- **The boundary data of an open set** $\Omega \subseteq \mathbb{R}^N$. An element consists of a
surface measure $\sigma$ on $\mathbb{R}^N$ carried by $\partial\Omega$, an outward unit normal
$\nu$ defined $\sigma$-almost everywhere, and the following properties: $\Omega$ is bounded,
$\sigma$ is finite, $\nu$ is measurable with $|\nu| = 1$ $\sigma$-almost everywhere, and the
divergence theorem (Gauss–Green)
$$\int_\Omega \operatorname{div} F \, dx = \int \langle F, \nu \rangle \, d\sigma$$
holds for every field $F$ of class $C^1(\overline{\Omega})$: $F$ is continuous on
$\overline{\Omega}$, $C^1$ on $\Omega$, and its derivative extends continuously to
$\overline{\Omega}$.

This is the regularity of the books ([han2009theoretical], §7.6; [quarteroni2000numerical],
(12.95); [brezis2011functional], §9.5, Example 4). The case of $C^1$ fields on $\mathbb{R}^N$ is
the corollary `BoundaryData.integral_div_eq_of_contDiff`. The surface measure is a measure on
the ambient space, not on a subtype, so $L^p(\partial\Omega)$ is `Lp ℝ p σ`. The instances are
`IsContDiffDomain.boundaryData` (bounded $C^1$ graph domains), `Triangulation.boundaryData`
(triangulated plane domains) and `EuclideanSpace.triangleBoundaryData` (a single triangle).
`BoundaryData` is not a class: a domain can have several descriptions, and the theorems take the
data explicitly. -/
structure BoundaryData {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N))) where
  /-- The surface measure, a measure on $\mathbb{R}^N$ carried by $\partial\Omega$. -/
  σ : Measure (EuclideanSpace ℝ (Fin N))
  /-- The outward unit normal, a function on $\mathbb{R}^N$ that is meaningful $\sigma$-almost
  everywhere. -/
  ν : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)
  /-- The set $\Omega$ is bounded. -/
  isBounded : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))
  /-- The surface measure is finite. -/
  isFiniteMeasure : IsFiniteMeasure σ
  /-- The surface measure is carried by $\partial\Omega$: $\sigma((\partial\Omega)^c) = 0$. -/
  measure_compl_frontier : σ (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))ᶜ = 0
  /-- The normal is almost everywhere strongly measurable for $\sigma$. -/
  aestronglyMeasurable_ν : AEStronglyMeasurable ν σ
  /-- The normal has unit length $\sigma$-almost everywhere. -/
  ae_norm_ν : ∀ᵐ x ∂σ, ‖ν x‖ = 1
  /-- **The divergence theorem**: $\int_\Omega \operatorname{div} F \, dx = \int \langle F, \nu
  \rangle \, d\sigma$ for every field $F$ that is continuous on $\overline{\Omega}$ and of class
  $C^1(\overline{\Omega})$ in the sense of `ContDiffOnClosure`. -/
  integral_div_eq : ∀ F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N),
    ContinuousOn F (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
    ContDiffOnClosure ℝ 1 F (Ω : Set (EuclideanSpace ℝ (Fin N))) →
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), EuclideanSpace.div F x = ∫ x, ⟪F x, ν x⟫_ℝ ∂σ

namespace BoundaryData

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω)

/-- The surface measure of a `BoundaryData` is finite. -/
instance instIsFiniteMeasure : IsFiniteMeasure B.σ := B.isFiniteMeasure

/-- $\sigma$-almost every point lies on $\partial\Omega$. -/
theorem ae_mem_frontier : ∀ᵐ x ∂B.σ, x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
  ae_iff.2 B.measure_compl_frontier

/-- $\sigma$-almost every point lies outside $\Omega$. -/
theorem ae_notMem : ∀ᵐ x ∂B.σ, x ∉ (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
  B.ae_mem_frontier.mono fun x hx hxΩ ↦ hx.2 (by rwa [Ω.isOpen.interior_eq])

/-- Every coordinate of the normal satisfies $|\nu_i| \le 1$ $\sigma$-almost everywhere. -/
theorem ae_abs_ν_apply_le (i : Fin N) : ∀ᵐ x ∂B.σ, |B.ν x i| ≤ 1 :=
  B.ae_norm_ν.mono fun x hx ↦ by
    rw [← Real.norm_eq_abs, ← hx]; exact PiLp.norm_apply_le _ i

/-- Every coordinate $\nu_i$ of the normal is almost everywhere strongly measurable for $\sigma$. -/
theorem aestronglyMeasurable_ν_apply (i : Fin N) :
    AEStronglyMeasurable (fun x ↦ B.ν x i) B.σ :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_aestronglyMeasurable B.aestronglyMeasurable_ν

/-- If $f \in L^p(\sigma)$, then $\nu_i f \in L^p(\sigma)$ for every coordinate $i$. -/
theorem memLp_ν_apply_mul {p : ℝ≥0∞} {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : MemLp f p B.σ)
    (i : Fin N) : MemLp (fun x ↦ B.ν x i * f x) p B.σ :=
  hf.of_le ((B.aestronglyMeasurable_ν_apply i).mul hf.aestronglyMeasurable) <|
    (B.ae_abs_ν_apply_le i).mono fun x hx ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hx

/-- If $f$ is integrable for $\sigma$, then $f \nu_i$ is integrable for $\sigma$ for every
coordinate $i$. -/
theorem integrable_mul_ν_apply {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : Integrable f B.σ)
    (i : Fin N) : Integrable (fun x ↦ f x * B.ν x i) B.σ :=
  hf.mul_bdd (B.aestronglyMeasurable_ν_apply i)
    ((B.ae_abs_ν_apply_le i).mono fun x hx ↦ by rwa [Real.norm_eq_abs])

/-- **Multiplication by a coordinate of the normal.** For $1 \le p \le \infty$ and a coordinate $i$,
the map $f \mapsto \nu_i f$ is a bounded linear operator on $L^p(\sigma)$ of norm at most $1$,
since $|\nu_i| \le 1$ $\sigma$-almost everywhere. -/
def mulNormalL (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin N) : Lp ℝ p B.σ →L[ℝ] Lp ℝ p B.σ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (B.memLp_ν_apply_mul (Lp.memLp f) i).toLp _
      map_add' := fun f g ↦ by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr (B.memLp_ν_apply_mul (Lp.memLp (f + g)) i)
          ((B.memLp_ν_apply_mul (Lp.memLp f) i).add (B.memLp_ν_apply_mul (Lp.memLp g) i)) ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [hx, Pi.add_apply, mul_add]
      map_smul' := fun c f ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr (B.memLp_ν_apply_mul (Lp.memLp (c • f)) i)
          ((B.memLp_ν_apply_mul (Lp.memLp f) i).const_smul c) ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul]
        ring }
    1 fun f ↦ by
      change ‖(B.memLp_ν_apply_mul (Lp.memLp f) i).toLp _‖ ≤ _
      rw [Lp.norm_toLp, one_mul, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_ae
        ((B.aestronglyMeasurable_ν_apply i).mul (Lp.aestronglyMeasurable f)) ?_)
      filter_upwards [B.ae_abs_ν_apply_le i] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hx

/-- The operator `BoundaryData.mulNormalL` maps $f$ to the class of $\nu_i f$: its value is
$\nu_i f$ $\sigma$-almost everywhere. -/
theorem coeFn_mulNormalL (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin N) (f : Lp ℝ p B.σ) :
    (B.mulNormalL p i f : EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[B.σ] fun x ↦ B.ν x i * f x :=
  MemLp.coeFn_toLp (B.memLp_ν_apply_mul (Lp.memLp f) i)

/-- **The divergence theorem for $C^1$ fields on $\mathbb{R}^N$.** If
$F \colon \mathbb{R}^N \to \mathbb{R}^N$ is $C^1$, then
$$\int_\Omega \operatorname{div} F \, dx = \int \langle F, \nu \rangle \, d\sigma.$$
-/
theorem integral_div_eq_of_contDiff {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (hF : ContDiff ℝ 1 F) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), EuclideanSpace.div F x
      = ∫ x, ⟪F x, B.ν x⟫_ℝ ∂B.σ :=
  B.integral_div_eq F hF.continuous.continuousOn (hF.contDiffOn.contDiffOnClosure Ω.isOpen)

include B in
/-- A function that is continuous on $\overline{\Omega}$ is integrable on $\Omega$, since $\Omega$
is bounded. -/
theorem integrableOn_of_continuousOn {G : Type*} [NormedAddCommGroup G]
    {f : EuclideanSpace ℝ (Fin N) → G}
    (hf : ContinuousOn f (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    IntegrableOn f (Ω : Set (EuclideanSpace ℝ (Fin N))) :=
  (hf.integrableOn_compact (Bornology.IsBounded.isCompact_closure B.isBounded)).mono_set
    subset_closure

/-- **The classical Green formula.** Let $u, v \colon \mathbb{R}^N \to \mathbb{R}$ be of class
$C^1(\overline{\Omega})$, and let $i$ be a coordinate. Then
$$\int_\Omega \partial_i u \, v \, dx + \int_\Omega u \, \partial_i v \, dx = \int u v \, \nu_i
  \, d\sigma.$$
This is the Green formula of [han2009theoretical], §7.6, and of [brezis2011functional], §9.5,
Example 4, Step A.

Each of $u$ and $v$ is continuous on $\overline{\Omega}$ and of class $C^1(\overline{\Omega})$
in the sense of `ContDiffOnClosure`. The proof is the divergence theorem for the field $uv e_i$. -/
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

/-- Local notation for the inverse Riesz map $(\mathbb{R}^N)^* \to \mathbb{R}^N$,
`(InnerProductSpace.toDualReal _).symm`. -/
local notation "𝓡⁻¹" =>
  LinearIsometryEquiv.symm (InnerProductSpace.toDualReal (EuclideanSpace ℝ (Fin N)))

/-- **Green's formula of second order for classical functions.** Let $u$ be of class
$C^2(\overline{\Omega})$ in the sense of `ContDiffOnClosure`, let $g$ be continuous on
$\overline{\Omega}$ with $g = Du$ on $\Omega$, and let $v$ be of class $C^1(\overline{\Omega})$.
Then
$$\int_\Omega \Delta u \, v \, dx + \int_\Omega \langle \nabla u, \nabla v \rangle \, dx = \int
  g(\nu) \, v \, d\sigma.$$
This is the formula of [brezis2011functional], §9.5, Example 4, Step A, of
[quarteroni2000numerical], (12.95), and of [han2009theoretical], §7.6.

The proof is the divergence theorem for the field $F = v R^{-1} g$, where $R^{-1}$ is the
inverse Riesz map; it is $v \nabla u$ on $\Omega$. The boundary values of $\nabla u$ are those
of the extension $g$, because a function of class $C^2(\overline{\Omega})$ in the sense of
`ContDiffOnClosure` has no derivative of its own on $\partial\Omega$. -/
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

/-- **Green's formula of second order in the form of the books.** Let $u$ be of class
$C^2(\overline{\Omega})$ in the sense of `ContDiffOnClosure` with $Du$ continuous on
$\overline{\Omega}$, and let $v$ be of class $C^1(\overline{\Omega})$. Then
$$\int_\Omega \Delta u \, v \, dx + \int_\Omega \langle \nabla u, \nabla v \rangle \, dx = \int
  \langle \nabla u, \nu \rangle \, v \, d\sigma.$$
-/
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

/-! ### The trace and Green's formula, as a structure -/

namespace BoundaryData

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The trace theorem and Green's formula on $\Omega$**, as a structure over boundary data $B$
with surface measure $\sigma$ and normal $\nu$. An element consists of:

* for every $1 \le p < \infty$, a bounded linear trace
  $T \colon W^{1,p}(\Omega) \to L^p(\sigma)$ (Theorem 7.3.10(b) of [han2009theoretical]; Theorem
  1.5.1.3 of [grisvard2011elliptic] with values in $L^p(\Gamma)$);
* the property that the trace of a function continuous on $\overline{\Omega}$ is its restriction
  (Theorem 7.3.10(a) of [han2009theoretical]);
* Green's formula $\int_\Omega \partial_i u \, v + \int_\Omega u \, \partial_i v = \int (Tu)(Tv)
  \, \nu_i \, d\sigma$ for $u \in W^{1,p}(\Omega)$ and $v \in W^{1,q}(\Omega)$ at finite
  conjugate exponents (Theorem 1.5.3.1 of [grisvard2011elliptic]; (7.6.1) and (7.6.3) of
  [han2009theoretical]; item 7(iii) of the Comments on Chapter 9 of [brezis2011functional]);
* Green's formula $\int_\Omega \partial_i u \, \varphi + \int_\Omega u \, \partial_i \varphi =
  \int (Tu) \varphi \, \nu_i \, d\sigma$ for $u \in W^{1,p}(\Omega)$, $1 \le p < \infty$, and a
  compactly supported $C^1$ function $\varphi$ on $\mathbb{R}^N$. This form holds also at
  $p = 1$, and the theorem on piecewise Sobolev functions (Example 7.2.7 of
  [han2009theoretical]) uses it.

The instances are `IsContDiffDomain.traceFamily` and `Triangulation.traceFamily`. Green's
formula is a field and not a theorem, because on a polygon it is proved by a sum over the
triangles (`Triangulation.green`), not by density on $\Omega$. -/
structure TraceFamily (B : BoundaryData Ω) where
  /-- The trace operator $W^{1,p}(\Omega) \to L^p(\sigma)$ at every finite exponent
  $1 \le p < \infty$. -/
  traceL : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → (SobolevEuclidean N 1 p Ω →L[ℝ] Lp ℝ p B.σ)
  /-- The trace of a function of $W^{1,p}(\Omega)$ that agrees almost everywhere on $\Omega$ with a
  function $\tilde u$ continuous on $\overline{\Omega}$ is $\tilde u$, $\sigma$-almost
  everywhere. -/
  traceL_ae_eq : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p Ω)
    (ũ : EuclideanSpace ℝ (Fin N) → ℝ),
    SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ →
    ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
    (traceL p hp u : EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[B.σ] ũ
  /-- Green's formula $\int_\Omega \partial_i u \, v + \int_\Omega u \, \partial_i v = \int (Tu)(Tv)
  \, \nu_i \, d\sigma$ for $u \in W^{1,p}(\Omega)$ and $v \in W^{1,q}(\Omega)$ at finite
  conjugate exponents $p$ and $q$. -/
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
  /-- Green's formula $\int_\Omega \partial_i u \, \varphi + \int_\Omega u \, \partial_i \varphi =
  \int (Tu) \varphi \, \nu_i \, d\sigma$ for $u \in W^{1,p}(\Omega)$, $1 \le p < \infty$, and a
  compactly supported $C^1$ function $\varphi$ on $\mathbb{R}^N$. -/
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

/-- **$W_0^{1,p}(\Omega)$ lies in the kernel of the trace.** For $1 \le p < \infty$ and
$u \in W_0^{1,p}(\Omega)$, the trace of $u$ is $0$. This is the easy half of item 7(ii) of the
Comments on Chapter 9 of [brezis2011functional]; the converse is in
`Numlib.Analysis.Sobolev.Boundary.Kernel`.

A test function vanishes on $\partial\Omega$, so its trace is zero by the field `traceL_ae_eq`.
The trace is continuous, and $W_0^{1,p}(\Omega)$ is the closure of the test functions. -/
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

/-- **The normal derivative of an $H^2$ function on the boundary.** For $u \in H^2(\Omega)$,
$$\frac{\partial u}{\partial \nu} = \sum_i \nu_i \, T(\partial_i u),$$
where $\partial_i u \in H^1(\Omega)$ and $T$ is the trace at $p = 2$. This is the normal
derivative of item 7(iii) of the Comments on Chapter 9 of [brezis2011functional].

The partial derivative $\partial_i u$ is `SobolevMultiIndex.partialDerivL`, and $H^2(\Omega)$ is
`SobolevEuclidean N 2 2 Ω`. The result is a function on $\mathbb{R}^N$, meaningful
$\sigma$-almost everywhere. -/
def normalTrace (u : SobolevEuclidean N 2 2 Ω) : EuclideanSpace ℝ (Fin N) → ℝ :=
  fun x ↦ ∑ i, B.ν x i * (𝒯.traceL 2 ENNReal.ofNat_ne_top
    (SobolevMultiIndex.partialDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i u) :
      EuclideanSpace ℝ (Fin N) → ℝ) x

/-- For $u \in H^2(\Omega)$, the normal derivative $\partial u / \partial \nu$ lies in
$L^2(\sigma)$. -/
theorem memLp_normalTrace (u : SobolevEuclidean N 2 2 Ω) : MemLp (𝒯.normalTrace u) 2 B.σ :=
  memLp_finsetSum _ fun i _ ↦ B.memLp_ν_apply_mul (Lp.memLp _) i

/-- The normal derivative is additive: $\partial(u + v)/\partial\nu = \partial u/\partial\nu +
\partial v/\partial\nu$ $\sigma$-almost everywhere. -/
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

/-- The normal derivative is homogeneous: $\partial(cu)/\partial\nu = c \, \partial u/\partial\nu$
$\sigma$-almost everywhere. -/
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

/-- **Green's formula for $u \in H^2(\Omega)$ and $v \in H^1(\Omega)$.** For $u \in H^2(\Omega)$ and
$v \in H^1(\Omega)$,
$$\int_\Omega \Bigl(\sum_i \partial_i \partial_i u\Bigr) v \, dx + \int_\Omega \sum_i \partial_i
  u \, \partial_i v \, dx = \int \frac{\partial u}{\partial \nu} \, (Tv) \, d\sigma,$$
where the first integrand is the weak Laplacian of $u$ times $v$. This is item 7(iii) of the
Comments on Chapter 9 of [brezis2011functional] and (7.6.4) of [han2009theoretical].

The proof applies the field `green` at $p = q = 2$ to $\partial_i u$ and $v$, and sums over $i$. -/
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

/-- Local notation for the standard basis of $\mathbb{R}^N$. -/
local notation "𝔅" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **The Neumann boundary condition of an $H^2$ weak solution.** Let $u \in H^2(\Omega)$ and
$f \in L^2(\Omega)$, and assume that
$$\int_\Omega \nabla u \cdot \nabla \varphi \, dx + \int_\Omega u \varphi \, dx = \int_\Omega f
  \varphi \, dx \qquad \text{for every } \varphi \in H^1(\Omega).$$
Then $\partial u / \partial \nu = 0$ $\sigma$-almost everywhere. This is the part of Theorem
9.26 of [brezis2011functional] that has no meaning without a trace; the hypothesis is the weak
form (49) of the Neumann problem $-\Delta u + u = f$ of §9.6, for $u$ seen as an element of
$H^1(\Omega)$.

The left side of the hypothesis is `Elliptic.laplaceForm` and the right side is `Elliptic.load`.
Against test functions, the weak equation gives $-\Delta_w u + u = f$ almost everywhere on
$\Omega$ (`Elliptic.neg_weakLaplacian_add_ae_eq_of_forall_laplaceForm_eq`). For
$\varphi \in C_c^\infty(\mathbb{R}^N)$, Green's formula
`BoundaryData.TraceFamily.green_laplacian` then leaves $\int (\partial u/\partial\nu) \varphi \,
d\sigma = 0$, and so $\partial u / \partial \nu \in L^2(\sigma)$ vanishes almost everywhere
(`ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
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

/-! ### The epigraph of a function of $d$ variables -/

namespace EuclideanSpace

variable {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **The epigraph** of $g \colon \mathbb{R}^d \to \mathbb{R}$: the region
$$\{y \in \mathbb{R}^{d+1} : g(y') < y_N\}$$
strictly above the graph of $g$, where $y' \in \mathbb{R}^d$ is the vector of the first $d$
coordinates of $y$ and $y_N$ is its last coordinate. This is the coordinate convention of
`IsBoundaryGraphAt`: the boundary is a graph over the first $d$ coordinates. -/
def epigraph (g : EuclideanSpace ℝ (Fin d) → ℝ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {y | g (init y) < y (Fin.last d)}

/-- A point $y$ lies in the epigraph of $g$ if and only if $g(y') < y_N$. -/
theorem mem_epigraph {y : EuclideanSpace ℝ (Fin (d + 1))} :
    y ∈ epigraph g ↔ g (init y) < y (Fin.last d) :=
  Iff.rfl

/-- The point $(x', t)$ lies in the epigraph of $g$ if and only if $g(x') < t$. -/
@[simp]
theorem snocLast_mem_epigraph (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    snocLast x' t ∈ epigraph g ↔ g x' < t := by
  simp [mem_epigraph]

/-- The vertical line through $x'$ meets the epigraph of $g$ in the open half-line
$\{t : t > g(x')\}$. -/
theorem epigraph_preimage_snocLast (x' : EuclideanSpace ℝ (Fin d)) :
    (fun t ↦ snocLast x' t) ⁻¹' epigraph g = Ioi (g x') := by
  ext t
  simp

/-- The upper half space $\{y : y_N > 0\}$ is the epigraph of the zero function. -/
theorem upperHalfSpace_eq_epigraph_zero : upperHalfSpace d = epigraph 0 := rfl

/-- **`IsBoundaryGraphAt` in terms of the epigraph.** For a class $V$ of functions on
$\mathbb{R}^d$, the set $\Omega$ is the region above a graph from $V$ in the ball $B(x_0, r)$ if
and only if there are a rigid motion $T$ and a $g \in V$ with
$$\Omega \cap B(x_0, r) = B(x_0, r) \cap T^{-1}(\operatorname{epi} g).$$
Here $\operatorname{epi} g$ is the epigraph `EuclideanSpace.epigraph g`. -/
theorem isBoundaryGraphAt_iff {V : Set (EuclideanSpace ℝ (Fin d) → ℝ)}
    {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ} :
    IsBoundaryGraphAt V Ω x₀ r ↔
      ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)), ∃ g ∈ V,
        Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' epigraph g :=
  Iff.rfl

/-- The epigraph of a continuous function is open. -/
theorem isOpen_epigraph (hg : Continuous g) : IsOpen (epigraph g) :=
  isOpen_lt (hg.comp continuous_init) continuous_apply_last

/-- **The closure of the epigraph.** If $g$ is continuous, then the closure of its epigraph is the
closed region $\{y : g(y') \le y_N\}$ on or above the graph.

A point on the graph is the limit of the points $(y', y_N + 1/(n+1))$ of the epigraph. -/
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

/-- Let $g$ be continuous, let $T$ be a rigid motion, let $B$ be open, and assume that $\Omega \cap
B = B \cap T^{-1}(\operatorname{epi} g)$. Then
$$\overline{\Omega} \cap B \subseteq T^{-1}(\{y : g(y') \le y_N\}),$$
so near a graph chart the closure of $\Omega$ lies on or above the graph. Here
$\operatorname{epi} g$ is the epigraph `EuclideanSpace.epigraph g`. -/
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

/-- **The boundary of the epigraph.** If $g$ is continuous, then the boundary of its epigraph is the
graph $\{y : y_N = g(y')\}$. -/
theorem frontier_epigraph (hg : Continuous g) :
    frontier (epigraph g) = {y | y (Fin.last d) = g (init y)} := by
  rw [(isOpen_epigraph hg).frontier_eq, closure_epigraph hg]
  ext y
  simp only [Set.mem_sdiff, mem_ofPred_eq, mem_epigraph, not_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨h.ge, h.le⟩

/-- If $g$ is continuous and $T$ is a rigid motion, then the boundary of
$T^{-1}(\operatorname{epi} g)$ is $T^{-1}(\{y : y_N = g(y')\})$. Here $\operatorname{epi} g$ is
the epigraph `EuclideanSpace.epigraph g`. -/
theorem frontier_preimage_epigraph (hg : Continuous g)
    (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    frontier (T ⁻¹' epigraph g) = T ⁻¹' {y | y (Fin.last d) = g (init y)} := by
  have h := T.toHomeomorph.preimage_frontier (epigraph g)
  rw [AffineIsometryEquiv.coe_toHomeomorph] at h
  rw [← h, frontier_epigraph hg]

/-- If $g$ is continuous, the point $(x', t)$ lies in the closure of the epigraph of $g$ if and only
if $g(x') \le t$. -/
theorem snocLast_mem_closure_epigraph (hg : Continuous g) (x' : EuclideanSpace ℝ (Fin d))
    (t : ℝ) : snocLast x' t ∈ closure (epigraph g) ↔ g x' ≤ t := by
  rw [closure_epigraph hg]
  simp

/-- **The chart condition does not depend on the chart in the overlap of two chart balls.** Let
$T_1, T_2$ be rigid motions, and assume that $\Omega \cap B(x_k, r_k) = B(x_k, r_k) \cap
T_k^{-1}(\operatorname{epi} g_k)$ for $k = 1, 2$. Then
$$B(x_1, r_1) \cap B(x_2, r_2) \cap T_1^{-1}(\operatorname{epi} g_1) = B(x_1, r_1) \cap B(x_2,
  r_2) \cap T_2^{-1}(\operatorname{epi} g_2).$$
Here $\operatorname{epi} g_k$ is the epigraph `EuclideanSpace.epigraph g_k`. -/
theorem inter_inter_preimage_epigraph_eq {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    {T₁ T₂ : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
    {g₁ g₂ : EuclideanSpace ℝ (Fin d) → ℝ} {x₁ x₂ : EuclideanSpace ℝ (Fin (d + 1))} {r₁ r₂ : ℝ}
    (h₁ : Ω ∩ Metric.ball x₁ r₁ = Metric.ball x₁ r₁ ∩ T₁ ⁻¹' epigraph g₁)
    (h₂ : Ω ∩ Metric.ball x₂ r₂ = Metric.ball x₂ r₂ ∩ T₂ ⁻¹' epigraph g₂) :
    Metric.ball x₁ r₁ ∩ Metric.ball x₂ r₂ ∩ T₁ ⁻¹' epigraph g₁
      = Metric.ball x₁ r₁ ∩ Metric.ball x₂ r₂ ∩ T₂ ⁻¹' epigraph g₂ := by
  ext y
  have e₁ := Set.ext_iff.1 h₁ y
  have e₂ := Set.ext_iff.1 h₂ y
  simp only [mem_inter_iff] at e₁ e₂ ⊢
  tauto
end EuclideanSpace

/-- **The boundary of a set that is locally an epigraph is the graph, inside the ball.** Let $g$ be
continuous, let $T$ be a rigid motion, and assume that $\Omega \cap B(x_0, r) = B(x_0, r) \cap
T^{-1}(\operatorname{epi} g)$. Then
$$\partial\Omega \cap B(x_0, r) = B(x_0, r) \cap T^{-1}(\{y : y_N = g(y')\}).$$
Here $\operatorname{epi} g$ is the epigraph `EuclideanSpace.epigraph g`.

The inclusion $\subseteq$ at a single point is `IsBoundaryGraphAt.last_eq_of_mem_frontier` of
`Numlib.Analysis.Sobolev.Chart`. -/
theorem IsBoundaryGraphAt.frontier_inter_ball {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Continuous g) {T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
    {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    frontier Ω ∩ Metric.ball x₀ r
      = Metric.ball x₀ r ∩ T ⁻¹' {y | y (Fin.last d) = g (EuclideanSpace.init y)} := by
  rw [← frontier_inter_open_inter Metric.isOpen_ball, h, inter_comm (Metric.ball x₀ r),
    frontier_inter_open_inter Metric.isOpen_ball, EuclideanSpace.frontier_preimage_epigraph hg,
    inter_comm]

namespace EuclideanSpace

variable {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Let $g$ be continuous, let $T$ be a rigid motion, and assume that $\Omega \cap B(x_0, r) =
B(x_0, r) \cap T^{-1}(\operatorname{epi} g)$. Then every boundary point of $\Omega$ in
$B(x_0, r)$ lies on the boundary of $T^{-1}(\operatorname{epi} g)$, that is, on the graph of the
chart. Here $\operatorname{epi} g$ is the epigraph `EuclideanSpace.epigraph g`. -/
theorem mem_frontier_preimage_epigraph_of_mem_frontier
    {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    {T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
    (hg : Continuous g) {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' epigraph g)
    {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y ∈ frontier Ω) (hyB : y ∈ Metric.ball x₀ r) :
    y ∈ frontier (T ⁻¹' epigraph g) := by
  have h2 : y ∈ frontier Ω ∩ Metric.ball x₀ r := ⟨hy, hyB⟩
  rw [IsBoundaryGraphAt.frontier_inter_ball hg h] at h2
  rw [frontier_preimage_epigraph hg]
  exact h2.2

/-- **The strip of height $t$ above the graph of $g$**: the set
$$\{y : g(y') < y_N < g(y') + t\},$$
in the frame of the graph. -/
def graphStrip (g : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) :
    Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {y | g (init y) < y (Fin.last d) ∧ y (Fin.last d) < g (init y) + t}

/-- If $g$ is continuous, the strip above the graph of $g$ is open. -/
theorem isOpen_graphStrip (hg : Continuous g) (t : ℝ) : IsOpen (graphStrip g t) :=
  (isOpen_lt (hg.comp continuous_init) continuous_apply_last).inter
    (isOpen_lt continuous_apply_last ((hg.comp continuous_init).add continuous_const))

/-- The point $(x', s)$ lies in the strip of height $t$ above the graph of $g$ if and only if
$g(x') < s < g(x') + t$. -/
theorem snocLast_mem_graphStrip {t : ℝ} (x' : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    snocLast x' s ∈ graphStrip g t ↔ g x' < s ∧ s < g x' + t := by
  simp [graphStrip]

end EuclideanSpace

end
