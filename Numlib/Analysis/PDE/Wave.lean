/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Numlib.Analysis.ODE.HarmonicOscillator
import Numlib.Analysis.PDE.Heat
import Numlib.Analysis.PDE.Heat.Classical
import Numlib.Analysis.Sobolev.TranslationCurve

/-!
# The wave equation

This file solves the wave equation
$$\partial_{tt} u - \Delta u = 0 \text{ in } \Omega \times (0, \infty), \qquad u = 0 \text{ on }
  \partial\Omega \times (0, \infty), \qquad u(\cdot, 0) = u_0, \qquad \partial_t u(\cdot, 0) = v_0$$
on an open set $\Omega \subseteq \mathbb{R}^N$, as [brezis2011functional], §10.3 (Theorems 10.7 and
10.8, Remarks 6–10) solves it with the results of chapter 7 (Theorems 7.4 and 7.5, Remark 6). The
equation becomes the first-order system $U' + AU = 0$ for $U = (u, \partial_t u)$ in the phase space
$H = H^1_0(\Omega) \times L^2(\Omega)$, with the inner product (34)
$$\langle (u_1, v_1), (u_2, v_2) \rangle
  = \int_\Omega \nabla u_1 \cdot \nabla u_2 + \int_\Omega u_1 u_2 + \int_\Omega v_1 v_2,$$
and the operator (35) $A(u, v) = (-v, -\Delta u)$ with domain
$D(A) = D(-\Delta) \times H^1_0(\Omega)$. Here $-\Delta$ is the Dirichlet Laplacian of
`Numlib.Analysis.PDE.DirichletLaplacian`. Its domain $D(-\Delta)$ is $H^2(\Omega) \cap
H^1_0(\Omega)$ on a $C^2$ domain with bounded boundary, and the weak domain in general. The operator
$A + I$ is maximal monotone. The operator $A$ itself is not monotone for this inner product, and it
is not symmetric.

A solution is a curve $u : \mathbb{R} \to L^2(\Omega)$ in the class (31) of Theorem 10.7. For
$u_0 \in D(-\Delta)$ and $v_0 \in H^1_0(\Omega)$ there is exactly one solution on $[0, \infty)$, and
its energy $\|u'(t)\|^2 + \int_\Omega |\nabla u(t)|^2$ is constant. Theorem 10.8 describes $D(A^k)$
and gives the smoothness of the solution for smooth compatible data. Everything except the Sobolev
regularity of $D(A^k)$ and the space–time smoothness holds on an arbitrary open set, for the same
reason as for the heat equation in `Numlib.Analysis.PDE.Heat`. Below,
$\iota : H^1_0(\Omega) \to L^2(\Omega)$ is the inclusion `SobolevMultiIndexZero.fnL`, and for
$v \in L^2(\Omega)$ the element $\tilde v \in H^1_0(\Omega)$ is the preimage with
$\iota \tilde v = v$ when there is one (`toSobolevZero`).

## Main definitions

* `Wave.phaseSpace`: the phase space $H^1_0(\Omega) \times L^2(\Omega)$ with the inner product (34).
* `Wave.operator`: the wave operator $A(u, v) = (-v, -\Delta u)$ with domain
  $D(-\Delta) \times H^1_0(\Omega)$.
* `Wave.IsSolution`: a solution of the wave equation in the class (31).
* `Wave.solution`: the solution, the first component of $e^t S_{A+I}(t)(u_0, v_0)$.
* `Wave.dAlembert`: d'Alembert's formula (40) on $\mathbb{R}$.
* `Wave.dirichletPhaseSpace` and `Wave.operator'`: for bounded $\Omega$, the phase space of Remark 7
  with the inner product $\int \nabla u_1 \cdot \nabla u_2 + \int v_1 v_2$, and the wave operator on
  it.
* `Wave.IsClassicalSolution`: a pointwise solution of $\partial_{tt} u = \Delta_x u$ on a cylinder
  $\Omega \times (0, T)$.
* `Wave.MemLaplacianDomain`: the domains $D_m$ of the Dirichlet Laplacian, with $D_0 = L^2(\Omega)$,
  $D_1 = H^1_0(\Omega)$ and $D_{m+2} = \{f \in D(-\Delta) : -\Delta f \in D_m\}$.
* `Wave.operator.powDomainToSobolevL`: the continuous injection
  $D(A^k) \to H^{k+1}(\Omega) \times H^k(\Omega)$ on a $C^{k+1}$ domain with bounded boundary.
* `Wave.dAlembertL2`: d'Alembert's formula as a curve in $L^2(\mathbb{R})$.

## Main results

* `Wave.operator_add_id_isMaximalMonotone`: $A + I$ is maximal monotone on every open set.
* `Wave.existsUnique_isSolution`: existence and uniqueness of the solution (Theorem 10.7).
* `Wave.IsSolution.energy`: conservation of energy (32).
* `Wave.existsUnique_isSolution_backward`: the wave equation is uniquely solvable backward in time
  (Remark 7).
* `Wave.operator'_isMaximalMonotone`, `Wave.neg_operator'_isMaximalMonotone`: for bounded $\Omega$,
  $A$ and $-A$ are maximal monotone for the Dirichlet inner product (Remark 7).
* `Wave.isSolution_dAlembert`, `Wave.IsSolution.eqOn_dAlembertL2`: d'Alembert's formula gives the
  solution on $\mathbb{R}$ (Remark 8).
* `Wave.dAlembert_contDiffOn_off_characteristics`: a singularity of the datum propagates only along
  the characteristics (Remark 8).
* `Wave.IsSolution.hasSum_eigenfunction`: the expansion of the solution in the Dirichlet
  eigenfunctions (Remark 9).
* `Wave.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`: the compatibility conditions are
  necessary (Remark 10).
* `Wave.mem_operator_powGraph_iff`: $D(A^k) = D_{k+1} \times D_k$.
* `Wave.MemLaplacianDomain.exists_sobolev`: $D_m \subseteq H^m(\Omega)$ on a $C^m$ domain with
  bounded boundary.
* `Wave.IsSolution.contDiffOnThrough_of_powDomain`: for data in $D(A^k)$ and $j \le k$,
  $u \in C^{k-j}([0, \infty); H^{j+1}(\Omega))$.
* `Wave.IsSolution.contDiffOnClosure_spaceTime`: for data in every $D(A^k)$,
  $u \in C^\infty(\bar\Omega \times [0, \infty))$ (Theorem 10.8).

## Proof outline

Theorem 7.4 (Hille–Yosida, `LinearPMap.IsMaximalMonotone.exists_isSolutionOn`) for the maximal
monotone operator $A + I$, with the shift of Remark 6 of chapter 7
(`LinearPMap.isSolutionOn_smul_id_vadd_iff`: $V = e^{-t} U$ solves $V' + (A + I) V = 0$), gives a
solution $U$ of $U' + AU = 0$. Its first component is a solution of the wave equation. Conversely
$(\tilde u, u')$ solves $U' + AU = 0$ for every solution $u$, and this gives uniqueness. For Theorem
10.8, $D(A^k) = D_{k+1} \times D_k$ on every open set, and $D_m \subseteq H^m(\Omega)$ on a $C^m$
domain with bounded boundary by Theorem 9.25 at even and at odd orders. Theorem 7.5 for $A + I$,
with the transport $D((A + I)^j) \cong D(A^j)$ (`LinearPMap.IsAddSmulId.transport`) and the shift
$e^t$, gives $U \in C^{k-j}([0, \infty); D(A^j))$, hence
$u \in C^{k-j}([0, \infty); H^{j+1}(\Omega))$. The space–time bridge of
`Numlib.Analysis.PDE.Bochner.SpaceTime` then gives $u \in C^\infty(\bar\Omega \times [0, \infty))$.

For Remark 8, the calculus of the translation group $t \mapsto \tau_t f = f(\cdot + t)$ in
$L^2(\mathbb{R})$ and $H^1(\mathbb{R})$ and of the primitive curve
$t \mapsto \int_{-t}^{t} \tau_s v_0 \, ds$ is in `Numlib.Analysis.Sobolev.TranslationCurve`. The
membership $u(t) \in D(-\Delta)$ is read through the $H^1$ element `Wave.dAlembertH1Space` that
carries $\partial_x u(t)$ (`Wave.mem_dirichletLaplacianDomain_of_forall_ae_eq`), and
$-\Delta u(t) = -\partial_{tt} u(t)$ holds because both sides equal $-\frac12 (\tau_t u_0'' +
\tau_{-t} u_0'') - \frac12 (\tau_t v_0' - \tau_{-t} v_0')$. Remark 9 reduces to the harmonic
oscillator on $[0, \infty)$ (`eq_cos_add_sin_of_hasDerivWithinAt_oscillator` of
`Numlib.Analysis.ODE.HarmonicOscillator`). Remark 10 follows Remark 4 for the heat equation
(`Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`).

## Implementation notes

* The phase space is Mathlib's $\ell^2$-product `WithLp 2` of $H^1_0(\Omega)$ and $L^2(\Omega)$
  (`WithLp.instProdInnerProductSpace`), which is complete because both factors are. It is wrapped in
  a `def` type synonym `Wave.phaseSpace` that carries only its `NormedAddCommGroup`,
  `InnerProductSpace ℝ` and `CompleteSpace` instances. Every algebraic instance of the phase space
  then comes from `NormedAddCommGroup`, the form that the `LinearPMap` theory of chapter 7 expects.
  An `abbrev` would put `WithLp.instAddCommGroup` in the type of the operator, and the Hille–Yosida
  statements would no longer unify with it.
* The components are `Wave.phaseSpace.fst`, `Wave.phaseSpace.snd` and `Wave.phaseSpace.mk`, with
  (34) as `Wave.phaseSpace.inner_def` and the norm as `Wave.phaseSpace.norm_sq_eq`. The space
  $H^1_0(\Omega)$ is `SobolevEuclideanZero N 1 2 Ω` with its $H^1$ inner product, which is the first
  part of (34) by `Elliptic.laplaceForm_eq_innerSL`.
* The operator is a `LinearPMap` on the phase space. Its domain asks the first component to lie in
  $D(-\Delta)$ after the inclusion `SobolevMultiIndexZero.fnL`, and the second component to lie in
  the range of that inclusion (`Wave.MemOperatorDomain`).
* A solution is a curve $u : \mathbb{R} \to L^2(\Omega)$, the unknown $u$ of the source and not the
  phase-space curve $U$. The class $C^1([0, \infty); H^1_0(\Omega))$ is read through the inclusion
  (`Bochner.ContDiffOnThrough`), and only the values on $[0, \infty)$ are constrained. The
  translation between $U$ and $u$ (`Wave.isSolution_of_isSolutionOn`,
  `Wave.IsSolution.isSolutionOn`) is the main part of `Wave.existsUnique_isSolution`.
* Remark 7 needs the other inner product $\int \nabla u_1 \cdot \nabla u_2$ on $H^1_0(\Omega)$. It
  is equivalent to the $H^1$ inner product exactly when Poincaré's inequality holds (bounded
  $\Omega$, Corollary 9.19). For it $\langle AU, U \rangle = 0$, and $A$ and $-A$ are maximal
  monotone. This is the second phase-space type `Wave.dirichletPhaseSpace`, with the same operator
  `Wave.operator'`. The two-sided solvability and the energy identity for all $t \in \mathbb{R}$ are
  obtained without it, by time reversal ($t \mapsto -t$, $v_0 \mapsto -v_0$,
  `Wave.existsUnique_isSolution_backward`), on every open set.
* The domains $D_m$ (`Wave.MemLaplacianDomain`) are the source's spaces "$w \in H^m(\Omega)$,
  $\Delta^j w = 0$ on $\Gamma$ for $2j < m$" of the proof of Theorem 10.8, before the Sobolev spaces
  are read in. They describe $D(A^k)$ on every open set. The continuous injection
  $D(A^k) \to H^{k+1}(\Omega) \times H^k(\Omega)$ comes from the closed graph theorem.
* Remark 8 is stated on $\Omega = \mathbb{R}$, as `⊤ : Opens (EuclideanSpace ℝ (Fin 1))`. The data
  $u_0 \in H^2(\mathbb{R})$ and $v_0 \in H^1(\mathbb{R}) = H^1_0(\mathbb{R})$ are read through
  `Wave.toZeroTopL`, and the formula (40) through `Wave.lineEmbed` and the coordinate
  $x \mapsto x_0$.
* Remark 10 (`Wave.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`) is stated for a function
  that is $C^\infty$ on all of $E \times \mathbb{R}$, as Remark 4 of the heat equation in
  `Numlib.Analysis.PDE.Heat.Classical` is. The source states it for
  $u \in C^\infty(\bar\Omega \times [0, \infty))$.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Interval Topology InnerProductSpace

noncomputable section

namespace Wave

open LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The phase space $H^1_0(\Omega) \times L^2(\Omega)$ -/

variable (Ω) in
/-- The **phase space of the wave equation**: $H = H^1_0(\Omega) \times L^2(\Omega)$ with the inner
product (34)
$$\langle (u_1, v_1), (u_2, v_2) \rangle = \langle u_1, u_2 \rangle_{H^1} + \langle v_1, v_2
  \rangle_{L^2}$$
of [brezis2011functional], §10.3. It is a Hilbert space.

The type is Mathlib's $\ell^2$-product `WithLp 2` of the two Hilbert spaces, as a type synonym
that carries only its `NormedAddCommGroup`, `InnerProductSpace` and `CompleteSpace` structures.
Every algebraic instance of the phase space then comes from them, as the `LinearPMap` theory of
chapter 7 expects. -/
def phaseSpace : Type :=
  WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

instance : NormedAddCommGroup (phaseSpace Ω) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))))

instance : InnerProductSpace ℝ (phaseSpace Ω) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))))

instance : CompleteSpace (phaseSpace Ω) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))))

namespace phaseSpace

variable (Ω) in
/-- The point $(u, v)$ of the phase space, for $u \in H^1_0(\Omega)$ and $v \in L^2(\Omega)$. -/
def mk (u : SobolevEuclideanZero N 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : phaseSpace Ω :=
  WithLp.toLp 2 (u, v)

/-- The first component $u \in H^1_0(\Omega)$ of a point $(u, v)$ of the phase space. -/
def fst (U : phaseSpace Ω) : SobolevEuclideanZero N 1 2 Ω :=
  (WithLp.ofLp (U : WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))))).1

/-- The second component $v \in L^2(\Omega)$ of a point $(u, v)$ of the phase space. -/
def snd (U : phaseSpace Ω) : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (WithLp.ofLp (U : WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))))).2

/-- The first component of $(u, v)$ is $u$. -/
@[simp]
theorem mk_fst (u : SobolevEuclideanZero N 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : (mk Ω u v).fst = u :=
  rfl

/-- The second component of $(u, v)$ is $v$. -/
@[simp]
theorem mk_snd (u : SobolevEuclideanZero N 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : (mk Ω u v).snd = v :=
  rfl

/-- Two points of the phase space with the same components are equal. -/
theorem ext {U V : phaseSpace Ω} (h1 : U.fst = V.fst) (h2 : U.snd = V.snd) : U = V :=
  WithLp.ofLp_injective 2 (Prod.ext h1 h2)

/-- Every point $U$ of the phase space is the pair of its two components. -/
theorem mk_fst_snd (U : phaseSpace Ω) : mk Ω U.fst U.snd = U :=
  rfl

/-- The inner product of the phase space is (34): for $U = (u_1, v_1)$ and $V = (u_2, v_2)$,
$$\langle U, V \rangle = \langle u_1, u_2 \rangle_{H^1} + \langle v_1, v_2 \rangle_{L^2}.$$
This is (34) of [brezis2011functional], §10.3.

The $H^1$ inner product is $\int_\Omega \nabla u_1 \cdot \nabla u_2 + \int_\Omega u_1 u_2$
(`Wave.inner_sobolevZero_eq`). -/
theorem inner_def (U V : phaseSpace Ω) :
    ⟪U, V⟫_ℝ = ⟪U.fst, V.fst⟫_ℝ + ⟪U.snd, V.snd⟫_ℝ :=
  rfl

/-- The norm of the phase space: $\|U\|^2 = \|u\|_{H^1}^2 + \|v\|_{L^2}^2$ for $U = (u, v)$. -/
theorem norm_sq_eq (U : phaseSpace Ω) : ‖U‖ ^ 2 = ‖U.fst‖ ^ 2 + ‖U.snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (U : WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))))

/-- The components of $0$: the first component of $0$ is $0$. -/
@[simp]
theorem zero_fst : (0 : phaseSpace Ω).fst = 0 :=
  rfl

/-- The components of $0$: the second component of $0$ is $0$. -/
@[simp]
theorem zero_snd : (0 : phaseSpace Ω).snd = 0 :=
  rfl

/-- The first component of $U + V$ is the sum of the first components. -/
@[simp]
theorem add_fst (U V : phaseSpace Ω) : (U + V).fst = U.fst + V.fst :=
  rfl

/-- The second component of $U + V$ is the sum of the second components. -/
@[simp]
theorem add_snd (U V : phaseSpace Ω) : (U + V).snd = U.snd + V.snd :=
  rfl

/-- The first component of $-U$ is the negative of the first component of $U$. -/
@[simp]
theorem neg_fst (U : phaseSpace Ω) : (-U).fst = -U.fst :=
  rfl

/-- The second component of $-U$ is the negative of the second component of $U$. -/
@[simp]
theorem neg_snd (U : phaseSpace Ω) : (-U).snd = -U.snd :=
  rfl

/-- The first component of $U - V$ is the difference of the first components. -/
@[simp]
theorem sub_fst (U V : phaseSpace Ω) : (U - V).fst = U.fst - V.fst :=
  rfl

/-- The second component of $U - V$ is the difference of the second components. -/
@[simp]
theorem sub_snd (U V : phaseSpace Ω) : (U - V).snd = U.snd - V.snd :=
  rfl

/-- The first component of $cU$ is $c$ times the first component of $U$. -/
@[simp]
theorem smul_fst (c : ℝ) (U : phaseSpace Ω) : (c • U).fst = c • U.fst :=
  rfl

/-- The second component of $cU$ is $c$ times the second component of $U$. -/
@[simp]
theorem smul_snd (c : ℝ) (U : phaseSpace Ω) : (c • U).snd = c • U.snd :=
  rfl

variable (Ω) in
/-- The first component $(u, v) \mapsto u$, as a continuous linear map from the phase space to
$H^1_0(\Omega)$. -/
def fstL : phaseSpace Ω →L[ℝ] SobolevEuclideanZero N 1 2 Ω :=
  WithLp.fstL 2 ℝ (SobolevEuclideanZero N 1 2 Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

variable (Ω) in
/-- The second component $(u, v) \mapsto v$, as a continuous linear map from the phase space to
$L^2(\Omega)$. -/
def sndL : phaseSpace Ω →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  WithLp.sndL 2 ℝ (SobolevEuclideanZero N 1 2 Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

/-- The map `Wave.phaseSpace.fstL` sends $U$ to its first component. -/
@[simp]
theorem fstL_apply (U : phaseSpace Ω) : fstL Ω U = U.fst :=
  rfl

/-- The map `Wave.phaseSpace.sndL` sends $U$ to its second component. -/
@[simp]
theorem sndL_apply (U : phaseSpace Ω) : sndL Ω U = U.snd :=
  rfl

end phaseSpace

/-- The $H^1$ inner product of $H^1_0(\Omega)$ is $\langle u_1, u_2 \rangle_{H^1} = \int_\Omega
\nabla u_1 \cdot \nabla u_2 + \int_\Omega u_1 u_2$, the Dirichlet form `Elliptic.dirichletForm`
plus the $L^2$ inner product of $\iota u_1$ and $\iota u_2$. -/
theorem inner_sobolevZero_eq (u₁ u₂ : SobolevEuclideanZero N 1 2 Ω) :
    ⟪u₁, u₂⟫_ℝ = dirichletForm Ω (u₁ : SobolevEuclidean N 1 2 Ω) (u₂ : SobolevEuclidean N 1 2 Ω)
      + ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₁,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          u₂⟫_ℝ :=
  (laplaceForm_apply_eq_inner Ω (u₁ : SobolevEuclidean N 1 2 Ω)
    (u₂ : SobolevEuclidean N 1 2 Ω)).symm.trans (laplaceForm_apply_eq_dirichletForm_add Ω _ _)

/-! ### The operator $A(u, v) = (-v, -\Delta u)$ -/

variable (Ω) in
/-- The **domain condition of the wave operator**: a point $(u, v)$ of the phase space satisfies it
if $\iota u \in D(-\Delta)$ and $v$ is in the range of the inclusion
$\iota : H^1_0(\Omega) \to L^2(\Omega)$, that is, $v \in H^1_0(\Omega)$. This is the domain
$D(A)$ of (35) in [brezis2011functional], §10.3, with the weak domain $D(-\Delta)$ of the
Dirichlet Laplacian in place of $H^2(\Omega) \cap H^1_0(\Omega)$. -/
def MemOperatorDomain (U : phaseSpace Ω) : Prop :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst
    ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero N 1 2 Ω,
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = U.snd

/-- The point $0$ satisfies the domain condition of the wave operator. -/
theorem memOperatorDomain_zero : MemOperatorDomain Ω (0 : phaseSpace Ω) := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · rw [phaseSpace.zero_fst, _root_.map_zero]
    exact Submodule.zero_mem _
  · rw [_root_.map_zero, phaseSpace.zero_snd]

/-- The domain condition of the wave operator is closed under addition. -/
theorem MemOperatorDomain.add {U V : phaseSpace Ω} (hU : MemOperatorDomain Ω U)
    (hV : MemOperatorDomain Ω V) : MemOperatorDomain Ω (U + V) := by
  obtain ⟨hU1, w, hw⟩ := hU
  obtain ⟨hV1, w', hw'⟩ := hV
  refine ⟨?_, ⟨w + w', ?_⟩⟩
  · rw [phaseSpace.add_fst, _root_.map_add]
    exact add_mem hU1 hV1
  · rw [_root_.map_add, hw, hw', phaseSpace.add_snd]

/-- The domain condition of the wave operator is closed under scalar multiplication. -/
theorem MemOperatorDomain.smul (c : ℝ) {U : phaseSpace Ω} (hU : MemOperatorDomain Ω U) :
    MemOperatorDomain Ω (c • U) := by
  obtain ⟨hU1, w, hw⟩ := hU
  refine ⟨?_, ⟨c • w, ?_⟩⟩
  · rw [phaseSpace.smul_fst, _root_.map_smul]
    exact Submodule.smul_mem _ c hU1
  · rw [_root_.map_smul, hw, phaseSpace.smul_snd]

variable (Ω) in
/-- The **domain of the wave operator** $D(A) = D(-\Delta) \times H^1_0(\Omega)$, as a submodule of
the phase space: the points that satisfy `Wave.MemOperatorDomain`. -/
def operatorDomain : Submodule ℝ (phaseSpace Ω) where
  carrier := {U | MemOperatorDomain Ω U}
  zero_mem' := memOperatorDomain_zero
  add_mem' := fun hU hV ↦ hU.add hV
  smul_mem' := fun c _ hU ↦ hU.smul c

/-- A point is in `Wave.operatorDomain` if and only if it satisfies `Wave.MemOperatorDomain`. -/
theorem mem_operatorDomain_iff {U : phaseSpace Ω} :
    U ∈ operatorDomain Ω ↔ MemOperatorDomain Ω U :=
  Iff.rfl

variable (Ω) in
/-- The formula of the wave operator, on the whole phase space:
$(u, v) \mapsto (-\tilde v, -\Delta u)$, where $\tilde v \in H^1_0(\Omega)$ is the preimage of
$v$ and $-\Delta u$ is the Dirichlet Laplacian of $\iota u$. Off $D(A)$ the junk values apply:
$\tilde v = 0$ when $v \notin H^1_0(\Omega)$, and $-\Delta u = 0$ when
$\iota u \notin D(-\Delta)$. The preimage is `toSobolevZero` and the Laplacian is
`dirichletLaplacianApply`. -/
def operatorApply (U : phaseSpace Ω) : phaseSpace Ω :=
  phaseSpace.mk Ω (-toSobolevZero Ω U.snd) (dirichletLaplacianApply Ω
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst))

/-- The first component of `Wave.operatorApply` at $(u, v)$ is $-\tilde v$. -/
theorem operatorApply_fst (U : phaseSpace Ω) :
    (operatorApply Ω U).fst = -toSobolevZero Ω U.snd :=
  rfl

/-- The second component of `Wave.operatorApply` at $(u, v)$ is $-\Delta u$. -/
theorem operatorApply_snd (U : phaseSpace Ω) :
    (operatorApply Ω U).snd = dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        U.fst) :=
  rfl

/-- For $U, V \in D(A)$, the first component of `Wave.operatorApply` is additive: it is the same at
$U + V$ as for the sum of the values at $U$ and $V$. -/
theorem operatorApply_add_fst {U V : phaseSpace Ω} (hU : MemOperatorDomain Ω U)
    (hV : MemOperatorDomain Ω V) :
    (operatorApply Ω (U + V)).fst = (operatorApply Ω U + operatorApply Ω V).fst := by
  change -toSobolevZero Ω (U.snd + V.snd) = -toSobolevZero Ω U.snd + -toSobolevZero Ω V.snd
  rw [toSobolevZero_add hU.2 hV.2, neg_add]

/-- For $U, V \in D(A)$, the second component of `Wave.operatorApply` is additive. -/
theorem operatorApply_add_snd {U V : phaseSpace Ω} (hU : MemOperatorDomain Ω U)
    (hV : MemOperatorDomain Ω V) :
    (operatorApply Ω (U + V)).snd = (operatorApply Ω U + operatorApply Ω V).snd := by
  change dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (U.fst + V.fst)) = _ + _
  rw [_root_.map_add]
  exact dirichletLaplacianApply_add hU.1 hV.1

/-- `Wave.operatorApply` is additive on $D(A)$: $A(U + V) = AU + AV$ for $U, V \in D(A)$. -/
theorem operatorApply_add {U V : phaseSpace Ω} (hU : MemOperatorDomain Ω U)
    (hV : MemOperatorDomain Ω V) :
    operatorApply Ω (U + V) = operatorApply Ω U + operatorApply Ω V :=
  phaseSpace.ext (operatorApply_add_fst hU hV) (operatorApply_add_snd hU hV)

/-- For $U \in D(A)$ and $c \in \mathbb{R}$, the first component of `Wave.operatorApply` at $cU$ is
$c$ times its value at $U$. -/
theorem operatorApply_smul_fst (c : ℝ) {U : phaseSpace Ω} (hU : MemOperatorDomain Ω U) :
    (operatorApply Ω (c • U)).fst = (c • operatorApply Ω U).fst := by
  change -toSobolevZero Ω (c • U.snd) = c • -toSobolevZero Ω U.snd
  rw [toSobolevZero_smul c hU.2, smul_neg]

/-- For $U \in D(A)$ and $c \in \mathbb{R}$, the second component of `Wave.operatorApply` at $cU$ is
$c$ times its value at $U$. -/
theorem operatorApply_smul_snd (c : ℝ) {U : phaseSpace Ω} (hU : MemOperatorDomain Ω U) :
    (operatorApply Ω (c • U)).snd = (c • operatorApply Ω U).snd := by
  change dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (c • U.fst)) = c • _
  rw [_root_.map_smul]
  exact dirichletLaplacianApply_smul c hU.1

/-- `Wave.operatorApply` is homogeneous on $D(A)$: $A(cU) = c \, AU$ for $U \in D(A)$ and
$c \in \mathbb{R}$. -/
theorem operatorApply_smul (c : ℝ) {U : phaseSpace Ω} (hU : MemOperatorDomain Ω U) :
    operatorApply Ω (c • U) = c • operatorApply Ω U :=
  phaseSpace.ext (operatorApply_smul_fst c hU) (operatorApply_smul_snd c hU)

variable (Ω) in
/-- The **wave operator** $A$ on the phase space $H^1_0(\Omega) \times L^2(\Omega)$: the unbounded
operator with domain $D(A) = D(-\Delta) \times H^1_0(\Omega)$ and
$$A(u, v) = (-v, -\Delta u).$$
This is (35) of [brezis2011functional], §10.3, with the weak domain $D(-\Delta)$.

It is a `LinearPMap` with domain `Wave.operatorDomain` and values `Wave.operatorApply`. The
first component $-v$ is read in $H^1_0(\Omega)$ as $-\tilde v$, and $-\Delta u$ is the Dirichlet
Laplacian `dirichletLaplacian` of $\iota u$. -/
def operator : phaseSpace Ω →ₗ.[ℝ] phaseSpace Ω where
  domain := operatorDomain Ω
  toFun :=
    { toFun := fun U ↦ operatorApply Ω U
      map_add' := fun U V ↦ operatorApply_add U.2 V.2
      map_smul' := fun c U ↦ operatorApply_smul c U.2 }

/-- The domain of `Wave.operator` is `Wave.operatorDomain`. -/
@[simp]
theorem operator_domain : (operator Ω).domain = operatorDomain Ω :=
  rfl

/-- A point $(u, v)$ lies in the domain of the wave operator if and only if $\iota u \in D(-\Delta)$
and $v \in H^1_0(\Omega)$. -/
theorem mem_operator_domain_iff {U : phaseSpace Ω} :
    U ∈ (operator Ω).domain ↔
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst
        ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero N 1 2 Ω,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
          = U.snd :=
  Iff.rfl

/-- A point of the domain of the wave operator satisfies `Wave.MemOperatorDomain`. -/
theorem memOperatorDomain_of_mem {U : phaseSpace Ω} (hU : U ∈ (operator Ω).domain) :
    MemOperatorDomain Ω U :=
  hU

/-- The value of the wave operator is `Wave.operatorApply`. -/
theorem operator_apply (U : (operator Ω).domain) : operator Ω U = operatorApply Ω U :=
  rfl

/-- The first component of $A(u, v)$ is $-\tilde v$, that is, $-v$ read in $H^1_0(\Omega)$. -/
theorem operator_apply_fst (U : (operator Ω).domain) :
    (operator Ω U).fst = -toSobolevZero Ω (U : phaseSpace Ω).snd :=
  rfl

/-- The second component of $A(u, v)$ is $-\Delta u$, the Dirichlet Laplacian of $\iota u$. -/
theorem operator_apply_snd (U : (operator Ω).domain) :
    (operator Ω U).snd = dirichletLaplacian Ω
      ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (U : phaseSpace Ω).fst, (mem_operator_domain_iff.1 U.2).1⟩ :=
  rfl

/-- The first component of $A(u, v)$, read in $L^2(\Omega)$ through $\iota$, is $-v$. -/
theorem fnL_operator_apply_fst (U : (operator Ω).domain) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (operator Ω U).fst = -(U : phaseSpace Ω).snd := by
  rw [operator_apply_fst, _root_.map_neg, fnL_toSobolevZero (mem_operator_domain_iff.1 U.2).2]


/-! ### Maximal monotonicity of $A + I$ -/

/-- Let $E$ be a normed group and $F$ a real inner product space, let $x \in E$ and $y, e \in F$
with $\|e\| \le \|x\|$, and let $a = -\langle e, y \rangle$. Then $0 \le a + \|x\|^2 + \|y\|^2$,
since $\langle e, y \rangle \le \|e\| \|y\| \le \|x\| \|y\| \le \frac12 (\|x\|^2 + \|y\|^2)$. -/
theorem nonneg_add_sq_of_eq_neg_inner {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : E) (y : F) {a : ℝ} {e : F} (ha : a = -⟪e, y⟫_ℝ) (he : ‖e‖ ≤ ‖x‖) :
    0 ≤ a + (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [ha]
  have h1 := abs_real_inner_le_norm e y
  have h3 := le_abs_self ⟪e, y⟫_ℝ
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_le_mul_of_nonneg_right he (norm_nonneg y),
    norm_nonneg e, norm_nonneg y]

/-- For every $U = (u, v) \in D(A)$,
$$\langle AU, U \rangle = -\langle u, v \rangle_{L^2}.$$
This is the computation before (36) in the proof of Theorem 10.7 of [brezis2011functional].

The inner product on the right is that of $\iota u$ and $v$ in $L^2(\Omega)$. The Dirichlet-form
terms $-\int_\Omega \nabla \tilde v \cdot \nabla u$ of $\langle -\tilde v, u \rangle_{H^1}$ and
$\int_\Omega \nabla u \cdot \nabla \tilde v = \langle -\Delta u, v \rangle$ cancel. -/
theorem operator_inner_self_eq (U : (operator Ω).domain) :
    ⟪operator Ω U, (U : phaseSpace Ω)⟫_ℝ
      = -⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          (U : phaseSpace Ω).fst, (U : phaseSpace Ω).snd⟫_ℝ := by
  have hmem := mem_operator_domain_iff.1 U.2
  have hwv : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω (U : phaseSpace Ω).snd) = (U : phaseSpace Ω).snd :=
    fnL_toSobolevZero hmem.2
  have h0 : ⟪operator Ω U, (U : phaseSpace Ω)⟫_ℝ
      = ⟪-toSobolevZero Ω (U : phaseSpace Ω).snd, (U : phaseSpace Ω).fst⟫_ℝ
        + ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
            (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst,
            hmem.1⟩, (U : phaseSpace Ω).snd⟫_ℝ :=
    rfl
  have h1 : ⟪-toSobolevZero Ω (U : phaseSpace Ω).snd, (U : phaseSpace Ω).fst⟫_ℝ
      = -⟪toSobolevZero Ω (U : phaseSpace Ω).snd, (U : phaseSpace Ω).fst⟫_ℝ :=
    inner_neg_left (𝕜 := ℝ) (toSobolevZero Ω (U : phaseSpace Ω).snd) (U : phaseSpace Ω).fst
  have h2 := inner_sobolevZero_eq (toSobolevZero Ω (U : phaseSpace Ω).snd) (U : phaseSpace Ω).fst
  have h3 : ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst, hmem.1⟩,
      (U : phaseSpace Ω).snd⟫_ℝ
      = dirichletForm Ω ((U : phaseSpace Ω).fst : SobolevEuclidean N 1 2 Ω)
        (toSobolevZero Ω (U : phaseSpace Ω).snd : SobolevEuclidean N 1 2 Ω) :=
    (congrArg (fun z ↦ ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst, hmem.1⟩,
      z⟫_ℝ) hwv).symm.trans (dirichletLaplacian_inner_eq_dirichletForm _
        (U : phaseSpace Ω).fst.2 rfl (toSobolevZero Ω (U : phaseSpace Ω).snd).2)
  have h4 : dirichletForm Ω ((U : phaseSpace Ω).fst : SobolevEuclidean N 1 2 Ω)
      (toSobolevZero Ω (U : phaseSpace Ω).snd : SobolevEuclidean N 1 2 Ω)
      = dirichletForm Ω (toSobolevZero Ω (U : phaseSpace Ω).snd : SobolevEuclidean N 1 2 Ω)
        ((U : phaseSpace Ω).fst : SobolevEuclidean N 1 2 Ω) :=
    (dirichletForm_isHermitian Ω _ _).trans (conj_trivial _)
  have h5 : ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω (U : phaseSpace Ω).snd),
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (U : phaseSpace Ω).fst⟫_ℝ
      = ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          (U : phaseSpace Ω).fst, (U : phaseSpace Ω).snd⟫_ℝ :=
    (congrArg (fun z ↦ ⟪z, SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst⟫_ℝ)
        hwv).trans (real_inner_comm _ _)
  linarith

/-- The operator $A + I$ is monotone: for every $U = (u, v) \in D(A)$,
$$0 \le \langle AU, U \rangle + \|U\|^2.$$
This is part (i) of the proof of Theorem 10.7 of [brezis2011functional].

Indeed $\langle AU, U \rangle = -\langle u, v \rangle_{L^2} \ge -\|u\|_{L^2} \|v\|_{L^2} \ge
-\frac12 (\|u\|_{H^1}^2 + \|v\|_{L^2}^2)$. -/
theorem operator_add_id_inner_self_nonneg (U : (operator Ω).domain) :
    0 ≤ ⟪operator Ω U, (U : phaseSpace Ω)⟫_ℝ + ‖(U : phaseSpace Ω)‖ ^ 2 := by
  have h := nonneg_add_sq_of_eq_neg_inner (U : phaseSpace Ω).fst (U : phaseSpace Ω).snd
    (operator_inner_self_eq U) (SobolevMultiIndexZero.norm_fnL_apply_le _)
  rw [phaseSpace.norm_sq_eq]
  exact h

/-- The operator $A + I$ is monotone in the sense of `LinearPMap.IsMonotone`:
$0 \le \langle (A + I) U, U \rangle$ for every $U \in D(A)$. -/
theorem operator_add_id_isMonotone :
    ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsMonotone := fun U ↦ by
  have h1 : ⟪((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω) U,
      (U : phaseSpace Ω)⟫_ℝ = ⟪(U : phaseSpace Ω), (U : phaseSpace Ω)⟫_ℝ
        + ⟪operator Ω U, (U : phaseSpace Ω)⟫_ℝ :=
    inner_add_left _ _ _
  have h2 : ⟪(U : phaseSpace Ω), (U : phaseSpace Ω)⟫_ℝ = ‖(U : phaseSpace Ω)‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have h3 := operator_add_id_inner_self_nonneg U
  change 0 ≤ ⟪((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω) U,
    (U : phaseSpace Ω)⟫_ℝ
  linarith


/-- The range of $A + 2I$ is the whole phase space: for every $F = (f, g)$ there is $U \in D(A)$
with
$$2U + AU = F.$$
This is part (ii) of the proof of Theorem 10.7 of [brezis2011functional], (36)–(37).

The Lean statement writes $2U + AU$ as $U + (U + AU)$. The proof solves $4u - \Delta u = 2f + g$
in $D(-\Delta)$ (`dirichletLaplacian_exists_smul_add_apply_eq` with $\lambda = 4$, on every open
set) and takes $v = 2u - f$. -/
theorem operator_exists_two_smul_add_apply_eq (F : phaseSpace Ω) :
    ∃ U : (operator Ω).domain,
      (U : phaseSpace Ω) + ((U : phaseSpace Ω) + operator Ω U) = F := by
  obtain ⟨x, hx⟩ := dirichletLaplacian_exists_smul_add_apply_eq (Ω := Ω) (c := 4) (by norm_num)
    (F.snd + (2 : ℝ) • SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume F.fst)
  obtain ⟨v', hv', hv'x⟩ := dirichletLaplacian_exists_lift x
  have hux : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
    (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) = x := hv'x
  have hmem : MemOperatorDomain Ω (phaseSpace.mk Ω (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst))) := by
    refine ⟨?_, ⟨_, rfl⟩⟩
    change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) ∈ dirichletLaplacianDomain Ω
    rw [hux]
    exact x.2
  refine ⟨⟨_, hmem⟩, phaseSpace.ext ?_ ?_⟩
  · change (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) + ((⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)
      + -toSobolevZero Ω (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        1 2 Ω volume ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst))) = F.fst
    have hw := toSobolevZero_fnL ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst)
    exact (congrArg (fun z ↦ (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)
      + ((⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) + -z)) hw).trans
      (by module)
  · change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst)
      + (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst)
        + dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
            (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω))) = F.snd
    have h1 : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst)
        = (2 : ℝ) • (x : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
          - SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
            F.fst :=
      (_root_.map_sub (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        1 2 Ω volume) ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)) F.fst).trans
        (congrArg (fun z ↦ z - SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume F.fst)
          ((_root_.map_smul (SobolevMultiIndexZero.fnL ℝ
            (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume) (2 : ℝ)
            (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)).trans
            (congrArg (fun z ↦ (2 : ℝ) • z) hux)))
    have hx' : (4 : ℝ) • (x : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        + dirichletLaplacianApply Ω x = F.snd + (2 : ℝ) • SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume F.fst := hx
    refine (congrArg₂ (fun a b ↦ a + (a + dirichletLaplacianApply Ω b)) h1 hux).trans ?_
    linear_combination (norm := module) hx'

/-- The operator $A + I$, with domain $D(A)$, is maximal monotone on the phase space
$H^1_0(\Omega) \times L^2(\Omega)$, for every open set $\Omega$. This is parts (i) and (ii) of
the proof of Theorem 10.7 of [brezis2011functional].

The operator $A + I$ is `LinearMap.id +ᵥ Wave.operator Ω`. Its range condition
$R(I + (A + I)) = H$ is $R(A + 2I) = H$ (`Wave.operator_exists_two_smul_add_apply_eq`). -/
theorem operator_add_id_isMaximalMonotone :
    ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsMaximalMonotone where
  isMonotone := operator_add_id_isMonotone
  exists_add_apply_eq F := by
    obtain ⟨U, hU⟩ := operator_exists_two_smul_add_apply_eq F
    exact ⟨U, hU⟩

/-! ### The solutions of the wave equation -/

variable (Ω) in
/-- A **solution of the wave equation** with data $u_0 \in H^1_0(\Omega)$ and $v_0 \in L^2(\Omega)$
is a curve $u : \mathbb{R} \to L^2(\Omega)$ such that $u \in C^2([0, \infty); L^2(\Omega))$,
$u \in C^1([0, \infty); H^1_0(\Omega))$ through the inclusion $\iota$, $u(t) \in D(-\Delta)$ for
$t \ge 0$ with $u \in C([0, \infty); D(-\Delta))$, and
$$u''(t) = \Delta u(t) \quad (t \ge 0), \qquad u(0) = u_0, \qquad u'(0) = v_0.$$
This is the problem (27)–(30) of [brezis2011functional], §10.3, in the class (31) of Theorem
10.7, with the weak domain $D(-\Delta)$ in place of $H^2(\Omega) \cap H^1_0(\Omega)$.

Only the values of $u$ on $[0, \infty)$ are constrained. The derivatives are taken within
$[0, \infty)$, so they are one-sided at $t = 0$. The condition $u(0) = u_0$ is
$u(0) = \iota u_0$, and $u \in C([0, \infty); D(-\Delta))$ is `LinearPMap.ContDiffOnPowDomain`
for `dirichletLaplacian` with $j = 1$ and order $0$. -/
structure IsSolution (u₀ : SobolevEuclideanZero N 1 2 Ω)
    (v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop where
  /-- The curve $u$ is in $C^2([0, \infty); L^2(\Omega))$. -/
  contDiffOn : ContDiffOn ℝ 2 u (Ici 0)
  /-- The curve $u$ is in $C^1([0, \infty); H^1_0(\Omega))$, through the inclusion $\iota$. -/
  contDiffOnThrough : Bochner.ContDiffOnThrough (SobolevMultiIndexZero.fnL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume : SobolevEuclideanZero N 1 2 Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) 1 u (Ici 0)
  /-- For $t \ge 0$, $u(t) \in D(-\Delta)$. -/
  mem_domain : ∀ t, 0 ≤ t → u t ∈ (dirichletLaplacian Ω).domain
  /-- The curve $u$ is in $C([0, \infty); D(-\Delta))$ for the graph norm of $-\Delta$. -/
  contDiffOnPowDomain : (dirichletLaplacian Ω).ContDiffOnPowDomain 0 1 u (Ici 0)
  /-- The wave equation $u''(t) = \Delta u(t)$ for $t \ge 0$, written $u'' = -(-\Delta) u$ with the
  second derivative within $[0, \infty)$. -/
  eqn : ∀ t (ht : 0 ≤ t),
    iteratedDerivWithin 2 u (Ici 0) t = -(dirichletLaplacian Ω ⟨u t, mem_domain t ht⟩)
  /-- The initial condition $u(0) = \iota u_0$. -/
  apply_zero : u 0 = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume u₀
  /-- The initial condition $u'(0) = v_0$, with the derivative within $[0, \infty)$. -/
  derivWithin_zero : derivWithin u (Ici 0) 0 = v₀

/-! ### From the phase space to $L^2(\Omega)$ -/

section Translation

variable {U : ℝ → phaseSpace Ω} {U₀ : phaseSpace Ω}

/-- If a curve $U$ in the phase space is $C^1$ on $[0, \infty)$, then its first component is $C^1$
on $[0, \infty)$ in $H^1_0(\Omega)$. -/
theorem contDiffOn_fst_of_contDiffOn (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    ContDiffOn ℝ 1 (fun t ↦ (U t).fst) (Ici 0) :=
  (phaseSpace.fstL Ω).contDiff.comp_contDiffOn hU1

/-- If a curve $U$ in the phase space is $C^1$ on $[0, \infty)$, then its second component is $C^1$
on $[0, \infty)$ in $L^2(\Omega)$. -/
theorem contDiffOn_snd_of_contDiffOn (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    ContDiffOn ℝ 1 (fun t ↦ (U t).snd) (Ici 0) :=
  (phaseSpace.sndL Ω).contDiff.comp_contDiffOn hU1

/-- For $U = (u, v) \in D(A)$, the first component of $-AU$ is $\tilde v$. -/
theorem neg_operator_apply_fst (V : (operator Ω).domain) :
    (-(operator Ω V)).fst = toSobolevZero Ω (V : phaseSpace Ω).snd :=
  neg_neg (toSobolevZero Ω (V : phaseSpace Ω).snd)

/-- For $U = (u, v) \in D(A)$, the second component of $-AU$ is $-(-\Delta u)$. -/
theorem neg_operator_apply_snd (V : (operator Ω).domain) :
    (-(operator Ω V)).snd = -(dirichletLaplacian Ω
      ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (V : phaseSpace Ω).fst, (mem_operator_domain_iff.1 V.2).1⟩) :=
  rfl

/-- The first component of $U' + AU = 0$: if $U = (u, v)$ solves $U' + AU = 0$ on $[0, \infty)$,
then $u' = \tilde v$ in $H^1_0(\Omega)$, with the derivative within $[0, \infty)$ at every
$t \ge 0$. -/
theorem hasDerivWithinAt_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ (U t).fst) (toSobolevZero Ω (U t).snd) (Ici 0) t := by
  have h := (phaseSpace.fstL Ω).hasFDerivAt.comp_hasDerivWithinAt t (hU.hasDerivWithinAt t ht)
  rw [phaseSpace.fstL_apply, neg_operator_apply_fst] at h
  exact h

/-- The second component of $U' + AU = 0$: if $U = (u, v)$ solves $U' + AU = 0$ on $[0, \infty)$,
then $v' = -(-\Delta u)$ in $L^2(\Omega)$, with the derivative within $[0, \infty)$ at every
$t \ge 0$. -/
theorem hasDerivWithinAt_snd (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ (U t).snd) (-(dirichletLaplacian Ω
      ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (U t).fst, (mem_operator_domain_iff.1 (hU.mem_domain t ht)).1⟩)) (Ici 0) t := by
  have h := (phaseSpace.sndL Ω).hasFDerivAt.comp_hasDerivWithinAt t (hU.hasDerivWithinAt t ht)
  rw [phaseSpace.sndL_apply, neg_operator_apply_snd] at h
  exact h

/-- If $U = (u, v)$ solves $U' + AU = 0$ on $[0, \infty)$ and $t \ge 0$, then
$\iota \tilde v(t) = v(t)$. -/
theorem fnL_toSobolevZero_snd (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω (U t).snd) = (U t).snd :=
  fnL_toSobolevZero (mem_operator_domain_iff.1 (hU.mem_domain t ht)).2

/-- If $U = (u, v)$ solves $U' + AU = 0$ on $[0, \infty)$, then $(\iota u)' = v$ in $L^2(\Omega)$,
with the derivative within $[0, \infty)$ at every $t \ge 0$. -/
theorem hasDerivWithinAt_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (U t).snd (Ici 0) t := by
  have h := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
    volume).hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_fst hU ht)
  rw [fnL_toSobolevZero_snd hU ht] at h
  exact h

/-- If $U = (u, v)$ solves $U' + AU = 0$ on $[0, \infty)$, then the derivative of $\iota u$ within
$[0, \infty)$ at $t \ge 0$ is $v(t)$. -/
theorem derivWithin_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    derivWithin (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0) t
      = (U t).snd :=
  (hasDerivWithinAt_fnL_fst hU ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- If $U = (u, v)$ solves $U' + AU = 0$ on $[0, \infty)$ and is $C^1$ there, then
$\iota u \in C^2([0, \infty); L^2(\Omega))$. -/
theorem contDiffOn_two_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U)
    (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    ContDiffOn ℝ 2 (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
  refine ⟨fun t ht ↦ (hasDerivWithinAt_fnL_fst hU ht).differentiableWithinAt,
    fun h ↦ by simp at h, ?_⟩
  exact (contDiffOn_snd_of_contDiffOn hU1).congr fun t ht ↦ derivWithin_fnL_fst hU ht

/-- The wave equation for the first component: if $U = (u, v)$ solves $U' + AU = 0$ on
$[0, \infty)$, then $(\iota u)''(t) = -(-\Delta u(t))$ for $t \ge 0$, with the second derivative
within $[0, \infty)$. -/
theorem iteratedDerivWithin_two_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    iteratedDerivWithin 2 (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0) t
      = -(dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst,
        (mem_operator_domain_iff.1 (hU.mem_domain t ht)).1⟩) := by
  have e : iteratedDerivWithin 2 (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0)
      = derivWithin (derivWithin (fun t ↦ SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0)) (Ici 0) :=
    iteratedDerivWithin_succ.trans
      (congrArg (fun g ↦ derivWithin g (Ici 0)) iteratedDerivWithin_one)
  have e2 : derivWithin (derivWithin (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0)) (Ici 0) t
      = derivWithin (fun t ↦ (U t).snd) (Ici 0) t :=
    derivWithin_congr (fun s hs ↦ derivWithin_fnL_fst hU hs) (derivWithin_fnL_fst hU ht)
  exact (congrFun e t).trans
    (e2.trans ((hasDerivWithinAt_snd hU ht).derivWithin (uniqueDiffOn_Ici 0 t ht)))

/-- If $U = (u, v)$ solves $U' + AU = 0$ on $[0, \infty)$ and is $C^1$ there, then
$\iota u \in C([0, \infty); D(-\Delta))$, because $-\Delta u = -v'$ is continuous. -/
theorem contDiffOnPowDomain_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U)
    (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    (dirichletLaplacian Ω).ContDiffOnPowDomain 0 1 (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0) := by
  rw [LinearPMap.contDiffOnPowDomain_iff dirichletLaplacian_isClosed]
  refine ⟨![fun t ↦ SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
    volume (U t).fst, fun t ↦ -derivWithin (fun t ↦ (U t).snd) (Ici 0) t], fun t _ ↦ rfl, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · exact ((SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
        volume).contDiff.comp_contDiffOn (contDiffOn_fst_of_contDiffOn hU1)).of_le (by simp)
    · exact contDiffOn_zero.2 ((contDiffOn_snd_of_contDiffOn hU1).continuousOn_derivWithin
        (uniqueDiffOn_Ici 0) le_rfl).neg
  · intro t ht i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    change ∃ h : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume (U t).fst ∈ (dirichletLaplacian Ω).domain, dirichletLaplacian Ω
        ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          (U t).fst, h⟩ = -derivWithin (fun t ↦ (U t).snd) (Ici 0) t
    refine ⟨(mem_operator_domain_iff.1 (hU.mem_domain t ht)).1, ?_⟩
    exact (neg_neg _).symm.trans (congrArg Neg.neg
      ((hasDerivWithinAt_snd hU ht).derivWithin (uniqueDiffOn_Ici 0 t ht)).symm)

/-- **From the phase space to the wave equation.** Let $U$ solve $U' + AU = 0$ on $[0, \infty)$ with
$U(0) = (u_0, v_0)$, and let $U$ be $C^1$ on $[0, \infty)$. Then the first component of $U$,
read in $L^2(\Omega)$ through $\iota$, is a solution of the wave equation with data
$(u_0, v_0)$. This is the existence part of the proof of Theorem 10.7 of [brezis2011functional].

The solution of $U' + AU = 0$ is `LinearPMap.IsSolutionOn` for `Wave.operator Ω`, and the
solution of the wave equation is `Wave.IsSolution`. -/
theorem isSolution_of_isSolutionOn {u₀ : SobolevEuclideanZero N 1 2 Ω}
    {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hU : (operator Ω).IsSolutionOn (phaseSpace.mk Ω u₀ v₀) (Ici 0) U)
    (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    IsSolution Ω u₀ v₀ fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst where
  contDiffOn := contDiffOn_two_fnL_fst hU hU1
  contDiffOnThrough := ⟨fun t ↦ (U t).fst, contDiffOn_fst_of_contDiffOn hU1, fun _ _ ↦ rfl⟩
  mem_domain t ht := (mem_operator_domain_iff.1 (hU.mem_domain t ht)).1
  contDiffOnPowDomain := contDiffOnPowDomain_fnL_fst hU hU1
  eqn _ ht := iteratedDerivWithin_two_fnL_fst hU ht
  apply_zero := congrArg (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
    1 2 Ω volume) (congrArg phaseSpace.fst hU.apply_zero)
  derivWithin_zero := (derivWithin_fnL_fst hU le_rfl).trans (congrArg phaseSpace.snd hU.apply_zero)

end Translation

/-! ### Existence: the shifted semigroup of $A + I$ -/

/-- The operator $1 \cdot I + A$ is $I + A$. -/
theorem one_smul_id_vadd_operator :
    (((1 : ℝ) • LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω)
      = (LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω := by
  rw [one_smul]

variable (Ω) in
/-- The **solution in the phase space** with data $(u_0, v_0)$:
$$U(t) = e^t S_{A+I}(t) (u_0, v_0),$$
where $S_{A+I}$ is the semigroup generated by $-(A + I)$ (`LinearPMap.semigroup`). The factor
$e^t$ is the shift of Remark 6 of chapter 7. This is the solution of the proof of Theorem 10.7
of [brezis2011functional].

The definition applies to all $t \in \mathbb{R}$ and all data. For data in $D(A)$ it solves
$U' + AU = 0$ on $[0, \infty)$ (`Wave.isSolutionOn_phaseSolution`). -/
def phaseSolution (u₀ : SobolevEuclideanZero N 1 2 Ω)
    (v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (t : ℝ) :
    phaseSpace Ω :=
  Real.exp t • ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).semigroup t
    (phaseSpace.mk Ω u₀ v₀)

variable {u₀ : SobolevEuclideanZero N 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- If $\iota u_0 \in D(-\Delta)$ and $v_0 \in H^1_0(\Omega)$, then $(u_0, v_0) \in D(A)$. -/
theorem memOperatorDomain_mk
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    MemOperatorDomain Ω (phaseSpace.mk Ω u₀ v₀) :=
  ⟨hu₀, hv₀⟩

/-- For data $(u_0, v_0) \in D(A)$, the phase-space solution $U(t) = e^t S_{A+I}(t)(u_0, v_0)$
solves $U' + AU = 0$ on $[0, \infty)$ with $U(0) = (u_0, v_0)$. This is Theorem 7.4 for $A + I$
with the shift $e^t$ of Remark 6 of chapter 7. -/
theorem isSolutionOn_phaseSolution (h₀ : MemOperatorDomain Ω (phaseSpace.mk Ω u₀ v₀)) :
    (operator Ω).IsSolutionOn (phaseSpace.mk Ω u₀ v₀) (Ici 0) (phaseSolution Ω u₀ v₀) := by
  have hV : ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsSolutionOn
      (phaseSpace.mk Ω u₀ v₀) (Ici 0) fun t ↦
        ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).semigroup t
          (phaseSpace.mk Ω u₀ v₀) :=
    operator_add_id_isMaximalMonotone.isSolutionOn_semigroup ⟨phaseSpace.mk Ω u₀ v₀, h₀⟩
  have hV' : (((1 : ℝ) • LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsSolutionOn
      (phaseSpace.mk Ω u₀ v₀) (Ici 0) fun t ↦
        ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).semigroup t
          (phaseSpace.mk Ω u₀ v₀) := by
    rw [one_smul_id_vadd_operator]
    exact hV
  have := (LinearPMap.isSolutionOn_smul_id_vadd_iff (c := 1)).1 hV'
  have e : (fun t ↦ Real.exp (1 * t) • ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω)
      +ᵥ operator Ω).semigroup t (phaseSpace.mk Ω u₀ v₀)) = phaseSolution Ω u₀ v₀ :=
    funext fun t ↦ by
      rw [one_mul]
      rfl
  rw [e] at this
  exact this

/-- For data $(u_0, v_0) \in D(A)$, the phase-space solution is $C^1$ on $[0, \infty)$ in the phase
space. -/
theorem contDiffOn_phaseSolution (h₀ : MemOperatorDomain Ω (phaseSpace.mk Ω u₀ v₀)) :
    ContDiffOn ℝ 1 (phaseSolution Ω u₀ v₀) (Ici 0) :=
  Real.contDiff_exp.contDiffOn.smul
    (operator_add_id_isMaximalMonotone.contDiffOn_semigroup_apply ⟨phaseSpace.mk Ω u₀ v₀, h₀⟩)

variable (Ω) in
/-- The **solution of the wave equation** with data $(u_0, v_0)$: $u(t)$ is the first component of
the phase-space solution $U(t) = e^t S_{A+I}(t)(u_0, v_0)$ (`Wave.phaseSolution`), read in
$L^2(\Omega)$ through $\iota$. For $\iota u_0 \in D(-\Delta)$ and $v_0 \in H^1_0(\Omega)$ it
solves the wave equation (`Wave.isSolution_solution`). This is the solution of Theorem 10.7 of
[brezis2011functional]. -/
def solution (u₀ : SobolevEuclideanZero N 1 2 Ω)
    (v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
    (phaseSolution Ω u₀ v₀ t).fst

/-- **Existence of the solution.** If $\iota u_0 \in D(-\Delta)$ and $v_0 \in H^1_0(\Omega)$, then
`Wave.solution Ω u₀ v₀` solves the wave equation with data $(u_0, v_0)$. This is the existence
part of Theorem 10.7 of [brezis2011functional], where the condition on $u_0$ is
$u_0 \in H^2(\Omega) \cap H^1_0(\Omega)$. -/
theorem isSolution_solution
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    IsSolution Ω u₀ v₀ (solution Ω u₀ v₀) :=
  isSolution_of_isSolutionOn (isSolutionOn_phaseSolution (memOperatorDomain_mk hu₀ hv₀))
    (contDiffOn_phaseSolution (memOperatorDomain_mk hu₀ hv₀))

/-! ### Uniqueness: from $L^2(\Omega)$ back to the phase space -/

/-- Let $f : \mathbb{R} \to H^1_0(\Omega)$ and $g : \mathbb{R} \to L^2(\Omega)$ have the derivatives
$a$ and $b$ within a set $s$ at $t$. Then the curve $t \mapsto (f(t), g(t))$ in the phase space
has the derivative $(a, b)$ within $s$ at $t$. -/
theorem phaseSpace.hasDerivWithinAt_mk {f : ℝ → SobolevEuclideanZero N 1 2 Ω}
    {g : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {a : SobolevEuclideanZero N 1 2 Ω}
    {b : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {s : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f a s t) (hg : HasDerivWithinAt g b s t) :
    HasDerivWithinAt (fun t ↦ phaseSpace.mk Ω (f t) (g t)) (phaseSpace.mk Ω a b) s t :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (SobolevEuclideanZero N 1 2 Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))).symm.hasFDerivAt
    |>.comp_hasDerivWithinAt t (hf.prodMk hg)

/-- **Uniqueness for $U' + AU = 0$.** Two solutions $U_1$ and $U_2$ of $U' + AU = 0$ on
$[0, \infty)$ with the same initial value agree on $[0, \infty)$. This is the uniqueness part of
the proof of Theorem 10.7 of [brezis2011functional].

No regularity beyond `LinearPMap.IsSolutionOn` is assumed. The proof applies the monotonicity of
$A + I$ (`LinearPMap.IsMonotone.eqOn_of_isSolutionOn`) to $e^{-t} U_1$ and $e^{-t} U_2$, by
Remark 6 of chapter 7. -/
theorem operator_eqOn_of_isSolutionOn {U₀ : phaseSpace Ω} {U₁ U₂ : ℝ → phaseSpace Ω}
    (h₁ : (operator Ω).IsSolutionOn U₀ (Ici 0) U₁) (h₂ : (operator Ω).IsSolutionOn U₀ (Ici 0) U₂) :
    EqOn U₁ U₂ (Ici 0) := by
  have hm := operator_add_id_isMonotone (Ω := Ω)
  rw [← one_smul_id_vadd_operator] at hm
  have key : ∀ U : ℝ → phaseSpace Ω, (operator Ω).IsSolutionOn U₀ (Ici 0) U →
      (((1 : ℝ) • LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsSolutionOn U₀
        (Ici 0) fun t ↦ Real.exp (-t) • U t := fun U hU ↦ by
    refine (LinearPMap.isSolutionOn_smul_id_vadd_iff (c := 1)).2 ?_
    convert hU using 1
    funext t
    simp only [smul_smul, ← Real.exp_add, one_mul, add_neg_cancel, Real.exp_zero, one_smul]
  intro t ht
  have h := hm.eqOn_of_isSolutionOn (key U₁ h₁) (key U₂ h₂) ht
  have h' := congrArg (fun z ↦ Real.exp t • z) h
  simpa only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul] using h'

namespace IsSolution

variable {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- If $u$ solves the wave equation, then its $H^1_0$ preimage $t \mapsto \tilde u(t)$ is $C^1$ on
$[0, \infty)$ in $H^1_0(\Omega)$. -/
theorem contDiffOn_toSobolevZero (h : IsSolution Ω u₀ v₀ u) :
    ContDiffOn ℝ 1 (fun t ↦ toSobolevZero Ω (u t)) (Ici 0) := by
  obtain ⟨v, hv, huv⟩ := h.contDiffOnThrough
  exact hv.congr fun t ht ↦ toSobolevZero_eq (huv t ht).symm

/-- If $u$ solves the wave equation and $t \ge 0$, then $\iota \tilde u(t) = u(t)$. -/
theorem fnL_toSobolevZero_apply (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω (u t)) = u t := by
  obtain ⟨v, -, huv⟩ := h.contDiffOnThrough
  exact fnL_toSobolevZero ⟨v t, (huv t ht).symm⟩

/-- If $u$ solves the wave equation and $t \ge 0$, then $u'(t) \in H^1_0(\Omega)$, with the
derivative within $[0, \infty)$. -/
theorem exists_fnL_eq_derivWithin (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = derivWithin u (Ici 0) t := by
  obtain ⟨v, hv, huv⟩ := h.contDiffOnThrough
  exact ⟨derivWithin v (Ici 0) t, (Bochner.ContDiffOnThrough.derivWithin_eq hv huv le_rfl
    (uniqueDiffOn_Ici 0) ht).symm⟩

/-- If $u$ solves the wave equation and $t \ge 0$, then the derivative of $\tilde u$ within
$[0, \infty)$ at $t$ is the preimage $\widetilde{u'(t)}$ of $u'(t)$. -/
theorem hasDerivWithinAt_toSobolevZero (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ toSobolevZero Ω (u t))
      (toSobolevZero Ω (derivWithin u (Ici 0) t)) (Ici 0) t := by
  have h1 := (h.contDiffOn_toSobolevZero.differentiableOn one_ne_zero t ht).hasDerivWithinAt
  have h2 := Bochner.ContDiffOnThrough.derivWithin_eq h.contDiffOn_toSobolevZero
    (fun t ht ↦ (h.fnL_toSobolevZero_apply ht).symm) le_rfl (uniqueDiffOn_Ici 0) ht
  rw [toSobolevZero_eq h2.symm]
  exact h1

/-- If $u$ solves the wave equation and $t \ge 0$, then $u'$ has the derivative $-(-\Delta u(t))$
within $[0, \infty)$ at $t$. -/
theorem hasDerivWithinAt_derivWithin (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (derivWithin u (Ici 0)) (-(dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩))
      (Ici 0) t := by
  have hc := h.contDiffOn
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
    contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)] at hc
  have h2 := (hc.2.2.differentiableOn one_ne_zero t ht).hasDerivWithinAt
  have h3 : derivWithin (derivWithin u (Ici 0)) (Ici 0) t
      = -(dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩) :=
    (congrFun (iteratedDerivWithin_two u (Ici 0)) t).symm.trans (h.eqn t ht)
  rw [h3] at h2
  exact h2

/-- If $u$ solves the wave equation and $t \ge 0$, then $(\tilde u(t), u'(t)) \in D(A)$. -/
theorem memOperatorDomain (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    MemOperatorDomain Ω
      (phaseSpace.mk Ω (toSobolevZero Ω (u t)) (derivWithin u (Ici 0) t)) := by
  refine ⟨?_, h.exists_fnL_eq_derivWithin ht⟩
  change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
    (toSobolevZero Ω (u t)) ∈ dirichletLaplacianDomain Ω
  rw [h.fnL_toSobolevZero_apply ht]
  exact h.mem_domain t ht

/-- **From the wave equation to the phase space.** Let $u$ solve the wave equation with data
$(u_0, v_0)$. Then $U(t) = (\tilde u(t), u'(t))$ solves $U' + AU = 0$ on $[0, \infty)$ with
$U(0) = (u_0, v_0)$. Here $\tilde u(t) \in H^1_0(\Omega)$ is the preimage of $u(t)$
(`toSobolevZero`) and $u'$ is the derivative within $[0, \infty)$. This is the uniqueness part
of the proof of Theorem 10.7 of [brezis2011functional]. -/
theorem isSolutionOn (h : IsSolution Ω u₀ v₀ u) :
    (operator Ω).IsSolutionOn (phaseSpace.mk Ω u₀ v₀) (Ici 0)
      fun t ↦ phaseSpace.mk Ω (toSobolevZero Ω (u t)) (derivWithin u (Ici 0) t) where
  apply_zero := phaseSpace.ext (toSobolevZero_eq h.apply_zero.symm) h.derivWithin_zero
  mem_domain _ ht := h.memOperatorDomain ht
  hasDerivWithinAt t ht := by
    refine (phaseSpace.hasDerivWithinAt_mk (h.hasDerivWithinAt_toSobolevZero ht)
      (h.hasDerivWithinAt_derivWithin ht)).congr_deriv (phaseSpace.ext ?_ ?_)
    · exact (neg_operator_apply_fst ⟨phaseSpace.mk Ω (toSobolevZero Ω (u t))
        (derivWithin u (Ici 0) t), h.memOperatorDomain ht⟩).symm
    · exact (congrArg (fun z ↦ -(dirichletLaplacian Ω z))
        (Subtype.ext (h.fnL_toSobolevZero_apply ht).symm)).trans
        (neg_operator_apply_snd ⟨phaseSpace.mk Ω (toSobolevZero Ω (u t))
          (derivWithin u (Ici 0) t), h.memOperatorDomain ht⟩).symm

/-- **Uniqueness of the solution.** Two solutions of the wave equation with the same data
$(u_0, v_0)$ agree on $[0, \infty)$. This is the uniqueness part of Theorem 10.7 of
[brezis2011functional]. -/
theorem unique {v : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : IsSolution Ω u₀ v₀ u) (h' : IsSolution Ω u₀ v₀ v) : EqOn u v (Ici 0) := fun _ ht ↦
  (h.fnL_toSobolevZero_apply ht).symm.trans
    ((congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst)
      (operator_eqOn_of_isSolutionOn h.isSolutionOn h'.isSolutionOn ht)).trans
      (h'.fnL_toSobolevZero_apply ht))

/-- The data of a solution lie in $D(A)$: if a solution of the wave equation with data $(u_0, v_0)$
exists, then $\iota u_0 \in D(-\Delta)$ and $v_0 \in H^1_0(\Omega)$. -/
theorem memOperatorDomain_mk (h : IsSolution Ω u₀ v₀ u) :
    MemOperatorDomain Ω (phaseSpace.mk Ω u₀ v₀) :=
  h.isSolutionOn.apply_zero ▸ h.isSolutionOn.mem_domain 0 self_mem_Ici

/-- Every solution of the wave equation with data $(u_0, v_0)$ agrees with `Wave.solution Ω u₀ v₀`
on $[0, \infty)$. -/
theorem eqOn_solution (h : IsSolution Ω u₀ v₀ u) : EqOn u (solution Ω u₀ v₀) (Ici 0) := fun _ ht ↦
  (h.fnL_toSobolevZero_apply ht).symm.trans
    (congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst)
      (operator_eqOn_of_isSolutionOn h.isSolutionOn
        (isSolutionOn_phaseSolution h.memOperatorDomain_mk) ht))

end IsSolution

/-- **Existence and uniqueness for the wave equation**, on an arbitrary open set
$\Omega \subseteq \mathbb{R}^N$. Let $u_0 \in H^1_0(\Omega)$ with $\iota u_0 \in D(-\Delta)$,
and let $v_0 \in H^1_0(\Omega)$. Then there is a solution $u$ of the wave equation with data
$(u_0, v_0)$, and every solution $v$ with the same data agrees with $u$ on $[0, \infty)$. This
is Theorem 10.7 of [brezis2011functional].

The source's condition $u_0 \in H^2(\Omega) \cap H^1_0(\Omega)$ is $\iota u_0 \in D(-\Delta)$.
Uniqueness holds only on $[0, \infty)$, because `Wave.IsSolution` does not constrain negative
times. -/
theorem existsUnique_isSolution
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    ∃ u, IsSolution Ω u₀ v₀ u ∧ ∀ v, IsSolution Ω u₀ v₀ v → EqOn v u (Ici 0) :=
  ⟨solution Ω u₀ v₀, isSolution_solution hu₀ hv₀, fun _ hv ↦ hv.eqOn_solution⟩

/-! ### Linearity of the solution in the data -/

/-- In the phase space, $(u + u', v + v') = (u, v) + (u', v')$. -/
theorem phaseSpace.mk_add (u u' : SobolevEuclideanZero N 1 2 Ω)
    (v v' : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    phaseSpace.mk Ω (u + u') (v + v') = phaseSpace.mk Ω u v + phaseSpace.mk Ω u' v' :=
  rfl

/-- In the phase space, $(cu, cv) = c (u, v)$. -/
theorem phaseSpace.mk_smul (c : ℝ) (u : SobolevEuclideanZero N 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    phaseSpace.mk Ω (c • u) (c • v) = c • phaseSpace.mk Ω u v :=
  rfl

variable {u₀' : SobolevEuclideanZero N 1 2 Ω}
  {v₀' : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- The phase-space solution is additive in the data: the solution with data
$(u_0 + u_0', v_0 + v_0')$ is the sum of the solutions with data $(u_0, v_0)$ and
$(u_0', v_0')$, at every $t$. -/
theorem phaseSolution_add (t : ℝ) :
    phaseSolution Ω (u₀ + u₀') (v₀ + v₀') t
      = phaseSolution Ω u₀ v₀ t + phaseSolution Ω u₀' v₀' t := by
  unfold phaseSolution
  rw [phaseSpace.mk_add, _root_.map_add, smul_add]

/-- The phase-space solution is homogeneous in the data: the solution with data $(c u_0, c v_0)$ is
$c$ times the solution with data $(u_0, v_0)$, at every $t$. -/
theorem phaseSolution_smul (c : ℝ) (t : ℝ) :
    phaseSolution Ω (c • u₀) (c • v₀) t = c • phaseSolution Ω u₀ v₀ t := by
  unfold phaseSolution
  rw [phaseSpace.mk_smul, _root_.map_smul, smul_comm]

/-- The solution of the wave equation is additive in the data: the solution with data
$(u_0 + u_0', v_0 + v_0')$ is the sum of the solutions with data $(u_0, v_0)$ and
$(u_0', v_0')$, at every $t$. Each $S_{A+I}(t)$ is linear. -/
theorem solution_add (t : ℝ) :
    solution Ω (u₀ + u₀') (v₀ + v₀') t = solution Ω u₀ v₀ t + solution Ω u₀' v₀' t :=
  (congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst) (phaseSolution_add t)).trans
    (_root_.map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume) (phaseSolution Ω u₀ v₀ t).fst (phaseSolution Ω u₀' v₀' t).fst)

/-- The solution of the wave equation is homogeneous in the data: the solution with data
$(c u_0, c v_0)$ is $c$ times the solution with data $(u_0, v_0)$, at every $t$. -/
theorem solution_smul (c : ℝ) (t : ℝ) :
    solution Ω (c • u₀) (c • v₀) t = c • solution Ω u₀ v₀ t :=
  (congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst) (phaseSolution_smul c t)).trans
    (_root_.map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume) c (phaseSolution Ω u₀ v₀ t).fst)

/-! ### Conservation of energy -/

variable (Ω) in
/-- The **energy** of a curve $u : \mathbb{R} \to L^2(\Omega)$ at time $t$:
$$E(t) = \|u'(t)\|_{L^2}^2 + \int_\Omega |\nabla \tilde u(t)|^2,$$
where $u'$ is the derivative within $[0, \infty)$ and $\tilde u(t) \in H^1_0(\Omega)$ is the
preimage of $u(t)$. This is the energy of (32) in [brezis2011functional], §10.3.

The integral is written $\langle B \tilde u(t), \tilde u(t) \rangle_{H^1}$ with $B$ the operator
`Elliptic.dirichletOperator` of the Dirichlet form. -/
def energyFun (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (t : ℝ) :
    ℝ :=
  ‖derivWithin u (Ici 0) t‖ ^ 2
    + ⟪dirichletOperator Ω (toSobolevZero Ω (u t)), toSobolevZero Ω (u t)⟫_ℝ

namespace IsSolution

variable {u₀ : SobolevEuclideanZero N 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- If $u$ solves the wave equation and $t \ge 0$, then $\int_\Omega \nabla \tilde u(t) \cdot \nabla
\widetilde{u'(t)} = \langle -\Delta u(t), u'(t) \rangle$. -/
theorem inner_dirichletOperator_eq (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ⟪dirichletOperator Ω (toSobolevZero Ω (u t)),
      toSobolevZero Ω (derivWithin u (Ici 0) t)⟫_ℝ
      = ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, derivWithin u (Ici 0) t⟫_ℝ :=
  (inner_dirichletOperator _ _ _).trans
    ((dirichletLaplacian_inner_eq_dirichletForm ⟨u t, h.mem_domain t ht⟩
      (toSobolevZero Ω (u t)).2 (h.fnL_toSobolevZero_apply ht)
      (toSobolevZero Ω (derivWithin u (Ici 0) t)).2).symm.trans
      (congrArg (fun z ↦ ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, z⟫_ℝ)
        (fnL_toSobolevZero (h.exists_fnL_eq_derivWithin ht))))

/-- If $u$ solves the wave equation, then the energy has the derivative $0$ within $[0, \infty)$ at
every $t \ge 0$. Indeed $\frac{d}{dt} \|u'\|^2 = 2 \langle u', \Delta u \rangle$ and
$\frac{d}{dt} \int_\Omega |\nabla \tilde u|^2 = 2 \langle -\Delta u, u' \rangle$ cancel, as in
the proof of (32) of [brezis2011functional], §10.3. -/
theorem hasDerivWithinAt_energyFun (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (energyFun Ω u) 0 (Ici 0) t := by
  have h1 := (h.hasDerivWithinAt_derivWithin ht).norm_sq
  have hũ := h.hasDerivWithinAt_toSobolevZero ht
  have h2 : HasDerivWithinAt
      (fun t ↦ ⟪dirichletOperator Ω (toSobolevZero Ω (u t)), toSobolevZero Ω (u t)⟫_ℝ)
      (⟪dirichletOperator Ω (toSobolevZero Ω (u t)),
        toSobolevZero Ω (derivWithin u (Ici 0) t)⟫_ℝ
        + ⟪dirichletOperator Ω (toSobolevZero Ω (derivWithin u (Ici 0) t)),
          toSobolevZero Ω (u t)⟫_ℝ) (Ici 0) t :=
    ((dirichletOperator Ω).hasFDerivAt.comp_hasDerivWithinAt t hũ).inner ℝ hũ
  refine (h1.add h2).congr_deriv ?_
  have e1 := h.inner_dirichletOperator_eq ht
  have e2 := inner_dirichletOperator_comm _ (toSobolevZero Ω (derivWithin u (Ici 0) t))
    (toSobolevZero Ω (u t))
  have e3 : ⟪derivWithin u (Ici 0) t, -(dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩)⟫_ℝ
      = -⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, derivWithin u (Ici 0) t⟫_ℝ := by
    rw [inner_neg_right, real_inner_comm]
  rw [e2, e1, e3]
  ring

/-- If $u$ solves the wave equation, then its energy is constant on $[0, \infty)$: $E(t) = E(0)$ for
$t \ge 0$. -/
theorem energyFun_eq (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    energyFun Ω u t = energyFun Ω u 0 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rfl
  refine constant_of_derivWithin_zero (f := energyFun Ω u) (a := 0) (b := t)
    (fun x hx ↦
      ((h.hasDerivWithinAt_energyFun hx.1).mono Icc_subset_Ici_self).differentiableWithinAt)
    (fun x hx ↦ ((h.hasDerivWithinAt_energyFun hx.1).mono Icc_subset_Ici_self).derivWithin
      (uniqueDiffOn_Icc hpos x ⟨hx.1, hx.2.le⟩)) t (right_mem_Icc.2 ht)

/-- **Conservation of energy**, for the $H^1_0$ preimage. Let $u$ solve the wave equation with data
$(u_0, v_0)$, and let $t \ge 0$. Then
$$\|u'(t)\|^2 + \int_\Omega |\nabla \tilde u(t)|^2 = \|v_0\|^2 + \int_\Omega |\nabla u_0|^2.$$
This is (32) of [brezis2011functional], §10.3, and Remark 6 there.

The derivative $u'$ is taken within $[0, \infty)$, and the identity holds on every open set. The
integrals are `Elliptic.dirichletForm`, and the preimage is `toSobolevZero Ω (u t)`. -/
theorem energy_dirichletForm (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ‖derivWithin u (Ici 0) t‖ ^ 2
      + dirichletForm Ω (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω)
        (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω)
      = ‖v₀‖ ^ 2
        + dirichletForm Ω (u₀ : SobolevEuclidean N 1 2 Ω) (u₀ : SobolevEuclidean N 1 2 Ω) := by
  have e := h.energyFun_eq ht
  have e1 : energyFun Ω u t = ‖derivWithin u (Ici 0) t‖ ^ 2
      + dirichletForm Ω (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω)
        (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω) :=
    congrArg (fun z ↦ ‖derivWithin u (Ici 0) t‖ ^ 2 + z) (inner_dirichletOperator _ _ _)
  have e2 : energyFun Ω u 0 = ‖v₀‖ ^ 2
      + dirichletForm Ω (u₀ : SobolevEuclidean N 1 2 Ω) (u₀ : SobolevEuclidean N 1 2 Ω) := by
    unfold energyFun
    rw [h.derivWithin_zero, toSobolevZero_eq h.apply_zero.symm, inner_dirichletOperator]
  exact e1.symm.trans (e.trans e2)

/-- **Conservation of energy.** Let $u$ solve the wave equation with data $(u_0, v_0)$, and let
$t \ge 0$. Then
$$\|u'(t)\|^2 + \langle -\Delta u(t), u(t) \rangle = \|v_0\|^2 + \langle -\Delta u_0, u_0
  \rangle.$$
This is (32) of [brezis2011functional], §10.3.

The two inner products are $\int_\Omega |\nabla u(t)|^2$ and $\int_\Omega |\nabla u_0|^2$
(`dirichletLaplacian_inner_self_eq_dirichletForm`). The datum $u_0$ is read in $L^2(\Omega)$
through $\iota$; it lies in $D(-\Delta)$ by `Wave.IsSolution.memOperatorDomain_mk`. -/
theorem energy (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ‖derivWithin u (Ici 0) t‖ ^ 2 + ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, u t⟫_ℝ
      = ‖v₀‖ ^ 2 + ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀, h.memOperatorDomain_mk.1⟩,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          u₀⟫_ℝ := by
  have e1 : ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, u t⟫_ℝ
      = dirichletForm Ω (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω)
        (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω) :=
    dirichletLaplacian_inner_self_eq_dirichletForm ⟨u t, h.mem_domain t ht⟩
      (toSobolevZero Ω (u t)).2 (h.fnL_toSobolevZero_apply ht)
  have e2 : ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀, h.memOperatorDomain_mk.1⟩,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀⟫_ℝ
      = dirichletForm Ω (u₀ : SobolevEuclidean N 1 2 Ω) (u₀ : SobolevEuclidean N 1 2 Ω) :=
    dirichletLaplacian_inner_self_eq_dirichletForm ⟨_, h.memOperatorDomain_mk.1⟩ u₀.2 rfl
  exact (congrArg (fun z ↦ ‖derivWithin u (Ici 0) t‖ ^ 2 + z) e1).trans
    ((h.energy_dirichletForm ht).trans (congrArg (fun z ↦ ‖v₀‖ ^ 2 + z) e2).symm)

end IsSolution

/-! ### Remark 8: d'Alembert's formula -/

/-- **d'Alembert's formula**: for functions $u_0, v_0 : \mathbb{R} \to \mathbb{R}$,
$$u(x, t) = \frac12 \bigl( u_0(x + t) + u_0(x - t) \bigr) + \frac12 \int_{x - t}^{x + t} v_0(s)
  \, ds,$$
as the curve $t \mapsto u(\cdot, t)$ of functions of $x$. This is (40) of
[brezis2011functional], §10.3, Remark 8; for $v_0 = 0$ it is (41).

The integral is Mathlib's oriented interval integral, so the formula is defined for every
$t \in \mathbb{R}$. The integral term is $0$ when $v_0$ is not integrable on the interval
between $x - t$ and $x + t$. -/
def dAlembert (u₀ v₀ : ℝ → ℝ) (t : ℝ) : ℝ → ℝ := fun x ↦
  (1 / 2) * (u₀ (x + t) + u₀ (x - t)) + (1 / 2) * ∫ s in (x - t)..(x + t), v₀ s

/-- The value of d'Alembert's formula at $(x, t)$ is $\frac12 (u_0(x + t) + u_0(x - t)) + \frac12
\int_{x - t}^{x + t} v_0(s) \, ds$. -/
theorem dAlembert_apply (u₀ v₀ : ℝ → ℝ) (t x : ℝ) :
    dAlembert u₀ v₀ t x
      = (1 / 2) * (u₀ (x + t) + u₀ (x - t)) + (1 / 2) * ∫ s in (x - t)..(x + t), v₀ s :=
  rfl

/-- d'Alembert's formula with $v_0 = 0$ is $u(x, t) = \frac12 (u_0(x + t) + u_0(x - t))$. This is
(41) of [brezis2011functional], §10.3. -/
theorem dAlembert_zero_apply (u₀ : ℝ → ℝ) (t x : ℝ) :
    dAlembert u₀ 0 t x = (1 / 2) * (u₀ (x + t) + u₀ (x - t)) := by
  rw [dAlembert_apply]
  simp

/-- **Propagation of singularities.** Let $u_0 : \mathbb{R} \to \mathbb{R}$ be $C^n$ on
$\mathbb{R} \setminus \{x_0\}$, for an order $n$ that may be infinite. Then the function $(x, t)
\mapsto \frac12 (u_0(x + t) + u_0(x - t))$ of (41) is $C^n$ on the complement of the two
characteristics $x + t = x_0$ and $x - t = x_0$ through $(x_0, 0)$. So a singularity of the
datum propagates along the characteristics and nowhere else. This is Remark 8 of
[brezis2011functional], §10.3. -/
theorem dAlembert_contDiffOn_off_characteristics {u₀ : ℝ → ℝ} {x₀ : ℝ} {n : WithTop ℕ∞}
    (hu₀ : ContDiffOn ℝ n u₀ {x₀}ᶜ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ dAlembert u₀ 0 p.2 p.1)
      {p : ℝ × ℝ | p.1 + p.2 ≠ x₀ ∧ p.1 - p.2 ≠ x₀} := by
  have e : (fun p : ℝ × ℝ ↦ dAlembert u₀ 0 p.2 p.1)
      = fun p : ℝ × ℝ ↦ (1 / 2) * (u₀ (p.1 + p.2) + u₀ (p.1 - p.2)) :=
    funext fun p ↦ dAlembert_zero_apply u₀ p.2 p.1
  rw [e]
  refine contDiffOn_const.mul (ContDiffOn.add ?_ ?_)
  · exact hu₀.comp (contDiff_fst.add contDiff_snd).contDiffOn fun p hp ↦ hp.1
  · exact hu₀.comp (contDiff_fst.sub contDiff_snd).contDiffOn fun p hp ↦ hp.2

/-! ### Remark 7: the two-sided solution, by time reversal -/

variable {u₀ : SobolevEuclideanZero N 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u v : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- The class of solutions depends only on the values on $[0, \infty)$: if $u$ solves the wave
equation with data $(u_0, v_0)$ and $v = u$ on $[0, \infty)$, then $v$ solves the wave equation
with the same data. -/
theorem IsSolution.congr (h : IsSolution Ω u₀ v₀ u) (huv : EqOn u v (Ici 0)) :
    IsSolution Ω u₀ v₀ v where
  contDiffOn := h.contDiffOn.congr fun _ ht ↦ (huv ht).symm
  contDiffOnThrough := by
    obtain ⟨w, hw, hwu⟩ := h.contDiffOnThrough
    exact ⟨w, hw, fun t ht ↦ (huv ht).symm.trans (hwu t ht)⟩
  mem_domain t ht := huv ht ▸ h.mem_domain t ht
  contDiffOnPowDomain := h.contDiffOnPowDomain.congr huv
  eqn t ht := by
    rw [← iteratedDerivWithin_congr huv ht, h.eqn t ht]
    exact congrArg (fun z ↦ -(dirichletLaplacian Ω z)) (Subtype.ext (huv ht))
  apply_zero := (huv self_mem_Ici).symm.trans h.apply_zero
  derivWithin_zero := (derivWithin_congr huv (huv self_mem_Ici)).symm.trans h.derivWithin_zero

/-- If $v_0 \in H^1_0(\Omega)$, then $-v_0 \in H^1_0(\Omega)$. -/
theorem exists_fnL_eq_neg
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = -v₀ := by
  obtain ⟨w, hw⟩ := hv₀
  exact ⟨-w, (_root_.map_neg _ w).trans (congrArg Neg.neg hw)⟩

variable (Ω) in
/-- The **two-sided solution** with data $(u_0, v_0)$:
$$u(t) = \begin{cases} u^+(t), & t \ge 0, \\ u^-(-t), & t < 0, \end{cases}$$
where $u^+$ is the solution with data $(u_0, v_0)$ and $u^-$ is the solution with data
$(u_0, -v_0)$ (`Wave.solution`). This is the solution for all $t \in \mathbb{R}$ of Remark 7 of
[brezis2011functional], §10.3, obtained here by time reversal. -/
def twoSidedSolution (u₀ : SobolevEuclideanZero N 1 2 Ω)
    (v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  if 0 ≤ t then solution Ω u₀ v₀ t else solution Ω u₀ (-v₀) (-t)

/-- For $t \ge 0$ the two-sided solution is the solution with data $(u_0, v_0)$ at $t$. -/
theorem twoSidedSolution_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    twoSidedSolution Ω u₀ v₀ t = solution Ω u₀ v₀ t :=
  ite_eq_left ht

/-- If $\iota u_0 \in D(-\Delta)$, $v_0 \in H^1_0(\Omega)$ and $t \ge 0$, then the two-sided
solution at $-t$ is the solution with data $(u_0, -v_0)$ at $t$. -/
theorem twoSidedSolution_neg_of_nonneg
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀)
    {t : ℝ} (ht : 0 ≤ t) : twoSidedSolution Ω u₀ v₀ (-t) = solution Ω u₀ (-v₀) t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [neg_zero, twoSidedSolution_of_nonneg le_rfl, (isSolution_solution hu₀ hv₀).apply_zero,
      (isSolution_solution hu₀ (exists_fnL_eq_neg hv₀)).apply_zero]
  · rw [twoSidedSolution, ite_eq_right (by linarith), neg_neg]

/-- If $\iota u_0 \in D(-\Delta)$ and $v_0 \in H^1_0(\Omega)$, then the two-sided solution solves
the wave equation with data $(u_0, v_0)$. This is the forward half of Remark 7 of
[brezis2011functional], §10.3. -/
theorem isSolution_twoSidedSolution
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    IsSolution Ω u₀ v₀ (twoSidedSolution Ω u₀ v₀) :=
  (isSolution_solution hu₀ hv₀).congr fun _ ht ↦ (twoSidedSolution_of_nonneg ht).symm

/-- If $\iota u_0 \in D(-\Delta)$ and $v_0 \in H^1_0(\Omega)$, then the reflection $t \mapsto u(-t)$
of the two-sided solution solves the wave equation with data $(u_0, -v_0)$. Time reversal
preserves (27)–(29) and changes the sign of (30). This is the backward half of Remark 7 of
[brezis2011functional], §10.3. -/
theorem isSolution_twoSidedSolution_neg
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    IsSolution Ω u₀ (-v₀) fun t ↦ twoSidedSolution Ω u₀ v₀ (-t) :=
  (isSolution_solution hu₀ (exists_fnL_eq_neg hv₀)).congr fun _ ht ↦
    (twoSidedSolution_neg_of_nonneg hu₀ hv₀ ht).symm

/-- **The wave equation is solvable backward in time.** Let $\Omega \subseteq \mathbb{R}^N$ be open,
let $u_0 \in H^1_0(\Omega)$ with $\iota u_0 \in D(-\Delta)$, and let $v_0 \in H^1_0(\Omega)$.
Then there is exactly one curve $u : \mathbb{R} \to L^2(\Omega)$ such that $u$ solves the wave
equation with data $(u_0, v_0)$ and its reflection $t \mapsto u(-t)$ solves it with data
$(u_0, -v_0)$. This is the two-sided solvability of Remark 7 of [brezis2011functional], §10.3.

The proof uses time reversal and not the Dirichlet inner product of the source's argument, so
$\Omega$ need not be bounded. The energy at negative times is `Wave.IsSolution.energy_neg`. -/
theorem existsUnique_isSolution_backward
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    ∃! u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      IsSolution Ω u₀ v₀ u ∧ IsSolution Ω u₀ (-v₀) fun t ↦ u (-t) := by
  refine ⟨twoSidedSolution Ω u₀ v₀, ⟨isSolution_twoSidedSolution hu₀ hv₀,
    isSolution_twoSidedSolution_neg hu₀ hv₀⟩, fun v ⟨hv, hv'⟩ ↦ funext fun t ↦ ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · exact (hv.eqOn_solution ht).trans (twoSidedSolution_of_nonneg ht).symm
  · have h1 := hv'.eqOn_solution (Left.nonneg_neg_iff.2 ht.le)
    simp only [neg_neg] at h1
    rw [h1, twoSidedSolution, ite_eq_right (not_le.2 ht)]

/-- **Conservation of energy at negative times.** Let $u : \mathbb{R} \to L^2(\Omega)$ be a curve
whose reflection $w(t) = u(-t)$ solves the wave equation with data $(u_0, -v_0)$, and let
$t \le 0$. Then
$$\|w'(-t)\|^2 + \langle -\Delta u(t), u(t) \rangle = \|v_0\|^2 + \langle -\Delta u_0, u_0
  \rangle,$$
where $w'$ is the derivative within $[0, \infty)$. With `Wave.IsSolution.energy` for $t \ge 0$,
this is the conservation $|U(t)|_H = |U_0|_H$ for all $t \in \mathbb{R}$ in the energy norm, as
in Remark 7 of [brezis2011functional], §10.3.

The statement is `Wave.IsSolution.energy` for the reflected solution, with $\|-v_0\| = \|v_0\|$. -/
theorem IsSolution.energy_neg (h : IsSolution Ω u₀ (-v₀) fun t ↦ u (-t))
    {t : ℝ} (ht : t ≤ 0) :
    ‖derivWithin (fun t ↦ u (-t)) (Ici 0) (-t)‖ ^ 2
      + ⟪dirichletLaplacian Ω ⟨u t, neg_neg t ▸ h.mem_domain (-t) (neg_nonneg.2 ht)⟩, u t⟫_ℝ
      = ‖v₀‖ ^ 2 + ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀, h.memOperatorDomain_mk.1⟩,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          u₀⟫_ℝ := by
  have e := h.energy (neg_nonneg.2 ht)
  have hx : (⟨u (-(-t)), h.mem_domain (-t) (neg_nonneg.2 ht)⟩ : (dirichletLaplacian Ω).domain)
      = ⟨u t, neg_neg t ▸ h.mem_domain (-t) (neg_nonneg.2 ht)⟩ :=
    Subtype.ext (congrArg u (neg_neg t))
  have e2 : ⟪dirichletLaplacian Ω ⟨u (-(-t)), h.mem_domain (-t) (neg_nonneg.2 ht)⟩, u (-(-t))⟫_ℝ
      = ⟪dirichletLaplacian Ω ⟨u t, neg_neg t ▸ h.mem_domain (-t) (neg_nonneg.2 ht)⟩, u t⟫_ℝ :=
    congrArg (fun z : (dirichletLaplacian Ω).domain ↦ ⟪dirichletLaplacian Ω z,
      (z : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))⟫_ℝ) hx
  have e3 : ‖-v₀‖ ^ 2 = ‖v₀‖ ^ 2 := by rw [norm_neg]
  linarith

end Wave

/-! ### Remark 9: the eigenfunction expansion -/

section Eigen

open LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
  {u₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

namespace Wave.IsSolution

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be bounded and nonempty, let $(e_n)$ be the Dirichlet
eigenbasis of $L^2(\Omega)$, and let $u$ solve the wave equation. Then for every $n$ the
coefficient $a_n(t) = \langle u(t), e_n \rangle$ has the derivative $\langle u'(t), e_n \rangle$
within $[0, \infty)$ at every $t \ge 0$. -/
theorem hasDerivWithinAt_inner_eigenbasis (h : IsSolution Ω u₀ v₀ u) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      ⟪derivWithin u (Ici 0) t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ (Ici 0) t := by
  have h1 := (h.contDiffOn.differentiableOn two_ne_zero t ht).hasDerivWithinAt.inner ℝ
    (hasDerivWithinAt_const t (Ici 0) (dirichletEigenbasis Ω hΩ hne n))
  refine h1.congr_deriv ?_
  rw [inner_zero_right, zero_add]

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be bounded and nonempty, let $(e_n)$ be the Dirichlet
eigenbasis of $L^2(\Omega)$ with eigenvalues $\lambda_n$, and let $u$ solve the wave equation.
Then $t \mapsto \langle u'(t), e_n \rangle$ has the derivative
$-\lambda_n \langle u(t), e_n \rangle$ within $[0, \infty)$ at every $t \ge 0$, since $\langle
u'', e_n \rangle = -\langle -\Delta u, e_n \rangle = -\langle u, -\Delta e_n \rangle =
-\lambda_n \langle u, e_n \rangle$. -/
theorem hasDerivWithinAt_inner_derivWithin_eigenbasis (h : IsSolution Ω u₀ v₀ u) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ ⟪derivWithin u (Ici 0) t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      (-dirichletEigenvalue Ω hΩ n * ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) (Ici 0) t := by
  obtain ⟨hmem, hAe⟩ := dirichletLaplacian_apply_dirichletEigenbasis hΩ hne n
  have h1 := (h.hasDerivWithinAt_derivWithin ht).inner ℝ
    (hasDerivWithinAt_const t (Ici 0) (dirichletEigenbasis Ω hΩ hne n))
  refine h1.congr_deriv ?_
  rw [inner_zero_right, zero_add, inner_neg_left,
    dirichletLaplacian_isFormalAdjoint ⟨u t, h.mem_domain t ht⟩ ⟨_, hmem⟩, hAe, inner_smul_right,
    neg_mul]

/-- **The Fourier coefficients of the solution.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be bounded
and nonempty, let $(e_n)$ be the orthonormal basis of $L^2(\Omega)$ of Dirichlet eigenfunctions
with eigenvalues $\lambda_n > 0$, and let $u$ solve the wave equation with data $(u_0, v_0)$.
Then for every $n$ and every $t \ge 0$,
$$\langle u(t), e_n \rangle = \langle u_0, e_n \rangle \cos(\sqrt{\lambda_n} \, t) +
  \frac{\langle v_0, e_n \rangle}{\sqrt{\lambda_n}} \sin(\sqrt{\lambda_n} \, t).$$
This is Remark 9 of [brezis2011functional], §10.3.

The basis is `Elliptic.dirichletEigenbasis` and the eigenvalues are
`Elliptic.dirichletEigenvalue`. The datum $u_0$ is read in $L^2(\Omega)$ through $\iota$. The
coefficient $a_n(t) = \langle u(t), e_n \rangle$ solves the harmonic oscillator
$a_n'' = -\lambda_n a_n$ with $a_n(0) = \langle u_0, e_n \rangle$ and
$a_n'(0) = \langle v_0, e_n \rangle$ (`eq_cos_add_sin_of_hasDerivWithinAt_oscillator`). -/
theorem inner_eigenfunction (h : IsSolution Ω u₀ v₀ u) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ
      = ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ
          * Real.cos (√(dirichletEigenvalue Ω hΩ n) * t)
        + ⟪v₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ / √(dirichletEigenvalue Ω hΩ n)
          * Real.sin (√(dirichletEigenvalue Ω hΩ n) * t) := by
  have h1 : ∀ s, 0 ≤ s → HasDerivWithinAt (fun t ↦ ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      ((fun t ↦ ⟪derivWithin u (Ici 0) t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) s) (Ici 0) s :=
    fun s hs ↦ h.hasDerivWithinAt_inner_eigenbasis hΩ hne n hs
  have h2 : ∀ s, 0 ≤ s → HasDerivWithinAt
      (fun t ↦ ⟪derivWithin u (Ici 0) t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      (-dirichletEigenvalue Ω hΩ n * (fun t ↦ ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) s)
      (Ici 0) s :=
    fun s hs ↦ h.hasDerivWithinAt_inner_derivWithin_eigenbasis hΩ hne n hs
  have h3 := eq_cos_add_sin_of_hasDerivWithinAt_oscillator (dirichletEigenvalue_pos Ω hΩ hne n)
    h1 h2 ht
  simp only [h.apply_zero, h.derivWithin_zero] at h3
  exact h3

/-- **The eigenfunction expansion of the solution.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
bounded and nonempty, let $(e_n)$ be the orthonormal basis of $L^2(\Omega)$ of Dirichlet
eigenfunctions with eigenvalues $\lambda_n > 0$, and let $u$ solve the wave equation with data
$(u_0, v_0)$. Then for every $t \ge 0$,
$$u(t) = \sum_{n} \Bigl( \langle u_0, e_n \rangle \cos(\sqrt{\lambda_n} \, t) + \frac{\langle
  v_0, e_n \rangle}{\sqrt{\lambda_n}} \sin(\sqrt{\lambda_n} \, t) \Bigr) e_n,$$
with the series converging unconditionally in $L^2(\Omega)$. This is Remark 9 of
[brezis2011functional], §10.3.

The datum $u_0$ is read in $L^2(\Omega)$ through $\iota$. The coefficients are
`Wave.IsSolution.inner_eigenfunction`. -/
theorem hasSum_eigenfunction (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n ↦ (⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        1 2 Ω volume u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ
          * Real.cos (√(dirichletEigenvalue Ω hΩ n) * t)
        + ⟪v₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ / √(dirichletEigenvalue Ω hΩ n)
          * Real.sin (√(dirichletEigenvalue Ω hΩ n) * t)) • dirichletEigenbasis Ω hΩ hne n)
      (u t) := by
  have := (dirichletEigenbasis Ω hΩ hne).hasSum_repr (u t)
  refine this.congr_fun fun n ↦ ?_
  have e1 : (dirichletEigenbasis Ω hΩ hne).repr (u t) n
      = ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ :=
    (HilbertBasis.repr_apply_apply _ _ _).trans (real_inner_comm _ _)
  exact congrArg (fun c : ℝ ↦ c • dirichletEigenbasis Ω hΩ hne n)
    ((h.inner_eigenfunction hΩ hne n ht).symm.trans e1.symm)

end Wave.IsSolution

end Eigen

/-! ### Remark 7: the phase space with the Dirichlet inner product -/

namespace Wave

open LinearPMap.PowDomain SobolevMultiIndex Elliptic

section DirichletPhaseSpace

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))}

variable (Ω hΩ) in
/-- For bounded $\Omega \subseteq \mathbb{R}^{d+1}$, the space $H^1_0(\Omega)$ with the **Dirichlet
inner product** $\langle u, v \rangle = \int_\Omega \nabla u \cdot \nabla v$. It is the energy
space of the operator `Elliptic.dirichletOperator` of the Dirichlet form. By Poincaré's
inequality this inner product is equivalent to the $H^1$ inner product ([brezis2011functional],
§10.3, Remark 7, and chapter 9, Remark 28). -/
abbrev dirichletEnergySpace : Type :=
  WithEnergy (dirichletOperator Ω).toLinearMap (dirichletOperator_isSymmetricCoercive Ω hΩ)

instance : CompleteSpace (dirichletEnergySpace Ω hΩ) :=
  WithEnergy.instCompleteSpace_of_continuousLinearMap _

variable (Ω hΩ) in
/-- For bounded $\Omega \subseteq \mathbb{R}^{d+1}$, the **phase space of Remark 7**:
$H^1_0(\Omega) \times L^2(\Omega)$ with the inner product
$$\langle (u_1, v_1), (u_2, v_2) \rangle = \int_\Omega \nabla u_1 \cdot \nabla u_2 + \int_\Omega
  v_1 v_2.$$
This is the phase space of Remark 7 of [brezis2011functional], §10.3.

The type is the $\ell^2$-product `WithLp 2` of `Wave.dirichletEnergySpace` and $L^2(\Omega)$, as
a type synonym that carries its `NormedAddCommGroup`, `InnerProductSpace` and `CompleteSpace`
structures, as `Wave.phaseSpace` does. -/
def dirichletPhaseSpace : Type :=
  WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))

instance : NormedAddCommGroup (dirichletPhaseSpace Ω hΩ) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))))

instance : InnerProductSpace ℝ (dirichletPhaseSpace Ω hΩ) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))))

instance : CompleteSpace (dirichletPhaseSpace Ω hΩ) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))))

namespace dirichletPhaseSpace

variable (Ω hΩ) in
/-- The point $(u, v)$ of the phase space of Remark 7, for $u \in H^1_0(\Omega)$ and
$v \in L^2(\Omega)$. -/
def mk (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    dirichletPhaseSpace Ω hΩ :=
  WithLp.toLp 2 (WithEnergy.equiv _ _ u, v)

/-- The first component $u \in H^1_0(\Omega)$ of a point $(u, v)$ of the phase space of Remark 7. -/
def fst (U : dirichletPhaseSpace Ω hΩ) : SobolevEuclideanZero (d + 1) 1 2 Ω :=
  (WithEnergy.equiv (dirichletOperator Ω).toLinearMap
    (dirichletOperator_isSymmetricCoercive Ω hΩ)).symm (WithLp.ofLp (U : WithLp 2
      (dirichletEnergySpace Ω hΩ
        × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))))).1

/-- The second component $v \in L^2(\Omega)$ of a point $(u, v)$ of the phase space of Remark 7. -/
def snd (U : dirichletPhaseSpace Ω hΩ) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (WithLp.ofLp (U : WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))))).2

/-- The first component of $(u, v)$ is $u$. -/
@[simp]
theorem mk_fst (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (mk Ω hΩ u v).fst = u :=
  rfl

/-- The second component of $(u, v)$ is $v$. -/
@[simp]
theorem mk_snd (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (mk Ω hΩ u v).snd = v :=
  rfl

/-- Two points of the phase space of Remark 7 with the same components are equal. -/
theorem ext {U V : dirichletPhaseSpace Ω hΩ} (h1 : U.fst = V.fst) (h2 : U.snd = V.snd) : U = V :=
  WithLp.ofLp_injective 2 (Prod.ext ((WithEnergy.equiv _ _).symm.injective h1) h2)

/-- The inner product of Remark 7: for $U = (u_1, v_1)$ and $V = (u_2, v_2)$, $\langle U, V
\rangle = \int_\Omega \nabla u_1 \cdot \nabla u_2 + \langle v_1, v_2 \rangle_{L^2}$. -/
theorem inner_def (U V : dirichletPhaseSpace Ω hΩ) :
    ⟪U, V⟫_ℝ = dirichletForm Ω (U.fst : SobolevEuclidean (d + 1) 1 2 Ω)
      (V.fst : SobolevEuclidean (d + 1) 1 2 Ω) + ⟪U.snd, V.snd⟫_ℝ :=
  congrArg (· + ⟪U.snd, V.snd⟫_ℝ) (inner_dirichletOperator Ω U.fst V.fst)

/-- The norm of Remark 7: $\|(u, v)\|^2 = \int_\Omega |\nabla u|^2 + \|v\|_{L^2}^2$. -/
theorem norm_sq_eq (U : dirichletPhaseSpace Ω hΩ) :
    ‖U‖ ^ 2 = dirichletForm Ω (U.fst : SobolevEuclidean (d + 1) 1 2 Ω)
      (U.fst : SobolevEuclidean (d + 1) 1 2 Ω) + ‖U.snd‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_def, real_inner_self_eq_norm_sq]

/-- The first component of $U + V$ is the sum of the first components. -/
@[simp]
theorem add_fst (U V : dirichletPhaseSpace Ω hΩ) : (U + V).fst = U.fst + V.fst :=
  rfl

/-- The second component of $U + V$ is the sum of the second components. -/
@[simp]
theorem add_snd (U V : dirichletPhaseSpace Ω hΩ) : (U + V).snd = U.snd + V.snd :=
  rfl

/-- The first component of $cU$ is $c$ times the first component of $U$. -/
@[simp]
theorem smul_fst (c : ℝ) (U : dirichletPhaseSpace Ω hΩ) : (c • U).fst = c • U.fst :=
  rfl

/-- The second component of $cU$ is $c$ times the second component of $U$. -/
@[simp]
theorem smul_snd (c : ℝ) (U : dirichletPhaseSpace Ω hΩ) : (c • U).snd = c • U.snd :=
  rfl

/-- The first component of $0$ is $0$. -/
@[simp]
theorem zero_fst : (0 : dirichletPhaseSpace Ω hΩ).fst = 0 :=
  rfl

/-- The second component of $0$ is $0$. -/
@[simp]
theorem zero_snd : (0 : dirichletPhaseSpace Ω hΩ).snd = 0 :=
  rfl

/-- The first component of $-U$ is the negative of the first component of $U$. -/
@[simp]
theorem neg_fst (U : dirichletPhaseSpace Ω hΩ) : (-U).fst = -U.fst :=
  rfl

/-- The second component of $-U$ is the negative of the second component of $U$. -/
@[simp]
theorem neg_snd (U : dirichletPhaseSpace Ω hΩ) : (-U).snd = -U.snd :=
  rfl

/-- In the phase space of Remark 7, $(u + u', v + v') = (u, v) + (u', v')$. -/
theorem mk_add (u u' : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v v' : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    mk Ω hΩ (u + u') (v + v') = mk Ω hΩ u v + mk Ω hΩ u' v' :=
  rfl

/-- In the phase space of Remark 7, $(cu, cv) = c (u, v)$. -/
theorem mk_smul (c : ℝ) (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    mk Ω hΩ (c • u) (c • v) = c • mk Ω hΩ u v :=
  rfl

/-- The norm of Remark 7 is at most the norm (34): $\|(u, v)\|^2 \le \|(u, v)\|_{H}^2$, where $H$ is
`Wave.phaseSpace`, because the Dirichlet form is bounded by the $H^1$ norm. -/
theorem norm_sq_le (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ‖mk Ω hΩ u v‖ ^ 2 ≤ ‖phaseSpace.mk Ω u v‖ ^ 2 := by
  rw [norm_sq_eq, phaseSpace.norm_sq_eq, mk_fst, mk_snd, phaseSpace.mk_fst, phaseSpace.mk_snd]
  have h1 := dirichletForm_self_le Ω (u : SobolevEuclidean (d + 1) 1 2 Ω)
  have h2 : ‖(u : SobolevEuclidean (d + 1) 1 2 Ω)‖ ^ 2 = ‖u‖ ^ 2 := rfl
  linarith

/-- The norm (34) is bounded by the norm of Remark 7: there is $c > 0$ with
$c \|(u, v)\|_{H}^2 \le \|(u, v)\|^2$ for all $u \in H^1_0(\Omega)$ and $v \in L^2(\Omega)$,
where $H$ is `Wave.phaseSpace`. This is Poincaré's inequality
(`Elliptic.dirichletForm_restrict_isCoercive`). -/
theorem exists_norm_sq_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
      (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))),
      c * ‖phaseSpace.mk Ω u v‖ ^ 2 ≤ ‖mk Ω hΩ u v‖ ^ 2 := by
  obtain ⟨c, hc, hcoer⟩ := dirichletForm_restrict_isCoercive Ω hΩ
  refine ⟨min c 1, lt_min hc one_pos, fun u v ↦ ?_⟩
  rw [norm_sq_eq, phaseSpace.norm_sq_eq, mk_fst, mk_snd, phaseSpace.mk_fst, phaseSpace.mk_snd]
  have h1 : c * ‖u‖ ^ 2 ≤ dirichletForm Ω (u : SobolevEuclidean (d + 1) 1 2 Ω)
      (u : SobolevEuclidean (d + 1) 1 2 Ω) := hcoer u
  have h2 := min_le_left c 1
  have h3 := min_le_right c 1
  nlinarith

end dirichletPhaseSpace

end DirichletPhaseSpace

/-! ### Remark 7: the wave operator on the Dirichlet phase space -/

section DirichletOperator

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))}

variable (Ω hΩ) in
/-- The domain condition of `Wave.operator'`: a point $(u, v)$ of the phase space of Remark 7
satisfies it if $\iota u \in D(-\Delta)$ and $v \in H^1_0(\Omega)$. It is
`Wave.MemOperatorDomain` read in the phase space of Remark 7. -/
def MemOperatorDomain' (U : dirichletPhaseSpace Ω hΩ) : Prop :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume U.fst
    ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero (d + 1) 1 2 Ω,
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume w
      = U.snd

/-- A point satisfies `Wave.MemOperatorDomain'` if and only if the same pair satisfies
`Wave.MemOperatorDomain` in `Wave.phaseSpace`. -/
theorem memOperatorDomain'_iff {U : dirichletPhaseSpace Ω hΩ} :
    MemOperatorDomain' Ω hΩ U ↔ MemOperatorDomain Ω (phaseSpace.mk Ω U.fst U.snd) :=
  Iff.rfl

/-- The point $0$ satisfies the domain condition of `Wave.operator'`. -/
theorem memOperatorDomain'_zero : MemOperatorDomain' Ω hΩ (0 : dirichletPhaseSpace Ω hΩ) :=
  memOperatorDomain_zero

/-- The domain condition of `Wave.operator'` is closed under addition. -/
theorem MemOperatorDomain'.add {U V : dirichletPhaseSpace Ω hΩ} (hU : MemOperatorDomain' Ω hΩ U)
    (hV : MemOperatorDomain' Ω hΩ V) : MemOperatorDomain' Ω hΩ (U + V) :=
  MemOperatorDomain.add (Ω := Ω) (U := phaseSpace.mk Ω U.fst U.snd)
    (V := phaseSpace.mk Ω V.fst V.snd) hU hV

/-- The domain condition of `Wave.operator'` is closed under scalar multiplication. -/
theorem MemOperatorDomain'.smul (c : ℝ) {U : dirichletPhaseSpace Ω hΩ}
    (hU : MemOperatorDomain' Ω hΩ U) : MemOperatorDomain' Ω hΩ (c • U) :=
  MemOperatorDomain.smul (Ω := Ω) c (U := phaseSpace.mk Ω U.fst U.snd) hU

variable (Ω hΩ) in
/-- The domain $D(A) = D(-\Delta) \times H^1_0(\Omega)$ in the phase space of Remark 7, as a
submodule. -/
def operatorDomain' : Submodule ℝ (dirichletPhaseSpace Ω hΩ) where
  carrier := {U | MemOperatorDomain' Ω hΩ U}
  zero_mem' := memOperatorDomain'_zero
  add_mem' := fun hU hV ↦ hU.add hV
  smul_mem' := fun c _ hU ↦ hU.smul c

variable (Ω hΩ) in
/-- The formula of the wave operator in the phase space of Remark 7:
$(u, v) \mapsto (-\tilde v, -\Delta u)$, on the whole space. -/
def operatorApply' (U : dirichletPhaseSpace Ω hΩ) : dirichletPhaseSpace Ω hΩ :=
  dirichletPhaseSpace.mk Ω hΩ (-toSobolevZero Ω U.snd) (dirichletLaplacianApply Ω
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      U.fst))

/-- For $U, V$ in the domain, the first component of `Wave.operatorApply'` is additive. -/
theorem operatorApply'_add_fst {U V : dirichletPhaseSpace Ω hΩ} (hU : MemOperatorDomain' Ω hΩ U)
    (hV : MemOperatorDomain' Ω hΩ V) :
    (operatorApply' Ω hΩ (U + V)).fst = (operatorApply' Ω hΩ U + operatorApply' Ω hΩ V).fst := by
  change -toSobolevZero Ω (U.snd + V.snd) = -toSobolevZero Ω U.snd + -toSobolevZero Ω V.snd
  rw [toSobolevZero_add hU.2 hV.2, neg_add]

/-- For $U, V$ in the domain, the second component of `Wave.operatorApply'` is additive. -/
theorem operatorApply'_add_snd {U V : dirichletPhaseSpace Ω hΩ} (hU : MemOperatorDomain' Ω hΩ U)
    (hV : MemOperatorDomain' Ω hΩ V) :
    (operatorApply' Ω hΩ (U + V)).snd = (operatorApply' Ω hΩ U + operatorApply' Ω hΩ V).snd := by
  change dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (U.fst + V.fst)) = _ + _
  rw [_root_.map_add]
  exact dirichletLaplacianApply_add hU.1 hV.1

/-- For $U$ in the domain and $c \in \mathbb{R}$, the first component of `Wave.operatorApply'` at
$cU$ is $c$ times its value at $U$. -/
theorem operatorApply'_smul_fst (c : ℝ) {U : dirichletPhaseSpace Ω hΩ}
    (hU : MemOperatorDomain' Ω hΩ U) :
    (operatorApply' Ω hΩ (c • U)).fst = (c • operatorApply' Ω hΩ U).fst := by
  change -toSobolevZero Ω (c • U.snd) = c • -toSobolevZero Ω U.snd
  rw [toSobolevZero_smul c hU.2, smul_neg]

/-- For $U$ in the domain and $c \in \mathbb{R}$, the second component of `Wave.operatorApply'` at
$cU$ is $c$ times its value at $U$. -/
theorem operatorApply'_smul_snd (c : ℝ) {U : dirichletPhaseSpace Ω hΩ}
    (hU : MemOperatorDomain' Ω hΩ U) :
    (operatorApply' Ω hΩ (c • U)).snd = (c • operatorApply' Ω hΩ U).snd := by
  change dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (c • U.fst)) = c • _
  rw [_root_.map_smul]
  exact dirichletLaplacianApply_smul c hU.1

variable (Ω hΩ) in
/-- For bounded $\Omega \subseteq \mathbb{R}^{d+1}$, the **wave operator of Remark 7**:
$A(u, v) = (-v, -\Delta u)$ on the phase space with the Dirichlet inner product
(`Wave.dirichletPhaseSpace`), with domain $D(-\Delta) \times H^1_0(\Omega)$. It is the same map
as `Wave.operator` on the same domain; only the inner product of the phase space differs. This
is the operator of Remark 7 of [brezis2011functional], §10.3. -/
def operator' : dirichletPhaseSpace Ω hΩ →ₗ.[ℝ] dirichletPhaseSpace Ω hΩ where
  domain := operatorDomain' Ω hΩ
  toFun :=
    { toFun := fun U ↦ operatorApply' Ω hΩ U
      map_add' := fun U V ↦ dirichletPhaseSpace.ext (operatorApply'_add_fst U.2 V.2)
        (operatorApply'_add_snd U.2 V.2)
      map_smul' := fun c U ↦ dirichletPhaseSpace.ext (operatorApply'_smul_fst c U.2)
        (operatorApply'_smul_snd c U.2) }

/-- A point $(u, v)$ lies in the domain of `Wave.operator'` if and only if $\iota u \in D(-\Delta)$
and $v \in H^1_0(\Omega)$. -/
theorem mem_operator'_domain_iff {U : dirichletPhaseSpace Ω hΩ} :
    U ∈ (operator' Ω hΩ).domain ↔ MemOperatorDomain' Ω hΩ U :=
  Iff.rfl

/-- The first component of $A(u, v)$ in the phase space of Remark 7 is $-\tilde v$. -/
theorem operator'_apply_fst (U : (operator' Ω hΩ).domain) :
    (operator' Ω hΩ U).fst = -toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd :=
  rfl

/-- The second component of $A(u, v)$ in the phase space of Remark 7 is $-\Delta u$. -/
theorem operator'_apply_snd (U : (operator' Ω hΩ).domain) :
    (operator' Ω hΩ U).snd = dirichletLaplacian Ω
      ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (U : dirichletPhaseSpace Ω hΩ).fst, (mem_operator'_domain_iff.1 U.2).1⟩ :=
  rfl

/-- For the inner product of Remark 7, $\langle AU, U \rangle = 0$ for every $U \in D(A)$. Indeed
$-\int_\Omega \nabla \tilde v \cdot \nabla u + \langle -\Delta u, v \rangle = 0$ by
`dirichletLaplacian_inner_eq_dirichletForm`. This is Remark 7 of [brezis2011functional], §10.3. -/
theorem operator'_inner_self_eq_zero (U : (operator' Ω hΩ).domain) :
    ⟪operator' Ω hΩ U, (U : dirichletPhaseSpace Ω hΩ)⟫_ℝ = 0 := by
  have hmem := mem_operator'_domain_iff.1 U.2
  have hwv : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd)
      = (U : dirichletPhaseSpace Ω hΩ).snd :=
    fnL_toSobolevZero hmem.2
  have h0 := dirichletPhaseSpace.inner_def (operator' Ω hΩ U) (U : dirichletPhaseSpace Ω hΩ)
  have h1 : dirichletForm Ω ((operator' Ω hΩ U).fst : SobolevEuclidean (d + 1) 1 2 Ω)
      ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω)
      = -dirichletForm Ω (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd :
          SobolevEuclidean (d + 1) 1 2 Ω)
        ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω) :=
    (congrArg (fun z ↦ dirichletForm Ω z
      ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω))
      (Submodule.coe_neg _ (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd))).trans
      ((congrArg (fun L : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ ↦
        L ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω))
        (_root_.map_neg (dirichletForm Ω)
          (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd :
            SobolevEuclidean (d + 1) 1 2 Ω))).trans
        (neg_apply _ _))
  have h2 : ⟪(operator' Ω hΩ U).snd, (U : dirichletPhaseSpace Ω hΩ).snd⟫_ℝ
      = dirichletForm Ω ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω)
        (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd : SobolevEuclidean (d + 1) 1 2 Ω) :=
    (congrArg (fun z ↦ ⟪(operator' Ω hΩ U).snd, z⟫_ℝ) hwv).symm.trans
      (dirichletLaplacian_inner_eq_dirichletForm ⟨_, hmem.1⟩
        (U : dirichletPhaseSpace Ω hΩ).fst.2 rfl
        (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd).2)
  have h3 := (dirichletForm_isHermitian Ω
    (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd : SobolevEuclidean (d + 1) 1 2 Ω)
    ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω)).trans (conj_trivial _)
  linarith

/-- For the inner product of Remark 7, $A$ is monotone, since $\langle AU, U \rangle = 0$. This is
part (i) of Remark 7 of [brezis2011functional], §10.3. -/
theorem operator'_isMonotone : (operator' Ω hΩ).IsMonotone := fun U ↦ by
  change (0 : ℝ) ≤ ⟪operator' Ω hΩ U, (U : dirichletPhaseSpace Ω hΩ)⟫_ℝ
  rw [operator'_inner_self_eq_zero]

/-- For the inner product of Remark 7, $-A$ is monotone. This is part (i) of Remark 7 of
[brezis2011functional], §10.3. -/
theorem neg_operator'_isMonotone : (-operator' Ω hΩ).IsMonotone := fun U ↦ by
  change (0 : ℝ) ≤ ⟪(-operator' Ω hΩ) U, (U : dirichletPhaseSpace Ω hΩ)⟫_ℝ
  rw [LinearPMap.neg_apply, inner_neg_left, operator'_inner_self_eq_zero, neg_zero]

/-- In an additive group, $x + a = g + f$ implies $(x - f) + a = g$. -/
private theorem sub_add_eq_of_add_eq {E : Type*} [AddCommGroup E] {x f g a : E}
    (h : x + a = g + f) : x - f + a = g := by
  rw [sub_add_eq_add_sub, h, add_sub_cancel_right]

/-- In an additive group, $x + a = f - g$ implies $(f - x) - a = g$. -/
private theorem sub_sub_eq_of_add_eq {E : Type*} [AddCommGroup E] {x f g a : E}
    (h : x + a = f - g) : f - x - a = g := by
  rw [sub_sub, h, sub_sub_cancel]

/-- For the inner product of Remark 7, $R(I + A)$ is the whole phase space: for every $F$ there is
$U \in D(A)$ with $U + AU = F$. This is part (ii) of Remark 7 of [brezis2011functional], §10.3.

For $F = (f, g)$ the proof solves $-\Delta u + u = g + f$ in $D(-\Delta)$
(`dirichletLaplacian_exists_add_apply_eq`) and takes $v = u - f$. -/
theorem operator'_exists_add_apply_eq (F : dirichletPhaseSpace Ω hΩ) :
    ∃ U : (operator' Ω hΩ).domain,
      (U : dirichletPhaseSpace Ω hΩ) + operator' Ω hΩ U = F := by
  obtain ⟨x, hx⟩ := dirichletLaplacian_exists_add_apply_eq (Ω := Ω) (F.snd
    + SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      F.fst)
  obtain ⟨u, hux⟩ := dirichletLaplacian_exists_sobolevZero_lift x
  have hmem : MemOperatorDomain' Ω hΩ (dirichletPhaseSpace.mk Ω hΩ u
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (u - F.fst))) := by
    refine ⟨?_, ⟨_, rfl⟩⟩
    change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume u ∈ dirichletLaplacianDomain Ω
    rw [hux]
    exact x.2
  refine ⟨⟨_, hmem⟩, dirichletPhaseSpace.ext ?_ ?_⟩
  · change u + -toSobolevZero Ω (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume (u - F.fst)) = F.fst
    exact (congrArg (fun z ↦ u + -z) (toSobolevZero_fnL (u - F.fst))).trans
      (by abel)
  · change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume (u - F.fst) + dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u) = F.snd
    have h1 : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume (u - F.fst)
        = (x : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
          - SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume F.fst :=
      (_root_.map_sub (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        1 2 Ω volume) u F.fst).trans (congrArg (fun z ↦ z - SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume F.fst) hux)
    refine (congrArg₂ (fun a b ↦ a + dirichletLaplacianApply Ω b) h1 hux).trans ?_
    exact sub_add_eq_of_add_eq hx

/-- For the inner product of Remark 7, $R(I - A)$ is the whole phase space: for every $F$ there is
$U \in D(A)$ with $U - AU = F$. This is part (ii) of Remark 7 of [brezis2011functional], §10.3.

For $F = (f, g)$ the proof solves $-\Delta u + u = f - g$ in $D(-\Delta)$ and takes $v = f - u$. -/
theorem neg_operator'_exists_add_apply_eq (F : dirichletPhaseSpace Ω hΩ) :
    ∃ U : (-operator' Ω hΩ).domain,
      (U : dirichletPhaseSpace Ω hΩ) + (-operator' Ω hΩ) U = F := by
  obtain ⟨x, hx⟩ := dirichletLaplacian_exists_add_apply_eq (Ω := Ω)
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      F.fst - F.snd)
  obtain ⟨u, hux⟩ := dirichletLaplacian_exists_sobolevZero_lift x
  have hmem : MemOperatorDomain' Ω hΩ (dirichletPhaseSpace.mk Ω hΩ u
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (F.fst - u))) := by
    refine ⟨?_, ⟨_, rfl⟩⟩
    change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume u ∈ dirichletLaplacianDomain Ω
    rw [hux]
    exact x.2
  refine ⟨⟨_, hmem⟩, dirichletPhaseSpace.ext ?_ ?_⟩
  · change u + -(-toSobolevZero Ω (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume (F.fst - u))) = F.fst
    exact (congrArg (fun z ↦ u + -(-z)) (toSobolevZero_fnL (F.fst - u))).trans
      ((congrArg (fun z ↦ u + z) (neg_neg (F.fst - u))).trans (add_sub_cancel u F.fst))
  · change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume (F.fst - u) + -dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u) = F.snd
    have h1 : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume (F.fst - u) = SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume F.fst
          - (x : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :=
      (_root_.map_sub (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        1 2 Ω volume) F.fst u).trans (congrArg (fun z ↦ SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume F.fst - z) hux)
    refine (congrArg₂ (fun a b ↦ a + -dirichletLaplacianApply Ω b) h1 hux).trans ?_
    rw [← sub_eq_add_neg]
    exact sub_sub_eq_of_add_eq hx

/-- For bounded $\Omega \subseteq \mathbb{R}^{d+1}$, the wave operator $A$ is maximal monotone on
the phase space with the Dirichlet inner product. This is parts (i) and (ii) of Remark 7 of
[brezis2011functional], §10.3.

Monotonicity is $\langle AU, U \rangle = 0$ (`Wave.operator'_inner_self_eq_zero`), and the range
condition is `Wave.operator'_exists_add_apply_eq`. -/
theorem operator'_isMaximalMonotone : (operator' Ω hΩ).IsMaximalMonotone :=
  ⟨operator'_isMonotone, operator'_exists_add_apply_eq⟩

/-- For bounded $\Omega \subseteq \mathbb{R}^{d+1}$, the operator $-A$ is maximal monotone on the
phase space with the Dirichlet inner product, so the wave equation is solvable backward in time.
This is parts (i) and (ii) of Remark 7 of [brezis2011functional], §10.3. -/
theorem neg_operator'_isMaximalMonotone : (-operator' Ω hΩ).IsMaximalMonotone :=
  ⟨neg_operator'_isMonotone, neg_operator'_exists_add_apply_eq⟩

end DirichletOperator

end Wave

namespace Wave

/-! ### Remark 10: the compatibility conditions are necessary -/

section Classical

open Heat Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Set E} {T : ℝ} {u : E × ℝ → ℝ}

/-- A **classical solution of the wave equation** on the open cylinder $\Omega \times (0, T)$: a
function $u : E \times \mathbb{R} \to \mathbb{R}$ of space and time with
$$\partial_{tt} u = \Delta_x u \quad \text{at every point of } \Omega \times (0, T).$$
Here $E$ is a finite-dimensional real inner product space and $\Omega \subseteq E$.

No regularity, boundary condition or initial condition is part of the structure. Remark 10 of
[brezis2011functional], chapter 10, assumes in addition that $u$ is smooth on
$E \times \mathbb{R}$. The derivatives $\partial_t$ and $\Delta_x$ are `Heat.timeDeriv` and
`Heat.spaceLaplacian` of `Numlib.Analysis.Calculus.SpaceTime`. -/
structure IsClassicalSolution (Ω : Set E) (T : ℝ) (u : E × ℝ → ℝ) : Prop where
  /-- The wave equation $\partial_{tt} u = \Delta_x u$ holds at every point of
  $\Omega \times (0, T)$. -/
  eqn : EqOn (timeDeriv (timeDeriv u)) (spaceLaplacian u) (Ω ×ˢ Ioo 0 T)

/-- **The iterated wave equation.** Let $\Omega \subseteq E$ be open, and let $u$ be a classical
solution of $\partial_{tt} u = \Delta_x u$ on $\Omega \times (0, T)$ that is $C^\infty$ on
$E \times \mathbb{R}$. Then for every $j \in \mathbb{N}$,
$$\partial_t^{2j} u = \Delta_x^j u \quad \text{and} \quad \partial_t^{2j+1} u = \Delta_x^j
  \partial_t u \quad \text{on } \Omega \times (0, T).$$

The proof is by induction on $j$, with the commutation
$\partial_t \Delta_x^j = \Delta_x^j \partial_t$ for smooth functions
(`Heat.timeDeriv_spaceLaplacian_iterate`) and the locality of both operators on the open
cylinder. -/
theorem IsClassicalSolution.timeDeriv_iterate_eqOn (hΩ : IsOpen Ω)
    (hu : IsClassicalSolution Ω T u) (hsmooth : ContDiff ℝ ∞ u) (j : ℕ) :
    EqOn (timeDeriv^[2 * j] u) (spaceLaplacian^[j] u) (Ω ×ˢ Ioo 0 T) ∧
      EqOn (timeDeriv^[2 * j + 1] u) (spaceLaplacian^[j] (timeDeriv u)) (Ω ×ˢ Ioo 0 T) := by
  have hV : IsOpen (Ω ×ˢ Ioo 0 T) := hΩ.prod isOpen_Ioo
  induction j with
  | zero => exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | succ j ih =>
    obtain ⟨h0, h1⟩ := ih
    have h2 : EqOn (timeDeriv^[2 * (j + 1)] u) (spaceLaplacian^[j + 1] u) (Ω ×ˢ Ioo 0 T) := by
      intro p hp
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Function.iterate_succ_apply',
        timeDeriv_eqOn hV h1 hp, timeDeriv_spaceLaplacian_iterate (contDiff_timeDeriv hsmooth) j,
        spaceLaplacian_iterate_eqOn hV hu.eqn j hp, Function.iterate_succ_apply]
    refine ⟨h2, fun p hp ↦ ?_⟩
    rw [Function.iterate_succ_apply', timeDeriv_eqOn hV h2 hp,
      timeDeriv_spaceLaplacian_iterate hsmooth (j + 1)]

/-- **The compatibility conditions are necessary.** Let $\Omega \subseteq E$ be open and $T > 0$.
Let $u$ be a classical solution of the wave equation $\partial_{tt} u = \Delta u$ on
$\Omega \times (0, T)$ that is $C^\infty$ on $E \times \mathbb{R}$ and vanishes on
$\partial\Omega \times (0, T)$. Then the data $u_0 = u(\cdot, 0)$ and
$v_0 = \partial_t u(\cdot, 0)$ satisfy
$$\Delta^j u_0 = 0 \quad \text{and} \quad \Delta^j v_0 = 0 \quad \text{on } \partial\Omega$$
for every $j \in \mathbb{N}$. This is Remark 10 of [brezis2011functional], chapter 10, for the
compatibility conditions of Theorem 10.8.

The source states the remark for $u \in C^\infty(\bar\Omega \times [0, \infty))$ in the sense of
chapter 9, footnote 16, where $\Delta^j u_0$ on the boundary refers to continuous extensions.
The smoothness of $u$ on all of $E \times \mathbb{R}$ assumed here makes the statement
meaningful as written. The boundary $\partial\Omega$ is `frontier Ω`. The proof is that of
Remark 4 for the heat equation (`Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`):
by `Wave.IsClassicalSolution.timeDeriv_iterate_eqOn`, the time derivatives of $u$, which vanish
on $\partial\Omega \times (0, T)$, give $\Delta^j u_0$ and $\Delta^j v_0$ at $t = 0$ by
continuity (`Heat.spaceLaplacian_iterate_slice`). -/
theorem IsClassicalSolution.iteratedLaplacian_eq_zero_frontier (hΩ : IsOpen Ω) (hT : 0 < T)
    (hu : IsClassicalSolution Ω T u) (hsmooth : ContDiff ℝ ∞ u)
    (hΓ : ∀ x ∈ frontier Ω, ∀ t ∈ Ioo 0 T, u (x, t) = 0) (j : ℕ) :
    ∀ x ∈ frontier Ω, (Laplacian.laplacian^[j] fun y ↦ u (y, 0)) x = 0 ∧
      (Laplacian.laplacian^[j] fun y ↦ timeDeriv u (y, 0)) x = 0 := by
  intro x hx
  obtain ⟨h0, h1⟩ := hu.timeDeriv_iterate_eqOn hΩ hsmooth j
  have hcl : closure Ω ×ˢ Icc 0 T ⊆ closure (Ω ×ˢ Ioo 0 T) := by
    rw [closure_prod_eq, closure_Ioo hT.ne]
  have hsub : Ω ×ˢ Ioo 0 T ⊆ closure Ω ×ˢ Icc 0 T := prod_mono subset_closure Ioo_subset_Icc_self
  have hx0 : (x, (0 : ℝ)) ∈ closure Ω ×ˢ Icc 0 T :=
    ⟨frontier_subset_closure hx, left_mem_Icc.2 hT.le⟩
  constructor
  · -- `Δ^j u (x, 0) = ∂ₜ^{2j} u (x, 0) = 0`
    have h := h0.of_subset_closure (contDiff_timeDeriv_iterate hsmooth _).continuous.continuousOn
      (contDiff_spaceLaplacian_iterate hsmooth j).continuous.continuousOn hsub hcl hx0
    rw [← spaceLaplacian_iterate_slice]
    exact h.symm.trans (timeDeriv_iterate_apply_zero_eq_zero hT hsmooth (hΓ x hx) _)
  · -- `Δ^j ∂ₜ u (x, 0) = ∂ₜ^{2j+1} u (x, 0) = 0`
    have h := h1.of_subset_closure (contDiff_timeDeriv_iterate hsmooth _).continuous.continuousOn
      (contDiff_spaceLaplacian_iterate (contDiff_timeDeriv hsmooth) j).continuous.continuousOn
      hsub hcl hx0
    rw [← spaceLaplacian_iterate_slice]
    exact h.symm.trans (timeDeriv_iterate_apply_zero_eq_zero hT hsmooth (hΓ x hx) _)

end Classical

end Wave

namespace Wave

open LinearPMap.PowDomain SobolevMultiIndex Elliptic

section LaplacianDomain

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The domains $D_m$ of the Dirichlet Laplacian, and $D(A^k)$ -/

variable (Ω) in
/-- The **domains $D_m$ of the Dirichlet Laplacian**, subsets of $L^2(\Omega)$ defined by recursion
on $m$: $D_0 = L^2(\Omega)$, $D_1 = H^1_0(\Omega)$ (the range of the inclusion $\iota$), and
$$D_{m+2} = \{ f \in D(-\Delta) : -\Delta f \in D_m \}.$$
So $D_{2\ell} = D((-\Delta)^\ell)$ and $D_{2\ell+1} = \{ f \in D((-\Delta)^\ell) :
(-\Delta)^\ell f \in H^1_0(\Omega) \}$ (`Wave.memLaplacianDomain_two_mul_iff`,
`Wave.memLaplacianDomain_two_mul_add_one_iff`). The domain of the $k$-th power of the wave
operator is $D_{k+1} \times D_k$ (`Wave.mem_operator_powGraph_iff`).

The set $D_m$ is the space $\{ w \in H^m(\Omega) : \Delta^j w = 0 \text{ on } \Gamma \text{ for
} 2j < m \}$ of the display in the proof of Theorem 10.8 of [brezis2011functional], §10.3,
before the Sobolev spaces are read in. On a $C^m$ domain with bounded boundary,
$D_m \subseteq H^m(\Omega)$ (`Wave.MemLaplacianDomain.exists_sobolev`). -/
def MemLaplacianDomain :
    ℕ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) → Prop
  | 0, _ => True
  | 1, f => ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = f
  | m + 2, f => f ∈ dirichletLaplacianDomain Ω ∧
      MemLaplacianDomain m (dirichletLaplacianApply Ω f)

variable {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- Every $f \in L^2(\Omega)$ lies in $D_0$: $D_0 = L^2(\Omega)$. -/
theorem memLaplacianDomain_zero : MemLaplacianDomain Ω 0 f := trivial

/-- $D_1 = H^1_0(\Omega)$: $f \in D_1$ if and only if $f = \iota w$ for some $w \in H^1_0(\Omega)$.
-/
theorem memLaplacianDomain_one_iff :
    MemLaplacianDomain Ω 1 f ↔ ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = f :=
  Iff.rfl

/-- $D_{m+2} = \{ f \in D(-\Delta) : -\Delta f \in D_m \}$: $f \in D_{m+2}$ if and only if
$f \in D(-\Delta)$ and $-\Delta f \in D_m$. -/
theorem memLaplacianDomain_add_two_iff {m : ℕ} :
    MemLaplacianDomain Ω (m + 2) f ↔ f ∈ dirichletLaplacianDomain Ω ∧
      MemLaplacianDomain Ω m (dirichletLaplacianApply Ω f) :=
  Iff.rfl

/-- Each $D_m$ is closed under scalar multiplication: if $f \in D_m$ and $c \in \mathbb{R}$, then
$cf \in D_m$. -/
theorem MemLaplacianDomain.smul {m : ℕ} (c : ℝ) :
    ∀ {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))},
      MemLaplacianDomain Ω m f → MemLaplacianDomain Ω m (c • f) := by
  induction m using Nat.twoStepInduction with
  | zero => intro f _; trivial
  | one =>
    rintro f ⟨w, hw⟩
    exact ⟨c • w, by rw [_root_.map_smul, hw]⟩
  | more m ih _ =>
    rintro f ⟨hf, hf'⟩
    refine ⟨Submodule.smul_mem _ c hf, ?_⟩
    rw [dirichletLaplacianApply_smul c hf]
    exact ih hf'

/-- Each $D_m$ is closed under negation: if $f \in D_m$, then $-f \in D_m$. -/
theorem MemLaplacianDomain.neg {m : ℕ} (h : MemLaplacianDomain Ω m f) :
    MemLaplacianDomain Ω m (-f) := by
  simpa using h.smul (-1)

/-- For every $m$, $-f \in D_m$ if and only if $f \in D_m$. -/
theorem memLaplacianDomain_neg_iff {m : ℕ} :
    MemLaplacianDomain Ω m (-f) ↔ MemLaplacianDomain Ω m f :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ h.neg⟩

/-- $D_{m+1} \subseteq H^1_0(\Omega)$: every $f \in D_{m+1}$ is $\iota w$ for some
$w \in H^1_0(\Omega)$. -/
theorem MemLaplacianDomain.exists_fnL_eq {m : ℕ} :
    ∀ {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))},
      MemLaplacianDomain Ω (m + 1) f → ∃ w : SobolevEuclideanZero N 1 2 Ω,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
          = f := by
  cases m with
  | zero => intro f h; exact h
  | succ m => rintro f ⟨hf, -⟩; exact dirichletLaplacian_exists_sobolevZero_lift ⟨f, hf⟩

/-- For every $m$, $f \in D_{m+1}$ if and only if $f \in H^1_0(\Omega)$ and $-f \in D_{m+1}$. This
is the form that appears in the induction of `Wave.mem_operator_powGraph_iff`. -/
theorem memLaplacianDomain_succ_iff_neg {m : ℕ} :
    MemLaplacianDomain Ω (m + 1) f ↔ (∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = f) ∧ MemLaplacianDomain Ω (m + 1) (-f) :=
  ⟨fun h ↦ ⟨h.exists_fnL_eq, h.neg⟩, fun h ↦ memLaplacianDomain_neg_iff.1 h.2⟩

/-- Let $U = (u, v) \in D(A)$, so that $AU = (-\tilde v, -\Delta u)$. Then the first component of
$AU$, read in $L^2(\Omega)$, lies in $D_{k+1}$ and the second lies in $D_k$ if and only if
$v \in D_{k+1}$ and $-\Delta u \in D_k$. -/
theorem memLaplacianDomain_operator_apply_iff (k : ℕ) (U : (operator Ω).domain) :
    (MemLaplacianDomain Ω (k + 1) (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (operator Ω U).fst) ∧
      MemLaplacianDomain Ω k (operator Ω U).snd) ↔
    (MemLaplacianDomain Ω (k + 1) (U : phaseSpace Ω).snd ∧
      MemLaplacianDomain Ω k (dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst))) := by
  rw [fnL_operator_apply_fst, memLaplacianDomain_neg_iff]
  exact Iff.rfl

set_option maxHeartbeats 400000 in
-- The `k + 1` step checks `MemLaplacianDomain Ω (k + 1 + 1) _` by unfolding its structural
-- recursion, which needs about twice the default budget since the v4.36.0-rc2 bump.
/-- **The domain of $A^k$**: $D(A^k) = D_{k+1} \times D_k$. Precisely, a point $U = (u, v)$ of the
phase space is the base point of an element of $D(A^k)$ if and only if $\iota u \in D_{k+1}$ and
$v \in D_k$. This is the display in the proof of Theorem 10.8 of [brezis2011functional], §10.3,
read on the weak domains.

The space $D(A^k)$ is `LinearPMap.PowDomain`, the tuples $(U, AU, \dots, A^k U)$, and the base
point is the coordinate $0$ (`LinearPMap.PowDomain.applyL`). The proof is by induction on $k$,
through $D(A^{k+1}) = \{ U \in D(A) : AU \in D(A^k) \}$
(`LinearPMap.PowDomain.exists_applyL_zero_eq_succ_iff`) and $A(u, v) = (-v, -\Delta u)$. -/
theorem mem_operator_powGraph_iff (k : ℕ) (U : phaseSpace Ω) :
    (∃ x : (operator Ω).PowDomain k, applyL (operator Ω) k 0 x = U) ↔
      MemLaplacianDomain Ω (k + 1) (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst) ∧
      MemLaplacianDomain Ω k U.snd := by
  induction k generalizing U with
  | zero =>
    refine ⟨fun _ ↦ ⟨⟨U.fst, rfl⟩, trivial⟩, fun _ ↦ ?_⟩
    exact ⟨LinearPMap.PowDomain.mk (operator Ω) (fun _ ↦ U) fun i ↦ i.elim0, rfl⟩
  | succ k ih =>
    rw [exists_applyL_zero_eq_succ_iff]
    constructor
    · rintro ⟨hU, y, hy⟩
      have h1 := (memLaplacianDomain_operator_apply_iff k ⟨U, hU⟩).1 ((ih _).1 ⟨y, hy⟩)
      obtain ⟨hU1, -⟩ := mem_operator_domain_iff.1 hU
      exact ⟨⟨hU1, h1.2⟩, h1.1⟩
    · rintro ⟨⟨hU1, hU2⟩, hv⟩
      have hU : U ∈ (operator Ω).domain := mem_operator_domain_iff.2 ⟨hU1, hv.exists_fnL_eq⟩
      exact ⟨hU, (ih _).2 ((memLaplacianDomain_operator_apply_iff k ⟨U, hU⟩).2 ⟨hv, hU2⟩)⟩

/-- Let $f \in D(-\Delta)$, and let $-\Delta f$ be the base point of an element of
$D((-\Delta)^\ell)$. Then $f$ is the base point of an element of $D((-\Delta)^{\ell+1})$. This
is the forward inductive step of $D_{2\ell} = D((-\Delta)^\ell)$.

The element is `LinearPMap.PowDomain.cons`. -/
theorem exists_powDomain_succ_of_apply {ℓ : ℕ} (hf : f ∈ dirichletLaplacianDomain Ω)
    (y : (dirichletLaplacian Ω).PowDomain ℓ)
    (hy : applyL (dirichletLaplacian Ω) ℓ 0 y = dirichletLaplacianApply Ω f) :
    ∃ x : (dirichletLaplacian Ω).PowDomain (ℓ + 1),
      applyL (dirichletLaplacian Ω) (ℓ + 1) 0 x = f :=
  ⟨cons ⟨f, hf⟩ y ((dirichletLaplacian_apply ⟨f, hf⟩).trans hy.symm), applyL_cons_zero _ _ _⟩

/-- Let $f$ be the base point of an element of $D((-\Delta)^{\ell+1})$. Then $f \in D(-\Delta)$, and
$-\Delta f$ is the base point of an element of $D((-\Delta)^\ell)$. This is the backward
inductive step of $D_{2\ell} = D((-\Delta)^\ell)$.

The element is given by `LinearPMap.PowDomain.shiftL`. -/
theorem mem_and_exists_powDomain_of_powDomain_succ {ℓ : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain (ℓ + 1))
    (hx : applyL (dirichletLaplacian Ω) (ℓ + 1) 0 x = f) :
    f ∈ dirichletLaplacianDomain Ω ∧ ∃ y : (dirichletLaplacian Ω).PowDomain ℓ,
      applyL (dirichletLaplacian Ω) ℓ 0 y = dirichletLaplacianApply Ω f := by
  have hf : f ∈ dirichletLaplacianDomain Ω := by
    rw [← hx]
    exact applyL_mem_domain x 0
  exact ⟨hf, shiftL (dirichletLaplacian Ω) ℓ x, (applyL_zero_shiftL x).trans
    ((dirichletLaplacian_apply _).trans (congrArg (dirichletLaplacianApply Ω) hx))⟩

/-- $D_{2\ell} = D((-\Delta)^\ell)$: a function $f \in L^2(\Omega)$ lies in $D_{2\ell}$ if and only
if it is the base point of an element of $D((-\Delta)^\ell)$.

The space $D((-\Delta)^\ell)$ is `LinearPMap.PowDomain` of `dirichletLaplacian`. -/
theorem memLaplacianDomain_two_mul_iff (ℓ : ℕ) :
    ∀ {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))},
      MemLaplacianDomain Ω (2 * ℓ) f ↔
        ∃ x : (dirichletLaplacian Ω).PowDomain ℓ, applyL (dirichletLaplacian Ω) ℓ 0 x = f := by
  induction ℓ with
  | zero =>
    intro f
    exact ⟨fun _ ↦ ⟨LinearPMap.PowDomain.mk (dirichletLaplacian Ω) (fun _ ↦ f) fun i ↦ i.elim0,
      applyL_mk _ _ 0⟩, fun _ ↦ trivial⟩
  | succ ℓ ih =>
    intro f
    change MemLaplacianDomain Ω (2 * ℓ + 2) f ↔ _
    refine memLaplacianDomain_add_two_iff.trans ((and_congr_right fun _ ↦ ih).trans ?_)
    constructor
    · rintro ⟨hf, y, hy⟩
      exact exists_powDomain_succ_of_apply hf y hy
    · rintro ⟨x, hx⟩
      exact mem_and_exists_powDomain_of_powDomain_succ x hx

/-- $D_{2\ell+1} = \{ f \in D((-\Delta)^\ell) : (-\Delta)^\ell f \in H^1_0(\Omega) \}$: a function
$f \in L^2(\Omega)$ lies in $D_{2\ell+1}$ if and only if it is the base point of an element $x$
of $D((-\Delta)^\ell)$ whose last coordinate $(-\Delta)^\ell f$ lies in $H^1_0(\Omega)$.

The space $D((-\Delta)^\ell)$ is `LinearPMap.PowDomain` of `dirichletLaplacian`, and the last
coordinate of $x$ is `LinearPMap.PowDomain.applyL` at `Fin.last ℓ`. -/
theorem memLaplacianDomain_two_mul_add_one_iff (ℓ : ℕ) :
    ∀ {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))},
      MemLaplacianDomain Ω (2 * ℓ + 1) f ↔
        ∃ x : (dirichletLaplacian Ω).PowDomain ℓ, applyL (dirichletLaplacian Ω) ℓ 0 x = f ∧
          ∃ w : SobolevEuclideanZero N 1 2 Ω,
            SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
              w = applyL (dirichletLaplacian Ω) ℓ (Fin.last ℓ) x := by
  induction ℓ with
  | zero =>
    intro f
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨LinearPMap.PowDomain.mk (dirichletLaplacian Ω) (fun _ ↦ f) fun i ↦ i.elim0,
        applyL_mk _ _ 0, w, hw.trans (applyL_mk (A := dirichletLaplacian Ω) (fun _ ↦ f)
          (fun i ↦ i.elim0) (Fin.last 0)).symm⟩
    · rintro ⟨x, hx, w, hw⟩
      exact ⟨w, hw.trans ((congrArg (fun i ↦ applyL (dirichletLaplacian Ω) 0 i x)
        (by simp : Fin.last 0 = 0)).trans hx)⟩
  | succ ℓ ih =>
    intro f
    change MemLaplacianDomain Ω (2 * ℓ + 1 + 2) f ↔ _
    refine memLaplacianDomain_add_two_iff.trans ((and_congr_right fun _ ↦ ih).trans ?_)
    constructor
    · rintro ⟨hf, y, hy, w, hw⟩
      refine ⟨cons ⟨f, hf⟩ y ((dirichletLaplacian_apply ⟨f, hf⟩).trans hy.symm),
        applyL_cons_zero _ _ _, w, ?_⟩
      exact hw.trans ((applyL_cons_succ _ _ _ (Fin.last ℓ)).symm.trans
        (congrArg (fun i ↦ applyL (dirichletLaplacian Ω) (ℓ + 1) i _) (Fin.succ_last ℓ)))
    · rintro ⟨x, hx, w, hw⟩
      refine ⟨(mem_and_exists_powDomain_of_powDomain_succ x hx).1,
        shiftL (dirichletLaplacian Ω) ℓ x, ?_, w, ?_⟩
      · exact (applyL_zero_shiftL x).trans ((dirichletLaplacian_apply _).trans
          (congrArg (dirichletLaplacianApply Ω) hx))
      · exact hw.trans ((congrArg (fun i ↦ applyL (dirichletLaplacian Ω) (ℓ + 1) i x)
          (Fin.succ_last ℓ).symm).trans (applyL_shiftL (Fin.last ℓ) x).symm)

end LaplacianDomain

end Wave

namespace Wave

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

/-! ### Theorem 10.8: $D(A^k) \subseteq H^{k+1}(\Omega) \times H^k(\Omega)$ -/

section Regularity

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^{2\ell}$ with bounded
boundary. Then every $f \in D_{2\ell}$ is the function of an element of $H^{2\ell}(\Omega)$.

This is Theorem 9.25 through `dirichletLaplacian_exists_sobolev_of_powDomain`. The class
$C^{2\ell}$ is `IsContDiffChartDomain`. -/
theorem MemLaplacianDomain.exists_sobolev_two_mul (ℓ : ℕ)
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : MemLaplacianDomain Ω (2 * ℓ) f) :
    ∃ w : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w = f := by
  obtain ⟨x, hx⟩ := (memLaplacianDomain_two_mul_iff ℓ).1 h
  obtain ⟨w, hw⟩ := dirichletLaplacian_exists_sobolev_of_powDomain ℓ hΩ hΓ x
  exact ⟨w, hw.trans hx⟩

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^{2\ell+1}$ with bounded
boundary. Then every $f \in D_{2\ell+1}$ is the function of an element of $H^{2\ell+1}(\Omega)$.

The proof uses `dirichletLaplacian_exists_sobolev_of_powDomain_of_last`. The class $C^{2\ell+1}$
is `IsContDiffChartDomain`. -/
theorem MemLaplacianDomain.exists_sobolev_two_mul_add_one (ℓ : ℕ)
    (hΩ : IsContDiffChartDomain (2 * ℓ + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : MemLaplacianDomain Ω (2 * ℓ + 1) f) :
    ∃ w : SobolevEuclidean (d + 1) (2 * ℓ + 1) 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ + 1) 2 Ω volume w = f := by
  obtain ⟨x, hx, hlast⟩ := (memLaplacianDomain_two_mul_add_one_iff ℓ).1 h
  obtain ⟨w, hw⟩ :=
    dirichletLaplacian_exists_sobolev_of_powDomain_of_last ℓ (2 * ℓ + 1) rfl hΩ hΓ x hlast
  exact ⟨w, hw.trans hx⟩

/-- **$D_m \subseteq H^m(\Omega)$.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class
$C^m$ with bounded boundary. Then every $f \in D_m$ is the function of an element of
$H^m(\Omega)$. This is the reading of the display in the proof of Theorem 10.8 of
[brezis2011functional], §10.3, in Sobolev spaces.

The class $C^m$ is `IsContDiffChartDomain`, and the function of an element of $H^m(\Omega)$ is
`SobolevMultiIndex.fnL`. Even $m$ is $D((-\Delta)^\ell) \subseteq H^{2\ell}(\Omega)$
(`dirichletLaplacian_exists_sobolev_of_powDomain`, Theorem 9.25), and odd $m$ is its companion
`dirichletLaplacian_exists_sobolev_of_powDomain_of_last`. -/
theorem MemLaplacianDomain.exists_sobolev (m : ℕ)
    (hΩ : IsContDiffChartDomain m (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : MemLaplacianDomain Ω m f) :
    ∃ w : SobolevEuclidean (d + 1) m 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω volume w = f := by
  obtain ⟨ℓ, hℓ | hℓ⟩ := Nat.even_or_odd' m
  · subst hℓ
    exact MemLaplacianDomain.exists_sobolev_two_mul ℓ hΩ hΓ h
  · subst hℓ
    exact MemLaplacianDomain.exists_sobolev_two_mul_add_one ℓ hΩ hΓ h

end Regularity

section Coord

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The wave operator $A$ is closed, on every open set $\Omega$.

The operator $A + I$ is maximal monotone, hence closed, and closedness is unchanged by the shift
(`LinearPMap.IsAddSmulId.isClosed`). -/
theorem operator_isClosed : (operator Ω).IsClosed :=
  (isAddSmulId_id_vadd (operator Ω)).isClosed operator_add_id_isMaximalMonotone.isClosed

variable (Ω) in
/-- The bounded linear map $D(A^k) \to L^2(\Omega)$, $x \mapsto \iota u$, where $(u, v)$ is the base
point of $x$. -/
def fstCoordL (k : ℕ) :
    (operator Ω).PowDomain k →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume).comp
    ((phaseSpace.fstL Ω).comp (applyL (operator Ω) k 0))

/-- The value of `Wave.fstCoordL` at $x \in D(A^k)$ is $\iota u$, where $(u, v)$ is the base point
of $x$. -/
theorem fstCoordL_apply {k : ℕ} (x : (operator Ω).PowDomain k) :
    fstCoordL Ω k x = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume (applyL (operator Ω) k 0 x).fst :=
  rfl

variable (Ω) in
/-- The bounded linear map $D(A^k) \to L^2(\Omega)$, $x \mapsto v$, where $(u, v)$ is the base point
of $x$. -/
def sndCoordL (k : ℕ) :
    (operator Ω).PowDomain k →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (phaseSpace.sndL Ω).comp (applyL (operator Ω) k 0)

/-- The value of `Wave.sndCoordL` at $x \in D(A^k)$ is $v$, where $(u, v)$ is the base point of $x$.
-/
theorem sndCoordL_apply {k : ℕ} (x : (operator Ω).PowDomain k) :
    sndCoordL Ω k x = (applyL (operator Ω) k 0 x).snd :=
  rfl

/-- For $x \in D(A^k)$ with base point $(u, v)$, $\iota u \in D_{k+1}$. -/
theorem memLaplacianDomain_fstCoordL (k : ℕ) (x : (operator Ω).PowDomain k) :
    MemLaplacianDomain Ω (k + 1) (fstCoordL Ω k x) :=
  ((mem_operator_powGraph_iff k _).1 ⟨x, rfl⟩).1

/-- For $x \in D(A^k)$ with base point $(u, v)$, $v \in D_k$. -/
theorem memLaplacianDomain_sndCoordL (k : ℕ) (x : (operator Ω).PowDomain k) :
    MemLaplacianDomain Ω k (sndCoordL Ω k x) :=
  ((mem_operator_powGraph_iff k _).1 ⟨x, rfl⟩).2

end Coord

section PowDomainToSobolev

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^{k+1}$ with bounded boundary,
and let $x \in D(A^k)$ have base point $(u, v)$. Then $\iota u$ is the function of an element of
$H^{k+1}(\Omega)$. -/
theorem exists_sobolev_fstCoordL (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    ∃ w : SobolevEuclidean (d + 1) (k + 1) 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (k + 1) 2 Ω volume w
        = fstCoordL Ω k x :=
  (memLaplacianDomain_fstCoordL k x).exists_sobolev (k + 1) hΩ hΓ

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^k$ with bounded boundary, and
let $x \in D(A^k)$ have base point $(u, v)$. Then $v$ is the function of an element of
$H^k(\Omega)$. -/
theorem exists_sobolev_sndCoordL (k : ℕ)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    ∃ z : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume z = sndCoordL Ω k x :=
  (memLaplacianDomain_sndCoordL k x).exists_sobolev k hΩ hΓ

/-- On an open set $\Omega \subseteq \mathbb{R}^{d+1}$ of class $C^{k+1}$ with bounded boundary, the
**continuous injection $D(A^k) \to H^{k+1}(\Omega)$ of the first component**: a bounded linear
map that sends $x$, with base point $(u, v)$, to the element of $H^{k+1}(\Omega)$ whose function
is $\iota u$ (`Wave.fnL_powDomainToSobolevFstL`).

The map is chosen by `SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq`,
which proves its continuity by the closed graph theorem. The space $D(A^k)$ is complete because
$A$ is closed (`Wave.operator_isClosed`). -/
def operator.powDomainToSobolevFstL (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (operator Ω).PowDomain k →L[ℝ] SobolevEuclidean (d + 1) (k + 1) 2 Ω :=
  haveI : CompleteSpace ((operator Ω).PowDomain k) := operator_isClosed.completeSpace_powDomain k
  Classical.choose (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := fstCoordL Ω k) (exists_sobolev_fstCoordL k hΩ hΓ))

/-- For $x \in D(A^k)$ with base point $(u, v)$, the function of
`Wave.operator.powDomainToSobolevFstL` at $x$ is $\iota u$. -/
theorem fnL_powDomainToSobolevFstL (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (k + 1) 2 Ω volume
      (operator.powDomainToSobolevFstL k hΩ hΓ x) = fstCoordL Ω k x :=
  haveI : CompleteSpace ((operator Ω).PowDomain k) := operator_isClosed.completeSpace_powDomain k
  Classical.choose_spec (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := fstCoordL Ω k) (exists_sobolev_fstCoordL k hΩ hΓ)) x

/-- On an open set $\Omega \subseteq \mathbb{R}^{d+1}$ of class $C^k$ with bounded boundary, the
**continuous injection $D(A^k) \to H^k(\Omega)$ of the second component**: a bounded linear map
that sends $x$, with base point $(u, v)$, to the element of $H^k(\Omega)$ whose function is $v$
(`Wave.fnL_powDomainToSobolevSndL`).

The map is chosen as for `Wave.operator.powDomainToSobolevFstL`. -/
def operator.powDomainToSobolevSndL (k : ℕ)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (operator Ω).PowDomain k →L[ℝ] SobolevEuclidean (d + 1) k 2 Ω :=
  haveI : CompleteSpace ((operator Ω).PowDomain k) := operator_isClosed.completeSpace_powDomain k
  Classical.choose (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := sndCoordL Ω k) (exists_sobolev_sndCoordL k hΩ hΓ))

/-- For $x \in D(A^k)$ with base point $(u, v)$, the function of
`Wave.operator.powDomainToSobolevSndL` at $x$ is $v$. -/
theorem fnL_powDomainToSobolevSndL (k : ℕ)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume
      (operator.powDomainToSobolevSndL k hΩ hΓ x) = sndCoordL Ω k x :=
  haveI : CompleteSpace ((operator Ω).PowDomain k) := operator_isClosed.completeSpace_powDomain k
  Classical.choose_spec (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := sndCoordL Ω k) (exists_sobolev_sndCoordL k hΩ hΓ)) x

/-- **$D(A^k) \subseteq H^{k+1}(\Omega) \times H^k(\Omega)$ with continuous injection.** On an open
set $\Omega \subseteq \mathbb{R}^{d+1}$ of class $C^{k+1}$ with bounded boundary, the bounded
linear map $x \mapsto (w, z)$ on $D(A^k)$, where $(u, v)$ is the base point of $x$,
$w \in H^{k+1}(\Omega)$ has the function $\iota u$, and $z \in H^k(\Omega)$ has the function $v$
(`Wave.fnL_powDomainToSobolevL_fst`, `Wave.fnL_powDomainToSobolevL_snd`). Its boundedness is the
estimate $\|w\|_{H^{k+1}} + \|z\|_{H^k} \le C \|x\|_{D(A^k)}$. This is the "in particular" of
the proof of Theorem 10.8 of [brezis2011functional], §10.3.

The memberships come from $D(A^k) = D_{k+1} \times D_k$ (`Wave.mem_operator_powGraph_iff`) and
$D_m \subseteq H^m(\Omega)$ (`Wave.MemLaplacianDomain.exists_sobolev`, Theorem 9.25 at every
order), and the continuity from the closed graph theorem. -/
def operator.powDomainToSobolevL (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (operator Ω).PowDomain k →L[ℝ]
      SobolevEuclidean (d + 1) (k + 1) 2 Ω × SobolevEuclidean (d + 1) k 2 Ω :=
  (operator.powDomainToSobolevFstL k hΩ hΓ).prod
    (operator.powDomainToSobolevSndL k (hΩ.of_le (by exact_mod_cast Nat.le_succ k)) hΓ)

/-- For $x \in D(A^k)$ with base point $(u, v)$, the first component of
`Wave.operator.powDomainToSobolevL` at $x$ has the function $\iota u$. -/
theorem fnL_powDomainToSobolevL_fst (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (k + 1) 2 Ω volume
      (operator.powDomainToSobolevL k hΩ hΓ x).1 = fstCoordL Ω k x :=
  fnL_powDomainToSobolevFstL k hΩ hΓ x

/-- For $x \in D(A^k)$ with base point $(u, v)$, the second component of
`Wave.operator.powDomainToSobolevL` at $x$ has the function $v$. -/
theorem fnL_powDomainToSobolevL_snd (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume
      (operator.powDomainToSobolevL k hΩ hΓ x).2 = sndCoordL Ω k x :=
  fnL_powDomainToSobolevSndL k _ hΓ x

end PowDomainToSobolev

/-! ### Theorem 10.8 -/

section Regularity10_8

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {u₀ : SobolevEuclideanZero N 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- Let $x \in D(A^k)$ have base point $(u_0, v_0)$. Then for every $t$,
$e^{1 \cdot t} S_{A+I}(t) (u_0, v_0)$ is the phase-space solution `Wave.phaseSolution` at $t$.
This identifies the shifted semigroup curve of Theorem 7.5 for $A + I$
(`LinearPMap.IsMaximalMonotone.contDiffOnPowDomain_exp_smul_semigroup` with $c = 1$). -/
theorem exp_smul_semigroup_eq_phaseSolution {k : ℕ} (x : (operator Ω).PowDomain k)
    (hx : applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀) (t : ℝ) :
    Real.exp (1 * t) • ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω)
      +ᵥ operator Ω).semigroup t (applyL (operator Ω) k 0 x) = phaseSolution Ω u₀ v₀ t := by
  rw [one_mul, hx]
  rfl

/-- Let $u$ solve the wave equation with data $(u_0, v_0)$, and let $t \ge 0$. Then the phase-space
solution is $U(t) = (\tilde u(t), u'(t))$, where $\tilde u(t)$ is the $H^1_0$ preimage of $u(t)$
and $u'$ is the derivative within $[0, \infty)$.

The proof is uniqueness for $U' + AU = 0$ (`Wave.operator_eqOn_of_isSolutionOn`). -/
theorem IsSolution.phaseSolution_eq (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    phaseSolution Ω u₀ v₀ t
      = phaseSpace.mk Ω (toSobolevZero Ω (u t)) (derivWithin u (Ici 0) t) :=
  operator_eqOn_of_isSolutionOn (isSolutionOn_phaseSolution h.memOperatorDomain_mk)
    h.isSolutionOn ht

/-- **Regularity in $D(A^j)$.** Let $\Omega \subseteq \mathbb{R}^N$ be open, let $u$ solve the wave
equation with data $(u_0, v_0)$, let $(u_0, v_0)$ be the base point of an element of $D(A^k)$,
and let $j \le k$. Then
$$U = (\tilde u, u') \in C^{k-j}([0, \infty); D(A^j)).$$
This is the step "by Theorem 7.5" of the proof of Theorem 10.8 of [brezis2011functional].

The class is `LinearPMap.ContDiffOnPowDomain`. The proof applies Theorem 7.5 to the maximal
monotone operator $A + I$ and shifts back by $e^t$
(`LinearPMap.IsMaximalMonotone.contDiffOnPowDomain_exp_smul_semigroup`, with the transport of
$D((A + I)^j)$ to $D(A^j)$), at $U(t) = e^t S_{A+I}(t)(u_0, v_0)$. -/
theorem IsSolution.contDiffOnPowDomain_of_powDomain (h : IsSolution Ω u₀ v₀ u) {k : ℕ}
    (x : (operator Ω).PowDomain k)
    (hx : applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀) {j : ℕ} (hj : j ≤ k) :
    (operator Ω).ContDiffOnPowDomain (k - j : ℕ) j
      (fun t ↦ phaseSpace.mk Ω (toSobolevZero Ω (u t)) (derivWithin u (Ici 0) t)) (Ici 0) := by
  have h1 := operator_add_id_isMaximalMonotone.contDiffOnPowDomain_exp_smul_semigroup
    (isAddSmulId_id_vadd (operator Ω)) x hj
  exact h1.congr fun t ht ↦ (exp_smul_semigroup_eq_phaseSolution x hx t).trans
    (h.phaseSolution_eq ht)

end Regularity10_8

section Regularity10_8'

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {u₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **Regularity in Sobolev spaces.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of
class $C^{j+1}$ with bounded boundary, let $u$ solve the wave equation with data $(u_0, v_0)$,
let $(u_0, v_0)$ be the base point of an element of $D(A^k)$, and let $j \le k$. Then
$$u \in C^{k-j}([0, \infty); H^{j+1}(\Omega)),$$
through the inclusion $H^{j+1}(\Omega) \to L^2(\Omega)$. This is the step
"$U \in C^{k-j}([0, \infty); D(A^j))$, hence $u \in C^{k-j}([0, \infty); H^{j+1}(\Omega))$" of
the proof of Theorem 10.8 of [brezis2011functional].

The class is `Bochner.ContDiffOnThrough`. The lift to $H^{j+1}(\Omega)$ is the first component
of `Wave.operator.powDomainToSobolevL` applied to the $D(A^j)$-lift of $(\tilde u, u')$
(`Wave.IsSolution.contDiffOnPowDomain_of_powDomain`). -/
theorem IsSolution.contDiffOnThrough_of_powDomain (h : IsSolution Ω u₀ v₀ u) {k : ℕ}
    (x : (operator Ω).PowDomain k)
    (hx : applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀) {j : ℕ} (hj : j ≤ k)
    (hΩ : IsContDiffChartDomain (j + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (j + 1) 2
      Ω volume) (k - j : ℕ) u (Ici 0) := by
  obtain ⟨V, hV0, hV⟩ := h.contDiffOnPowDomain_of_powDomain x hx hj
  refine ⟨operator.powDomainToSobolevFstL j hΩ hΓ ∘ V,
    (operator.powDomainToSobolevFstL j hΩ hΓ).contDiff.comp_contDiffOn hV, fun t ht ↦ ?_⟩
  have e1 : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (j + 1) 2 Ω volume
      ((operator.powDomainToSobolevFstL j hΩ hΓ ∘ V) t) = fstCoordL Ω j (V t) :=
    fnL_powDomainToSobolevFstL j hΩ hΓ (V t)
  have e2 : fstCoordL Ω j (V t) = SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume (toSobolevZero Ω (u t)) :=
    (congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume U.fst) (hV0 t ht)).trans
      (congrArg (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2
        Ω volume) (phaseSpace.mk_fst _ _))
  rw [e1, e2, h.fnL_toSobolevZero_apply ht]

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^\infty$ with bounded
boundary, let $u$ solve the wave equation with data $(u_0, v_0)$, and let $(u_0, v_0)$ be the
base point of an element of $D(A^k)$ for every $k$. Then
$u \in C^\infty([0, \infty); H^m(\Omega))$ for every $m$, through the inclusion
$H^m(\Omega) \to L^2(\Omega)$.

One lift serves all orders (`Bochner.ContDiffOnThrough.infty_of_forall_nat`). It comes from
`Wave.IsSolution.contDiffOnThrough_of_powDomain` at $j = m$ and $k = m + n$, lowered from
$H^{m+1}$ to $H^m$ (`Bochner.ContDiffOnThrough.sobolev_of_le`). -/
theorem IsSolution.contDiffOnThrough_sobolev_forall (h : IsSolution Ω u₀ v₀ u)
    (hU₀ : ∀ k, ∃ x : (operator Ω).PowDomain k,
      applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) (m : ℕ) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω
      volume) ∞ u (Ici 0) := by
  have hm : IsContDiffChartDomain (m + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (WithTop.coe_le_coe.2 le_top)
  have key : ∀ n : ℕ, Bochner.ContDiffOnThrough
      (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (m + 1) 2 Ω volume) n u (Ici 0) := by
    intro n
    obtain ⟨x, hx⟩ := hU₀ (m + n)
    have := h.contDiffOnThrough_of_powDomain x hx (j := m) (by omega) hm hΓ
    rwa [show m + n - m = n by omega] at this
  have hJ : Function.Injective
      (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (m + 1) 2 Ω volume) :=
    fnL_injective
  exact (Bochner.ContDiffOnThrough.infty_of_forall_nat hJ key).sobolev_of_le (Nat.le_succ m)

/-- **Smoothness of the solution for smooth compatible data.** Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^\infty$ with bounded boundary,
let $u$ solve the wave equation with data $(u_0, v_0)$, and let $(u_0, v_0)$ be the base point
of an element of $D(A^k)$ for every $k$. Then $u \in C^\infty(\bar\Omega \times [0, \infty))$:
there is a function $U : \mathbb{R}^{d+1} \times \mathbb{R} \to \mathbb{R}$ with
$U(\cdot, t) = u(t)$ almost everywhere on $\Omega$ for every $t \ge 0$, which is $C^\infty$ on
$\Omega \times (0, \infty)$ and whose derivatives all extend continuously to
$\bar\Omega \times [0, \infty)$. This is Theorem 10.8 of [brezis2011functional].

The source's hypothesis, $u_0, v_0 \in H^k(\Omega)$ for every $k$ with the compatibility
conditions $\Delta^j u_0 = \Delta^j v_0 = 0$ on $\Gamma$, is read as $(u_0, v_0) \in D(A^k)$ for
every $k$, through `Wave.mem_operator_powGraph_iff` and `Wave.MemLaplacianDomain`. The class of
$U$ is `ContDiffOnClosure`. The proof combines
`Wave.IsSolution.contDiffOnThrough_sobolev_forall` with the space–time bridge
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`. -/
theorem IsSolution.contDiffOnClosure_spaceTime (h : IsSolution Ω u₀ v₀ u)
    (hU₀ : ∀ k, ∃ x : (operator Ω).PowDomain k,
      applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      (∀ t ∈ Ici (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ioi 0) :=
  Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici
    (IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ)
    (h.contDiffOnThrough_sobolev_forall hU₀ hΩ hΓ)

end Regularity10_8'

end Wave

namespace Wave

open LinearPMap.PowDomain SobolevMultiIndex Elliptic SobolevEuclidean MeasureTheory.Lp

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### Remark 8: d'Alembert's formula solves the wave equation on $\mathbb{R}$ -/

/-- **Membership in $D(-\Delta)$ through first derivatives in $H^1$.** Let $v \in H^1_0(\Omega)$,
and let $Q_1, \dots, Q_N \in H^1(\Omega)$ with $\partial_i v = Q_i$ almost everywhere on
$\Omega$ for each $i$. Then $f = \iota v$ lies in $D(-\Delta)$, and
$$-\Delta f = -\sum_{i} \partial_i Q_i.$$

The derivatives are weak derivatives (`SobolevMultiIndex.weakDeriv`). This is
`mem_dirichletLaplacianDomain_of_sobolev_two` with the $H^2$ element replaced by the family of
its first derivatives, which is all that the proof uses
(`Elliptic.dirichletForm_eq_load_neg_sum_weakDeriv`). -/
theorem mem_dirichletLaplacianDomain_of_forall_ae_eq {v : SobolevEuclidean N 1 2 Ω}
    (hv : v ∈ SobolevEuclideanZero N 1 2 Ω) (Q : Fin N → SobolevEuclidean N 1 2 Ω)
    (hQ : ∀ i, ⇑(weakDeriv v (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn (Q i)) :
    fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v ∈ dirichletLaplacianDomain Ω
      ∧ dirichletLaplacianApply Ω (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)
        = -∑ i, weakDeriv (Q i) (MultiIndexLE.single i) := by
  have heq' := Elliptic.dirichletForm_eq_load_neg_sum_weakDeriv Q hQ
  exact ⟨⟨v, hv, rfl, _, heq'⟩, (eq_dirichletLaplacianApply hv rfl heq').symm⟩

/-- For $1 \le p < \infty$, the **inclusion $W^{1,p}(\mathbb{R}^N) \to W^{1,p}_0(\mathbb{R}^N)$** as
a bounded linear map of norm at most $1$. The two spaces coincide
(`SobolevEuclideanZero.eq_top`), and the map is the identity. -/
def toZeroTopL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SobolevEuclidean N 1 p ⊤ →L[ℝ] SobolevEuclideanZero N 1 p ⊤ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (SobolevEuclideanZero N 1 p ⊤) LinearMap.id fun u ↦ by
      rw [SobolevEuclideanZero.eq_top hp]; exact Submodule.mem_top)
    1 fun u ↦ by rw [one_mul]; exact le_rfl

/-- For $1 \le p < \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$, the function of `Wave.toZeroTopL` at
$u$ is the function of $u$. -/
theorem fnL_toZeroTopL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p ⊤ volume
      (toZeroTopL hp u) = fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p ⊤ volume u :=
  rfl

/-- For $1 \le p < \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$, `Wave.toZeroTopL` at $u$ is $u$ as an
element of $W^{1,p}(\mathbb{R}^N)$. -/
theorem coe_toZeroTopL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤) :
    (toZeroTopL hp u : SobolevEuclidean N 1 p ⊤) = u :=
  rfl


/-! ### d'Alembert's formula as a solution on $\mathbb{R}$ -/

section DAlembertSolution

local notation "𝔼₁" => EuclideanSpace ℝ (Fin 1)
local notation "𝔟₁" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 1) ℝ)
local notation "𝕖" => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
local notation "L2₁" => Lp ℝ 2 (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 1))) :
  Set (EuclideanSpace ℝ (Fin 1))))

variable (u₀ : SobolevEuclidean 1 2 2 ⊤) (v₀ : SobolevEuclidean 1 1 2 ⊤)

/-- The datum $u_0 \in H^2(\mathbb{R})$ as an element of $H^1(\mathbb{R})$
(`SobolevMultiIndex.toLowerOrderL`). Here $\mathbb{R}$ is $\mathbb{R}^1$,
`EuclideanSpace ℝ (Fin 1)`. -/
abbrev dAlembertU₀ : SobolevEuclidean 1 1 2 ⊤ := toLowerOrderL ℝ 𝔟₁ 2 ⊤ volume (by omega) u₀

/-- The derivative $u_0' \in H^1(\mathbb{R})$ of the datum $u_0 \in H^2(\mathbb{R})$
(`SobolevMultiIndex.partialDerivL`). -/
abbrev dAlembertU₀' : SobolevEuclidean 1 1 2 ⊤ := partialDerivL ℝ 𝔟₁ 2 ⊤ volume 0 u₀

/-- **d'Alembert's formula as a curve in $L^2(\mathbb{R})$**: for $u_0 \in H^2(\mathbb{R})$ and
$v_0 \in H^1(\mathbb{R})$,
$$u(t) = \frac12 (\tau_t u_0 + \tau_{-t} u_0) + \frac12 \int_{-t}^{t} \tau_s v_0 \, ds,$$
where $\tau_t f = f(\cdot + t)$ is the translation. It is the $L^2$ class of $x \mapsto \frac12
(u_0(x + t) + u_0(x - t)) + \frac12 \int_{x - t}^{x + t} v_0(s) \, ds$
(`Wave.coeFn_dAlembertL2`, `Wave.coeFn_dAlembertL2_dAlembert`).

The translations are `MeasureTheory.Lp.translateCurve`, and the integral is
`MeasureTheory.Lp.primitiveCurve`, a Bochner integral in $L^2$ written as
$\int_0^t (\tau_s v_0 + \tau_{-s} v_0) \, ds$. -/
def dAlembertL2 (t : ℝ) : L2₁ :=
  (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) t
      + translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) (-t))
    + (1 / 2 : ℝ) • primitiveCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) t

/-- The time derivative of d'Alembert's curve:
$$u'(t) = \frac12 (\tau_t u_0' - \tau_{-t} u_0') + \frac12 (\tau_t v_0 + \tau_{-t} v_0).$$
-/
def dAlembertL2Deriv (t : ℝ) : L2₁ :=
  (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀' u₀)) t
      - translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀' u₀)) (-t))
    + (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) t
      + translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) (-t))

/-- The second time derivative of d'Alembert's curve, which is also its second space derivative:
$$u''(t) = \frac12 (\tau_t u_0'' + \tau_{-t} u_0'') + \frac12 (\tau_t v_0' - \tau_{-t} v_0').$$
-/
def dAlembertL2Deriv2 (t : ℝ) : L2₁ :=
  (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (weakDeriv (dAlembertU₀' u₀) (MultiIndexLE.single 0)) t
      + translateCurve ℝ 2 𝕖 (weakDeriv (dAlembertU₀' u₀) (MultiIndexLE.single 0)) (-t))
    + (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (weakDeriv v₀ (MultiIndexLE.single 0)) t
      - translateCurve ℝ 2 𝕖 (weakDeriv v₀ (MultiIndexLE.single 0)) (-t))

/-- The weak derivative of $u_0 \in H^2(\mathbb{R})$, taken as an element of $H^1(\mathbb{R})$, is
$u_0'$ read in $L^2(\mathbb{R})$. -/
theorem weakDeriv_dAlembertU₀ :
    weakDeriv (dAlembertU₀ u₀) (MultiIndexLE.single 0) = fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀' u₀) :=
  (fnL_partialDerivL (k := 1) 0 u₀).symm

/-- d'Alembert's curve $u : \mathbb{R} \to L^2(\mathbb{R})$ is differentiable at every $t$, with the
derivative $u'(t)$ of `Wave.dAlembertL2Deriv`. -/
theorem hasDerivAt_dAlembertL2 (t : ℝ) :
    HasDerivAt (dAlembertL2 u₀ v₀) (dAlembertL2Deriv u₀ v₀ t) t := by
  have h1 := ((hasDerivAt_translateCurve_add_neg (by simp) (dAlembertU₀ u₀) 0 t).congr_deriv
    (by rw [weakDeriv_dAlembertU₀])).const_smul (1 / 2 : ℝ)
  have h2 := (hasDerivAt_primitiveCurve 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) (by simp) t).const_smul
    (1 / 2 : ℝ)
  exact h1.add h2

/-- The time derivative $u'$ of d'Alembert's curve is differentiable in $L^2(\mathbb{R})$ at every
$t$, with the derivative $u''(t)$ of `Wave.dAlembertL2Deriv2`. -/
theorem hasDerivAt_dAlembertL2Deriv (t : ℝ) :
    HasDerivAt (dAlembertL2Deriv u₀ v₀) (dAlembertL2Deriv2 u₀ v₀ t) t := by
  have h1 := (hasDerivAt_translateCurve_sub_neg (by simp) (dAlembertU₀' u₀) 0 t).const_smul
    (1 / 2 : ℝ)
  have h2 := (hasDerivAt_translateCurve_add_neg (by simp) v₀ 0 t).const_smul (1 / 2 : ℝ)
  exact h1.add h2

/-- The second derivative $u''$ of d'Alembert's curve is continuous from $\mathbb{R}$ to
$L^2(\mathbb{R})$. -/
theorem continuous_dAlembertL2Deriv2 : Continuous (dAlembertL2Deriv2 u₀ v₀) := by
  have h1 := (continuous_translateCurve_add_neg 𝕖
    (weakDeriv (dAlembertU₀' u₀) (MultiIndexLE.single 0)) (by simp)).const_smul (1 / 2 : ℝ)
  have h2 := (continuous_translateCurve_sub_neg 𝕖
    (weakDeriv v₀ (MultiIndexLE.single 0)) (by simp)).const_smul (1 / 2 : ℝ)
  exact h1.add h2

/-- d'Alembert's curve is in $C^2(\mathbb{R}; L^2(\mathbb{R}))$. -/
theorem contDiff_dAlembertL2 : ContDiff ℝ 2 (dAlembertL2 u₀ v₀) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t ↦ (hasDerivAt_dAlembertL2 u₀ v₀ t).differentiableAt, fun h ↦ by simp at h, ?_⟩
  have e : deriv (dAlembertL2 u₀ v₀) = dAlembertL2Deriv u₀ v₀ :=
    funext fun t ↦ (hasDerivAt_dAlembertL2 u₀ v₀ t).deriv
  rw [e, contDiff_one_iff_deriv]
  refine ⟨fun t ↦ (hasDerivAt_dAlembertL2Deriv u₀ v₀ t).differentiableAt, ?_⟩
  have e2 : deriv (dAlembertL2Deriv u₀ v₀) = dAlembertL2Deriv2 u₀ v₀ :=
    funext fun t ↦ (hasDerivAt_dAlembertL2Deriv u₀ v₀ t).deriv
  rw [e2]
  exact continuous_dAlembertL2Deriv2 u₀ v₀

/-- The translation $\tau_t$ on $H^1(\mathbb{R})$: $w \mapsto w(\cdot + t)$
(`SobolevMultiIndex.translateL`). -/
abbrev dAlembertTL (w : SobolevEuclidean 1 1 2 ⊤) (t : ℝ) : SobolevEuclidean 1 1 2 ⊤ :=
  translateL ℝ 𝔟₁ 1 2 volume (IsTranslationInvariant.top (t • 𝕖)) w

/-- **The lift of d'Alembert's curve to $H^1(\mathbb{R})$**:
$$\tilde u(t) = \frac12 (\tau_t u_0 + \tau_{-t} u_0) + \frac12 \int_{-t}^{t} \tau_s v_0 \, ds
  \in H^1(\mathbb{R}),$$
with the integral a Bochner integral in $H^1(\mathbb{R})$ (`SobolevEuclidean.primitiveCurveL`).
Its function is $u(t)$ (`Wave.fnL_dAlembertH1`). -/
def dAlembertH1 (t : ℝ) : SobolevEuclidean 1 1 2 ⊤ :=
  (1 / 2 : ℝ) • (dAlembertTL (dAlembertU₀ u₀) t + dAlembertTL (dAlembertU₀ u₀) (-t))
    + (1 / 2 : ℝ) • primitiveCurveL 1 𝕖 v₀ t

/-- **The space derivative of d'Alembert's curve**, as an element of $H^1(\mathbb{R})$:
$$\partial_x u(t) = \frac12 (\tau_t u_0' + \tau_{-t} u_0') + \frac12 (\tau_t v_0 - \tau_{-t}
  v_0).$$
-/
def dAlembertH1Space (t : ℝ) : SobolevEuclidean 1 1 2 ⊤ :=
  (1 / 2 : ℝ) • (dAlembertTL (dAlembertU₀' u₀) t + dAlembertTL (dAlembertU₀' u₀) (-t))
    + (1 / 2 : ℝ) • (dAlembertTL v₀ t - dAlembertTL v₀ (-t))

/-- The function of the $H^1$ lift $\tilde u(t)$ is d'Alembert's curve $u(t)$, for every $t$. -/
theorem fnL_dAlembertH1 (t : ℝ) :
    fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertH1 u₀ v₀ t) = dAlembertL2 u₀ v₀ t := by
  change (1 / 2 : ℝ) • (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertTL (dAlembertU₀ u₀) t)
      + fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertTL (dAlembertU₀ u₀) (-t)))
    + (1 / 2 : ℝ) • fnL ℝ 𝔟₁ 1 2 ⊤ volume (primitiveCurveL 1 𝕖 v₀ t) = _
  rw [fnL_primitiveCurveL (by simp) 𝕖 v₀ t]
  rfl

/-- The weak derivative of the $H^1$ lift $\tilde u(t)$ is the function of $\partial_x u(t)$
(`Wave.dAlembertH1Space`), for every $t$. The space derivative of
$\int_{-t}^{t} \tau_s v_0 \, ds$ is $\tau_t v_0 - \tau_{-t} v_0$
(`SobolevEuclidean.primitiveCurve_weakDeriv_single`). -/
theorem weakDeriv_dAlembertH1 (t : ℝ) :
    weakDeriv (dAlembertH1 u₀ v₀ t) (MultiIndexLE.single 0)
      = fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertH1Space u₀ v₀ t) := by
  change (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (weakDeriv (dAlembertU₀ u₀) (MultiIndexLE.single 0)) t
      + translateCurve ℝ 2 𝕖 (weakDeriv (dAlembertU₀ u₀) (MultiIndexLE.single 0)) (-t))
    + (1 / 2 : ℝ) • weakDeriv (primitiveCurveL 1 𝕖 v₀ t) (MultiIndexLE.single 0) = _
  simp only [weakDeriv_primitiveCurveL (by simp) 𝕖 v₀ t,
    primitiveCurve_weakDeriv_single (by simp) v₀ 0 t, weakDeriv_dAlembertU₀]
  rfl

/-- The weak derivative of $\partial_x u(t)$ (`Wave.dAlembertH1Space`) is the second derivative
$u''(t)$ (`Wave.dAlembertL2Deriv2`), for every $t$. -/
theorem weakDeriv_dAlembertH1Space (t : ℝ) :
    weakDeriv (dAlembertH1Space u₀ v₀ t) (MultiIndexLE.single 0) = dAlembertL2Deriv2 u₀ v₀ t :=
  rfl

/-- The $H^1$ lift of d'Alembert's curve is in $C^1(\mathbb{R}; H^1(\mathbb{R}))$. -/
theorem contDiff_dAlembertH1 : ContDiff ℝ 1 (dAlembertH1 u₀ v₀) :=
  ((contDiff_translateL_add_neg (by simp) u₀ 0).const_smul (1 / 2 : ℝ)).add
    ((contDiff_primitiveCurveL (by simp) 𝕖 v₀).const_smul (1 / 2 : ℝ))

/-- For every $t$, d'Alembert's curve satisfies $u(t) \in D(-\Delta)$ and $-\Delta u(t) = -u''(t)$
on $\Omega = \mathbb{R}$.

The proof applies `Wave.mem_dirichletLaplacianDomain_of_forall_ae_eq` to the $H^1$ lift and to
the $H^1$ element `Wave.dAlembertH1Space` that carries its space derivative. -/
theorem dAlembertL2_mem_dirichletLaplacianDomain (t : ℝ) :
    dAlembertL2 u₀ v₀ t ∈ dirichletLaplacianDomain ⊤
      ∧ dirichletLaplacianApply ⊤ (dAlembertL2 u₀ v₀ t) = -dAlembertL2Deriv2 u₀ v₀ t := by
  have hmem : dAlembertH1 u₀ v₀ t ∈ SobolevEuclideanZero 1 1 2 ⊤ := by
    rw [SobolevEuclideanZero.eq_top (by simp)]
    exact Submodule.mem_top
  have h := mem_dirichletLaplacianDomain_of_forall_ae_eq hmem (fun _ ↦ dAlembertH1Space u₀ v₀ t)
    fun i ↦ by
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [weakDeriv_dAlembertH1]
      exact EventuallyEq.rfl
  rw [fnL_dAlembertH1, Fin.sum_univ_one, weakDeriv_dAlembertH1Space] at h
  exact h

/-- d'Alembert's curve at $t = 0$ is $u_0$, read in $L^2(\mathbb{R})$. -/
theorem dAlembertL2_zero : dAlembertL2 u₀ v₀ 0 = fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀) := by
  unfold dAlembertL2
  simp only [neg_zero, translateCurve_zero, primitiveCurve_zero]
  module

/-- The time derivative of d'Alembert's curve at $t = 0$ is $v_0$, read in $L^2(\mathbb{R})$. -/
theorem dAlembertL2Deriv_zero : dAlembertL2Deriv u₀ v₀ 0 = fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀ := by
  unfold dAlembertL2Deriv
  simp only [neg_zero, translateCurve_zero]
  module

/-- **d'Alembert's formula solves the wave equation on $\mathbb{R}$.** For $u_0 \in H^2(\mathbb{R})$
and $v_0 \in H^1(\mathbb{R})$, d'Alembert's curve
$$u(t) = \frac12 (\tau_t u_0 + \tau_{-t} u_0) + \frac12 \int_{-t}^{t} \tau_s v_0 \, ds$$
in $L^2(\mathbb{R})$ is a solution of the wave equation on $\Omega = \mathbb{R}$ with data
$(u_0, v_0)$, in the class (31) of Theorem 10.7. This is Remark 8 of [brezis2011functional],
§10.3, (40).

The datum $u_0$ is read in $H^1_0(\mathbb{R}) = H^1(\mathbb{R})$ through `Wave.toZeroTopL`, and
$v_0$ in $L^2(\mathbb{R})$. The curve is the $L^2$ class of $x \mapsto \frac12 (u_0(x + t) +
u_0(x - t)) + \frac12 \int_{x - t}^{x + t} v_0(s) \, ds$ (`Wave.coeFn_dAlembertL2`). It is $C^2$
into $L^2(\mathbb{R})$ and $C^1$ into $H^1_0(\mathbb{R}) = H^1(\mathbb{R})$ by the translation
calculus of `Numlib.Analysis.Sobolev.TranslationCurve`, and $u(t) \in D(-\Delta)$ with $-\Delta
u(t) = -u''(t) = -\frac12 (\tau_t u_0'' + \tau_{-t} u_0'') - \frac12 (\tau_t v_0' - \tau_{-t}
v_0')$. By uniqueness it is the solution of Theorem 10.7 (`Wave.IsSolution.eqOn_dAlembertL2`). -/
theorem isSolution_dAlembert :
    IsSolution ⊤ (toZeroTopL (by simp) (dAlembertU₀ u₀)) (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀)
      (dAlembertL2 u₀ v₀) where
  contDiffOn := (contDiff_dAlembertL2 u₀ v₀).contDiffOn
  contDiffOnThrough := ⟨fun t ↦ toZeroTopL (by simp) (dAlembertH1 u₀ v₀ t),
    ((toZeroTopL (N := 1) (p := 2) (by simp)).contDiff.comp
      (contDiff_dAlembertH1 u₀ v₀)).contDiffOn,
    fun t _ ↦ (fnL_dAlembertH1 u₀ v₀ t).symm⟩
  mem_domain t _ := (dAlembertL2_mem_dirichletLaplacianDomain u₀ v₀ t).1
  contDiffOnPowDomain := by
    rw [LinearPMap.contDiffOnPowDomain_iff dirichletLaplacian_isClosed]
    refine ⟨![dAlembertL2 u₀ v₀, fun t ↦ -dAlembertL2Deriv2 u₀ v₀ t], fun t _ ↦ rfl, ?_, ?_⟩
    · rw [Fin.forall_fin_two]
      exact ⟨contDiffOn_zero.2 (contDiff_dAlembertL2 u₀ v₀).continuous.continuousOn,
        contDiffOn_zero.2 (continuous_dAlembertL2Deriv2 u₀ v₀).neg.continuousOn⟩
    · intro t _ i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact ⟨(dAlembertL2_mem_dirichletLaplacianDomain u₀ v₀ t).1,
        (dAlembertL2_mem_dirichletLaplacianDomain u₀ v₀ t).2⟩
  eqn t ht := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
      (contDiff_dAlembertL2 u₀ v₀).contDiffAt ht, iteratedDeriv_succ, iteratedDeriv_one,
      dirichletLaplacian_apply, (dAlembertL2_mem_dirichletLaplacianDomain u₀ v₀ t).2, neg_neg]
    have e : deriv (dAlembertL2 u₀ v₀) = dAlembertL2Deriv u₀ v₀ :=
      funext fun t ↦ (hasDerivAt_dAlembertL2 u₀ v₀ t).deriv
    rw [e]
    exact (hasDerivAt_dAlembertL2Deriv u₀ v₀ t).deriv
  apply_zero := dAlembertL2_zero u₀ v₀
  derivWithin_zero := by
    rw [(hasDerivAt_dAlembertL2 u₀ v₀ 0).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 0
      self_mem_Ici)]
    exact dAlembertL2Deriv_zero u₀ v₀

/-- **Uniqueness on $\mathbb{R}$.** Let $u_0 \in H^2(\mathbb{R})$ and $v_0 \in H^1(\mathbb{R})$.
Every solution of the wave equation on $\mathbb{R}$ with data $(u_0, v_0)$ is d'Alembert's curve
on $[0, \infty)$. This is Remark 8 of [brezis2011functional], §10.3.

The proof is `Wave.IsSolution.unique` with `Wave.isSolution_dAlembert`. -/
theorem IsSolution.eqOn_dAlembertL2 {u : ℝ → L2₁}
    (h : IsSolution ⊤ (toZeroTopL (by simp) (dAlembertU₀ u₀)) (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) u) :
    EqOn u (dAlembertL2 u₀ v₀) (Ici 0) :=
  h.unique (isSolution_dAlembert u₀ v₀)

/-- **d'Alembert's curve, pointwise.** For every $t$, $u(t)$ is the $L^2$ class of
$$x \mapsto \frac12 \bigl( u_0(x + te) + u_0(x - te) \bigr) + \frac12 \int_0^t \bigl( v_0(x +
  se) + v_0(x - se) \bigr) \, ds,$$
where $e$ is the unit vector of $\mathbb{R}^1$ and $u_0$, $v_0$ are the functions of the Sobolev
elements (`SobolevMultiIndex.fn`). -/
theorem coeFn_dAlembertL2 (t : ℝ) :
    dAlembertL2 u₀ v₀ t
      =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 1))) : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x ↦ (1 / 2 : ℝ) * (fn u₀ (x + t • 𝕖) + fn u₀ (x - t • 𝕖))
        + (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, (fn v₀ (x + s • 𝕖) + fn v₀ (x - s • 𝕖)) := by
  refine (Lp.coeFn_smul_add_add_smul (1 / 2 : ℝ)
    (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) t)
    (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) (-t))
    (primitiveCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) t)).trans ?_
  filter_upwards [coeFn_translateCurve 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) t,
    coeFn_translateCurve 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) (-t),
    coeFn_primitiveCurve 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) t] with x h1 h2 h3
  simp only [h1, h2, h3, neg_smul, ← sub_eq_add_neg]
  rfl

/-- The identification $\mathbb{R} \to \mathbb{R}^1$, $r \mapsto (r)$, where $\mathbb{R}^1$ is
`EuclideanSpace ℝ (Fin 1)`. -/
def lineEmbed (r : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 fun _ ↦ r

/-- The coordinate of $(r) \in \mathbb{R}^1$ is $r$. -/
@[simp]
theorem lineEmbed_apply (r : ℝ) (i : Fin 1) : lineEmbed r i = r := rfl

/-- Every point $x \in \mathbb{R}^1$ is $(x_0)$, the image of its coordinate under `Wave.lineEmbed`.
-/
theorem lineEmbed_coord (x : EuclideanSpace ℝ (Fin 1)) : lineEmbed (x 0) = x := by
  ext i
  rw [lineEmbed_apply, Subsingleton.elim i 0]

/-- For $x \in \mathbb{R}^1$ and $t \in \mathbb{R}$, $x + te = (x_0 + t)$, where $e$ is the unit
vector of $\mathbb{R}^1$. -/
theorem add_smul_single_eq_lineEmbed (x : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    x + t • 𝕖 = lineEmbed (x 0 + t) := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [lineEmbed]

/-- For $x \in \mathbb{R}^1$ and $t \in \mathbb{R}$, $x - te = (x_0 - t)$, where $e$ is the unit
vector of $\mathbb{R}^1$. -/
theorem sub_smul_single_eq_lineEmbed (x : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    x - t • 𝕖 = lineEmbed (x 0 - t) := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [lineEmbed]

/-- The map $r \mapsto (r)$ from $\mathbb{R}$ to $\mathbb{R}^1$ preserves Lebesgue measure. -/
theorem measurePreserving_lineEmbed : MeasurePreserving lineEmbed volume volume :=
  (PiLp.volume_preserving_toLp (Fin 1)).comp
    ((volume_preserving_funUnique (Fin 1) ℝ).symm (MeasurableEquiv.funUnique (Fin 1) ℝ))

/-- The map $r \mapsto (r)$ from $\mathbb{R}$ to $\mathbb{R}^1$ sends Lebesgue measure to Lebesgue
measure restricted to the whole space `⊤ : Opens ℝ¹`. -/
theorem measurePreserving_lineEmbed_top : MeasurePreserving lineEmbed volume
    (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 1))) : Set (EuclideanSpace ℝ (Fin 1)))) :=
  ⟨measurePreserving_lineEmbed.measurable, by
    rw [measurePreserving_lineEmbed.map_eq, Measure.restrict_coe_top]⟩

/-- For $w \in H^1(\mathbb{R}^1)$, the function $r \mapsto w((r))$ is integrable on every bounded
interval of $\mathbb{R}$. -/
theorem intervalIntegrable_comp_lineEmbed (w : SobolevEuclidean 1 1 2 ⊤) (a b : ℝ) :
    IntervalIntegrable (fun r ↦ fn w (lineEmbed r)) volume a b := by
  have h : MemLp (fun r ↦ fn w (lineEmbed r)) 2 (volume : Measure ℝ) :=
    (SobolevMultiIndex.memLp w).comp_measurePreserving measurePreserving_lineEmbed_top
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ι a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  exact intervalIntegrable_iff.2 ((h.restrict (Ι a b)).integrable one_le_two)

/-- Let $g : \mathbb{R} \to \mathbb{R}$ be integrable on every bounded interval. Then for all
$x_0, t \in \mathbb{R}$,
$$\int_0^t \bigl( g(x_0 + s) + g(x_0 - s) \bigr) \, ds = \int_{x_0 - t}^{x_0 + t} g(s) \, ds.$$
-/
theorem integral_add_sub_eq_integral_sub_add {g : ℝ → ℝ}
    (hg : ∀ a b, IntervalIntegrable g volume a b) (x₀ t : ℝ) :
    ∫ s in (0 : ℝ)..t, (g (x₀ + s) + g (x₀ - s)) = ∫ s in (x₀ - t)..(x₀ + t), g s := by
  have h1 : IntervalIntegrable (fun s ↦ g (x₀ + s)) volume 0 t := by
    have := (hg x₀ (x₀ + t)).comp_add_left x₀
    simpa using this
  have h2 : IntervalIntegrable (fun s ↦ g (x₀ - s)) volume 0 t := by
    have := (hg (x₀ - t) x₀).comp_sub_left x₀
    simpa using this.symm
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_comp_add_left g,
    intervalIntegral.integral_comp_sub_left g, add_zero, sub_zero, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hg _ _) (hg _ _)]

/-- **d'Alembert's curve is d'Alembert's formula (40).** For every $t$, $u(t)$ is the $L^2$ class of
$$x \mapsto \frac12 \bigl( u_0(x + t) + u_0(x - t) \bigr) + \frac12 \int_{x - t}^{x + t} v_0(s)
  \, ds,$$
that is, of `Wave.dAlembert` for the data read as functions on $\mathbb{R}$ through
`Wave.lineEmbed`, at the coordinate $x_0$ of $x \in \mathbb{R}^1$. -/
theorem coeFn_dAlembertL2_dAlembert (t : ℝ) :
    dAlembertL2 u₀ v₀ t
      =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 1))) : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x ↦ dAlembert (fun r ↦ fn u₀ (lineEmbed r)) (fun r ↦ fn v₀ (lineEmbed r)) t (x 0) := by
  refine (coeFn_dAlembertL2 u₀ v₀ t).trans (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [dAlembert_apply, add_smul_single_eq_lineEmbed, sub_smul_single_eq_lineEmbed]
  congr 2
  have e : ∀ s, fn v₀ (x + s • 𝕖) + fn v₀ (x - s • 𝕖)
      = fn v₀ (lineEmbed (x 0 + s)) + fn v₀ (lineEmbed (x 0 - s)) := fun s ↦ by
    rw [add_smul_single_eq_lineEmbed, sub_smul_single_eq_lineEmbed]
  simp only [e]
  exact integral_add_sub_eq_integral_sub_add (intervalIntegrable_comp_lineEmbed v₀) (x 0) t

end DAlembertSolution

end Wave
