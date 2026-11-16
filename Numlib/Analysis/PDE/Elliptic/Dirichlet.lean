/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.Holder
import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.Sobolev.Compactness
import Numlib.Analysis.Sobolev.Poincare
import Numlib.Analysis.Sobolev.Zero
import Numlib.Analysis.Normed.Operator.Riesz
import Numlib.Variational.EllipticInterval
import Numlib.Variational.Inequality.Basic

/-!
# Variational formulation of second-order elliptic boundary value problems

This file develops the weak theory of the Dirichlet and Neumann problems for second-order elliptic
equations on an open set $\Omega \subseteq \mathbb{R}^N$, following [brezis2011functional], §9.5.
The equations are $-\Delta u + u = f$ and the general equation $-\sum_{i,j} \partial_j (a_{ij}
\partial_i u) + \sum_i a_i \partial_i u + a_0 u = f$, with $f \in L^2(\Omega)$. The function spaces
are the Hilbert spaces $H^1(\Omega)$ and $H^1_0(\Omega)$ of `Numlib.Analysis.Sobolev.MultiIndex`.
For $u \in H^1(\Omega)$, $\partial_i u \in L^2(\Omega)$ is the weak partial derivative, $\|u\|_2$ is
the norm of $u$ in $L^2(\Omega)$, and $\|u\|$ is the norm of $H^1(\Omega)$, so that $\|u\|^2 =
\|u\|_2^2 + \sum_i \|\partial_i u\|_2^2$. The load of $f$ is the functional
$v \mapsto \int_\Omega f v$.

Every form of the file is a bounded bilinear form on $H^1(\Omega)$ that is a sum of pairings $(u, v)
\mapsto \langle T \partial^\alpha u, \partial^\beta v \rangle_{L^2(\Omega)}$, where $T$ is the
identity or the multiplication by a coefficient in $L^\infty(\Omega)$. The three forms are the
Dirichlet form $\int_\Omega \nabla u \cdot \nabla v$, the form $\int_\Omega \nabla u \cdot \nabla
v + \int_\Omega u v$ of $-\Delta + 1$, and the general form (41)
$$a(u, v) = \sum_{i,j} \int_\Omega a_{ij} \, \partial_i u \, \partial_j v + \sum_i \int_\Omega a_i
  \, \partial_i u \, v + \int_\Omega a_0 u v.$$
The form of $-\Delta + 1$ is the inner product of $H^1(\Omega)$, so its existence theorems are the
Riesz representation theorem and need no boundedness of $\Omega$. A weak solution of the Dirichlet
problem is a $u \in H^1_0(\Omega)$ with $a(u, v) = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$;
the Neumann problem has $H^1(\Omega)$ in place of $H^1_0(\Omega)$. The file proves existence and
uniqueness of weak solutions, Dirichlet's principle, the passage between classical and weak
solutions, and the Fredholm alternative for the general form.

## Main definitions

* `Elliptic.mulL`: the multiplication by a coefficient in $L^\infty(\Omega)$, as a bounded operator
  on $L^2(\Omega)$.
* `Elliptic.pairing`: the bilinear form $(u, v) \mapsto \langle T \partial^\alpha u, \partial^\beta
  v \rangle_{L^2(\Omega)}$ on $H^1(\Omega)$.
* `Elliptic.dirichletForm`: the Dirichlet form $\int_\Omega \nabla u \cdot \nabla v$.
* `Elliptic.laplaceForm`: the form $\int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v$ of
  $-\Delta + 1$.
* `Elliptic.load`: the functional $v \mapsto \int_\Omega f v$ on $H^1(\Omega)$.
* `Elliptic.admissibleSet`: the affine set $\{v \in H^1(\Omega) : v - \tilde g \in H^1_0(\Omega)\}$
  of the inhomogeneous Dirichlet problem.
* `Elliptic.IsUniformlyElliptic`: the ellipticity condition (36) for coefficients in
  $L^\infty(\Omega)$, almost everywhere on $\Omega$.
* `Elliptic.generalForm`: the general second-order form (41).
* `Elliptic.solutionOperator`: the solution operator $T \colon L^2(\Omega) \to L^2(\Omega)$ of the
  weak Dirichlet problem for a form that is coercive on $H^1_0(\Omega)$.
* `Elliptic.homogeneousKernel`: the space of weak solutions in $H^1_0(\Omega)$ of the homogeneous
  Dirichlet problem.

## Main results

* `Elliptic.laplaceForm_eq_innerSL`: the form of $-\Delta + 1$ is the inner product of
  $H^1(\Omega)$.
* `Elliptic.existsUnique_isGalerkinSolution_laplace`: the Dirichlet problem for $-\Delta u + u = f$
  has exactly one weak solution in $H^1_0(\Omega)$ (Theorem 9.21).
* `Elliptic.isMinOn_energy_iff_isGalerkinSolution_laplace`: the weak solution is the minimizer over
  $H^1_0(\Omega)$ of $\frac12 \int_\Omega (|\nabla v|^2 + v^2) - \int_\Omega f v$ (Dirichlet's
  principle, Theorem 9.21).
* `Elliptic.existsUnique_isWeakSolution_inhomogeneous`: the Dirichlet problem with the boundary
  values of $\tilde g \in H^1(\Omega)$ has exactly one weak solution in $\tilde g + H^1_0(\Omega)$
  (Proposition 9.22).
* `Elliptic.existsUnique_isGalerkinSolution_neumann`: the Neumann problem for $-\Delta u + u = f$
  has exactly one weak solution in $H^1(\Omega)$ (Proposition 9.24).
* `Elliptic.generalForm_garding`: Gårding's inequality for the general form, with an explicit shift.
* `Elliptic.existsUnique_isGalerkinSolution_general_of_nonneg`: on a bounded $\Omega$, with
  ellipticity, $a_i = 0$ and $a_0 \ge 0$, the Dirichlet problem for the general form has exactly one
  weak solution (Example 3).
* `Elliptic.isGalerkinSolution_laplace_of_classical`: a classical solution of the Dirichlet problem
  for $-\Delta u + u = f$ is a weak solution (Example 1, Step A).
* `Elliptic.exists_sobolev_forall_laplaceForm_eq_load_of_classical`: the interior half of Step A,
  without the boundary condition, as used by Example 2.
* `Elliptic.laplacian_ae_eq_of_isGalerkinSolution`: a weak solution that is $C^2$ in $\Omega$
  satisfies $-\Delta u + u = f$ almost everywhere (Example 1, Step D).
* `Elliptic.isGalerkinSolution_general_of_classical`: a classical solution of the Dirichlet problem
  for the general equation is a weak solution (Example 3, Step A).
* `Elliptic.solutionOperator_isCompactOperator`: the solution operator is compact when $\Omega$ has
  finite measure.
* `Elliptic.finiteDimensional_ker_general`: the homogeneous Dirichlet problem for the general form
  has a finite-dimensional space of weak solutions (Theorem 9.23, first half).
* `Elliptic.exists_orthogonality_iff_exists_solution`: the Dirichlet problem for the general form is
  solvable if and only if $f$ is orthogonal to a subspace of the same dimension (Theorem 9.23,
  second half).
* `Elliptic.existsUnique_of_ker_eq_bot`: if the homogeneous problem has only the zero solution,
  every problem has exactly one weak solution (Remark 23).

## Proof outline

The existence theorems apply the Lax–Milgram theorem on $H^1_0(\Omega)$ or on $H^1(\Omega)$. For the
general form on a bounded $\Omega$ with $a_i = 0$ and $a_0 \ge 0$, Poincaré's inequality gives
coercivity on $H^1_0(\Omega)$. For the Fredholm alternative, Gårding's inequality gives a $\lambda$
for which $a + \lambda \langle \cdot, \cdot \rangle_{L^2}$ is coercive on $H^1_0(\Omega)$. Its
solution operator $T$ is compact by the Rellich–Kondrachov theorem, and $u$ is a weak solution if
and only if $u = T(f + \lambda u)$, so the Riesz–Fredholm theory of the compact operator $T$ on
$L^2(\Omega)$ applies. A classical solution is a weak solution by integration by parts against test
functions and density of the test functions in $H^1_0(\Omega)$.

## Implementation notes

* A weak problem is `IsGalerkinSolution a (Elliptic.load Ω f) K u` of `Numlib.Variational.Galerkin`,
  with `K = SobolevEuclideanZero N 1 2 Ω` for the Dirichlet problem and `K = ⊤` for the Neumann
  problem. Nothing distinguishes the continuous problem from a Galerkin discretization.
* The space $H^1(\Omega)$ is `SobolevEuclidean N 1 2 Ω`, and its closed subspace $H^1_0(\Omega)$
  is `SobolevEuclideanZero N 1 2 Ω`.
* The weak derivative $\partial^\alpha u$ is `SobolevMultiIndex.weakDeriv u α`. The derivative
  $\partial_i u$ is the case `α = MultiIndexLE.single i`, and the case `α = 0` is the class of $u$
  in $L^2(\Omega)$, also written `SobolevMultiIndex.fn u` or `SobolevMultiIndex.fnL`.
* Coefficients are elements of `Lp ℝ ⊤ (volume.restrict Ω)`. The coefficients
  $a_{ij} \in C^1(\bar\Omega)$ and $a_0 \in C(\bar\Omega)$ of the source enter as $L^\infty$ classes
  on a bounded $\Omega$, and the ellipticity condition is stated almost everywhere.
* The Laplacian of a classical solution is Mathlib's $\Delta$ (`InnerProductSpace.instLaplacian`),
  computed in coordinates by `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`.
* The hypothesis $u \in C^2(\bar\Omega)$ on a classical solution is `ContDiffOnClosure ℝ 2 u Ω` of
  `Numlib.Analysis.Calculus.ContDiffOnClosure`: $u$ is $C^2$ on $\Omega$ and its derivatives of
  order at most $2$ extend continuously to $\bar\Omega$, as in footnote 16 of
  [brezis2011functional], §9.3. Where boundary values are read, `ContinuousOn u (closure Ω)` is
  assumed in addition. Mathlib's stronger `ContDiffOn ℝ 2 u (closure Ω)` implies both.
* Proposition 9.24 holds here for every open $\Omega$. The source assumes $\Omega$ bounded and of
  class $C^1$, which is needed only for the passage between the classical and the weak formulations.
* Theorem 9.23 and Remark 23 hold here for every open $\Omega$ of finite measure. The source assumes
  $\Omega$ bounded.
* The second clause of Remark 23, that $a_0 \ge 0$ alone forces the trivial kernel, is the general
  case of Proposition 9.29, which the source cites from Gilbarg and Trudinger. It is not proved
  here.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace Elliptic

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-! ### Multiplication by an $L^\infty$ coefficient, and the pairings -/

/-- Let $a \in L^\infty(\Omega)$. The **multiplication operator** of $a$ is the bounded linear
operator $f \mapsto a f$ on $L^2(\Omega)$.

It is Mathlib's Hölder product at the exponents $(2, \infty, 2)$, and the analogue on an open
subset of $\mathbb{R}^N$ of `EllipticInterval.mulL`. -/
def mulL (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
    2 ⊤ 2).flip a

/-- For $a \in L^\infty(\Omega)$ and $f \in L^2(\Omega)$, the class `Elliptic.mulL Ω a f` is the
pointwise product $x \mapsto a(x) f(x)$, almost everywhere on $\Omega$. -/
theorem coeFn_mulL (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    mulL Ω a f =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ a x * f x := by
  refine ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f a).trans (Eventually.of_forall fun x ↦ ?_)
  simp [mul_comm]

/-- For $a \in L^\infty(\Omega)$ and $f \in L^2(\Omega)$, $\|a f\|_2 \le \|a\|_\infty \|f\|_2$. -/
theorem norm_mulL_apply_le (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖mulL Ω a f‖ ≤ ‖a‖ * ‖f‖ := by
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le f a).trans ?_
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖f‖ * ‖a‖ ≤ 1 * ‖f‖ * ‖a‖ := by
        gcongr; exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = ‖a‖ * ‖f‖ := by ring

/-- For $a \in L^\infty(\Omega)$, the operator norm of the multiplication by $a$ on $L^2(\Omega)$ is
at most $\|a\|_\infty$. -/
theorem norm_mulL_le (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖mulL Ω a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_mulL_apply_le Ω a)

/-- For $a \in L^\infty(\Omega)$ and $f, g \in L^2(\Omega)$, $\langle a f, g \rangle_{L^2(\Omega)} =
\int_\Omega a f g$. -/
theorem inner_mulL_eq_integral (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⟪mulL Ω a f, g⟫_ℝ = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a x * f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ((coeFn_mulL Ω a f).mono fun x hx ↦ ?_)
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- For $a \in L^\infty(\Omega)$ and $f, g \in L^2(\Omega)$, the function $a f g$ is integrable on
$\Omega$. -/
theorem integrable_mul_mul (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Integrable (fun x ↦ a x * f x * g x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (mulL Ω a f) g).congr
    ((coeFn_mulL Ω a f).mono fun x hx ↦ ?_)
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- Let $T$ be a bounded linear operator on $L^2(\Omega)$, and let $\alpha, \beta$ be multi-indices
of order at most $1$. The **pairing** of $T$, $\alpha$ and $\beta$ is the bounded bilinear form
$$(u, v) \mapsto \langle T \partial^\alpha u, \partial^\beta v \rangle_{L^2(\Omega)}$$
on $H^1(\Omega)$. Every form of this module is a finite sum of pairings.

The weak derivatives enter through the continuous linear map `SobolevMultiIndex.weakDerivL`. The
forms of this module are assembled from pairings in the same way as `EllipticInterval.form` on
$H^1(a, b)$. -/
def pairing (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α β : MultiIndexLE (Fin N) 1) : SesqForm ℝ (SobolevEuclidean N 1 2 Ω) :=
  (((innerSL ℝ).comp (T.comp (SobolevMultiIndex.weakDerivL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume α))).flip.comp
      (SobolevMultiIndex.weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
        volume β)).flip

/-- For $u, v \in H^1(\Omega)$, the pairing of $T$, $\alpha$ and $\beta$ at $(u, v)$ is $\langle T
\partial^\alpha u, \partial^\beta v \rangle_{L^2(\Omega)}$. -/
theorem pairing_apply (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α β : MultiIndexLE (Fin N) 1) (u v : SobolevEuclidean N 1 2 Ω) :
    pairing Ω T α β u v
      = ⟪T (SobolevMultiIndex.weakDeriv u α), SobolevMultiIndex.weakDeriv v β⟫_ℝ :=
  rfl

/-- For $u, v \in H^1(\Omega)$, the pairing of $T$, $\alpha$ and $\beta$ satisfies $|\langle T
\partial^\alpha u, \partial^\beta v \rangle| \le \|T\| \, \|\partial^\alpha u\|_2 \,
\|\partial^\beta v\|_2$. -/
theorem abs_pairing_le (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α β : MultiIndexLE (Fin N) 1) (u v : SobolevEuclidean N 1 2 Ω) :
    |pairing Ω T α β u v|
      ≤ ‖T‖ * ‖SobolevMultiIndex.weakDeriv u α‖ * ‖SobolevMultiIndex.weakDeriv v β‖ := by
  rw [pairing_apply]
  exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact T.le_opNorm _)

/-- For $u, v \in H^1(\Omega)$, the pairing of $T$, $\alpha$ and $\beta$ satisfies $|\langle T
\partial^\alpha u, \partial^\beta v \rangle| \le \|T\| \, \|u\| \, \|v\|$, with the norm of
$H^1(\Omega)$. -/
theorem abs_pairing_le' (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α β : MultiIndexLE (Fin N) 1) (u v : SobolevEuclidean N 1 2 Ω) :
    |pairing Ω T α β u v| ≤ ‖T‖ * ‖u‖ * ‖v‖ :=
  (abs_pairing_le Ω T α β u v).trans (by
    gcongr
    · exact SobolevMultiIndex.norm_weakDeriv_le u α
    · exact SobolevMultiIndex.norm_weakDeriv_le v β)

/-- A pairing through the identity is symmetric: $\langle \partial^\alpha u, \partial^\beta v
\rangle_{L^2(\Omega)} = \langle \partial^\beta v, \partial^\alpha u \rangle_{L^2(\Omega)}$ for
$u, v \in H^1(\Omega)$. -/
theorem pairing_id_comm (α β : MultiIndexLE (Fin N) 1) (u v : SobolevEuclidean N 1 2 Ω) :
    pairing Ω (ContinuousLinearMap.id ℝ _) α β u v
      = pairing Ω (ContinuousLinearMap.id ℝ _) β α v u := by
  simp only [pairing_apply, ContinuousLinearMap.id_apply]
  exact real_inner_comm _ _

/-! ### The Dirichlet form and the form of $-\Delta + 1$ -/

/-- The **Dirichlet form** is the bilinear form on $H^1(\Omega)$
$$(u, v) \mapsto \int_\Omega \nabla u \cdot \nabla v = \sum_{i=1}^N \int_\Omega \partial_i u \,
  \partial_i v.$$
It is the scalar product of $H^1_0(\Omega)$ in Corollary 9.19 of [brezis2011functional], and it
appears in Theorem 9.31.

It is the sum over $i$ of the pairings through the identity with $\alpha = \beta = e_i$. -/
def dirichletForm : SesqForm ℝ (SobolevEuclidean N 1 2 Ω) :=
  ∑ i : Fin N,
    pairing Ω (ContinuousLinearMap.id ℝ _) (MultiIndexLE.single i) (MultiIndexLE.single i)

/-- For $u, v \in H^1(\Omega)$, the Dirichlet form is $\sum_i \langle \partial_i u, \partial_i v
\rangle_{L^2(\Omega)}$. -/
theorem dirichletForm_apply_inner (u v : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω u v = ∑ i : Fin N, ⟪SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i),
      SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)⟫_ℝ := by
  simp only [dirichletForm, sum_apply, pairing_apply,
    ContinuousLinearMap.id_apply]

/-- For $u, v \in H^1(\Omega)$, the Dirichlet form is the integral $\int_\Omega \sum_i \partial_i
u(x) \, \partial_i v(x) \, dx$. -/
theorem dirichletForm_apply (u v : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i : Fin N, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x := by
  rw [dirichletForm_apply_inner, integral_finsetSum Finset.univ fun i _ ↦ ?_]
  · exact Finset.sum_congr rfl fun i _ ↦ L2.inner_eq_integral_mul _ _
  · exact (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i))
      (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))).congr
      (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])

/-- The Dirichlet form is symmetric. -/
theorem dirichletForm_isHermitian : (dirichletForm Ω).IsHermitian := fun u v ↦ by
  rw [dirichletForm_apply_inner, dirichletForm_apply_inner, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _

/-- The Dirichlet form is additive in its first argument: its value at $(u + v, w)$ is the sum of
its values at $(u, w)$ and $(v, w)$. -/
theorem dirichletForm_add_left (u v w : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω (u + v) w = dirichletForm Ω u w + dirichletForm Ω v w :=
  ContinuousLinearMap.map_add₂ _ u v w

/-- The Dirichlet form is homogeneous in its first argument: its value at $(c u, w)$ is $c$ times
its value at $(u, w)$. -/
theorem dirichletForm_smul_left (c : ℝ) (u w : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω (c • u) w = c * dirichletForm Ω u w := by
  rw [map_smulₛₗ, smul_apply, smul_eq_mul, conj_trivial]

/-- For $v \in H^1(\Omega)$, the Dirichlet form at $(v, v)$ is $\int_\Omega |\nabla v|^2 = \sum_i
\|\partial_i v\|_2^2$. -/
theorem dirichletForm_self_eq (v : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω v v
      = ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2 := by
  rw [dirichletForm_apply_inner]
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_self_eq_norm_sq _

/-- For $v \in H^1(\Omega)$, the gradient norm is $\|\nabla v\|_2 = \sqrt{\sum_i \|\partial_i
v\|_2^2}$.

The gradient norm is `SobolevMultiIndex.gradNorm` at $p = 2$. -/
theorem gradNorm_eq_sqrt (v : SobolevEuclidean N 1 2 Ω) :
    SobolevMultiIndex.gradNorm v
      = √(∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2) := by
  rw [SobolevMultiIndex.gradNorm_eq_sum (p := 2) (by norm_num), Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

/-- For $v \in H^1(\Omega)$, the squared norm of $H^1(\Omega)$ is $\|v\|^2 = \|v\|_2^2 + \sum_i
\|\partial_i v\|_2^2$. -/
theorem norm_sq_eq (v : SobolevEuclidean N 1 2 Ω) :
    ‖v‖ ^ 2 = ‖SobolevMultiIndex.weakDeriv v 0‖ ^ 2
      + ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2 := by
  rw [SobolevMultiIndex.norm_eq_sum (p := 2) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun α _ ↦ sq_nonneg _),
    MultiIndexLE.sum_univ_one]

/-- For $v \in H^1(\Omega)$, the Dirichlet form at $(v, v)$ is $\|\nabla v\|_2^2$, the square of the
gradient norm `SobolevMultiIndex.gradNorm` of `Numlib.Analysis.Sobolev.MultiIndex`. -/
theorem dirichletForm_self_eq_gradNorm_sq (v : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω v v = SobolevMultiIndex.gradNorm v ^ 2 := by
  rw [dirichletForm_self_eq, gradNorm_eq_sqrt,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]

/-- The Dirichlet form is positive: $\int_\Omega |\nabla v|^2 \ge 0$ for $v \in H^1(\Omega)$. -/
theorem dirichletForm_self_nonneg (v : SobolevEuclidean N 1 2 Ω) : 0 ≤ dirichletForm Ω v v := by
  rw [dirichletForm_self_eq]
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _

/-- For $v \in H^1(\Omega)$, $\int_\Omega |\nabla v|^2 \le \|v\|^2$, because
$\|v\|^2 = \|v\|_2^2 + \int_\Omega |\nabla v|^2$. -/
theorem dirichletForm_self_le (v : SobolevEuclidean N 1 2 Ω) : dirichletForm Ω v v ≤ ‖v‖ ^ 2 := by
  rw [dirichletForm_self_eq, norm_sq_eq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The Dirichlet form is bounded by the gradient norms: for $u, v \in H^1(\Omega)$,
$$\left| \int_\Omega \nabla u \cdot \nabla v \right| \le \|\nabla u\|_2 \, \|\nabla v\|_2.$$

The proof is the Cauchy–Schwarz inequality in $L^2(\Omega)$ and in $\mathbb{R}^N$. -/
theorem abs_dirichletForm_le (u v : SobolevEuclidean N 1 2 Ω) :
    |dirichletForm Ω u v| ≤ SobolevMultiIndex.gradNorm u * SobolevMultiIndex.gradNorm v := by
  rw [dirichletForm_apply_inner, gradNorm_eq_sqrt, gradNorm_eq_sqrt]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦ abs_real_inner_le_norm _ _).trans ?_
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The Dirichlet form is bounded with constant $1$: $\left| \int_\Omega \nabla u \cdot \nabla v
\right| \le \|u\| \, \|v\|$ for $u, v \in H^1(\Omega)$, because the gradient norm is bounded by
the norm of $H^1(\Omega)$. -/
theorem dirichletForm_isBoundedWith : (dirichletForm Ω).IsBoundedWith 1 := fun u v ↦ by
  rw [Real.norm_eq_abs, one_mul]
  refine (abs_dirichletForm_le Ω u v).trans ?_
  gcongr
  · exact SobolevMultiIndex.gradNorm_nonneg _
  · exact SobolevMultiIndex.gradNorm_le_norm u
  · exact SobolevMultiIndex.gradNorm_le_norm v

section Poincare

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Poincaré's inequality** for the Dirichlet form. Let $N = d + 1 \ge 1$, let $R \ge 0$, and let
$\Omega \subseteq B(0, R)$. Every $u \in H^1_0(\Omega)$ satisfies
$$\|u\|^2 \le (1 + (2R)^2) \int_\Omega |\nabla u|^2.$$

This is `SobolevEuclideanZero.norm_le_gradNorm` at $p = 2$. The coercivity of the Dirichlet form
on $H^1_0(\Omega)$, `Elliptic.dirichletForm_restrict_isCoerciveWith` of
`Numlib.Analysis.PDE.Elliptic.Spectral`, restates it. -/
theorem norm_sq_le_dirichletForm_self {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ‖u‖ ^ 2 ≤ (1 + (2 * R) ^ 2) * dirichletForm Ω u u := by
  have hP := SobolevEuclideanZero.norm_le_gradNorm (p := 2) (by norm_num) hR hΩ ⟨u, hu⟩
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow] at hP
  rw [dirichletForm_self_eq_gradNorm_sq]
  have hK : (0 : ℝ) ≤ 1 + (2 * R) ^ 2 := by positivity
  calc ‖u‖ ^ 2 ≤ (√(1 + (2 * R) ^ 2) * SobolevMultiIndex.gradNorm u) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hP 2
    _ = (1 + (2 * R) ^ 2) * SobolevMultiIndex.gradNorm u ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]

end Poincare

/-- The **form of $-\Delta + 1$** is the bilinear form on $H^1(\Omega)$
$$a(u, v) = \int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v.$$
It is the form of Theorem 9.21, Proposition 9.22, Proposition 9.24, Theorem 9.25, Theorem 9.27
and Corollary 9.28 of [brezis2011functional].

It is the Dirichlet form plus the pairing through the identity with $\alpha = \beta = 0$. -/
def laplaceForm : SesqForm ℝ (SobolevEuclidean N 1 2 Ω) :=
  dirichletForm Ω + pairing Ω (ContinuousLinearMap.id ℝ _) 0 0

/-- For $u, v \in H^1(\Omega)$, the form of $-\Delta + 1$ is $a(u, v) = \sum_i \langle \partial_i u,
\partial_i v \rangle_{L^2(\Omega)} + \langle u, v \rangle_{L^2(\Omega)}$. -/
theorem laplaceForm_apply_inner (u v : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω u v = (∑ i : Fin N, ⟪SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i),
      SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)⟫_ℝ)
      + ⟪SobolevMultiIndex.weakDeriv u 0, SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
  rw [laplaceForm, add_apply, add_apply,
    dirichletForm_apply_inner, pairing_apply, ContinuousLinearMap.id_apply]

/-- For $U, V \in H^1(\Omega)$, the form of $-\Delta + 1$ is the Dirichlet form plus
$\langle U, V \rangle_{L^2(\Omega)}$, with the classes in $L^2(\Omega)$ written through
`SobolevMultiIndex.fnL`. -/
theorem laplaceForm_apply_eq_dirichletForm_add (U V : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω U V = dirichletForm Ω U V
      + ⟪SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ := by
  rw [laplaceForm, add_apply, add_apply, pairing_apply, ContinuousLinearMap.id_apply]
  rfl

/-- For $u, v \in H^1(\Omega)$, the form of $-\Delta + 1$ is the Dirichlet form plus
$\langle u, v \rangle_{L^2(\Omega)}$, with the classes in $L^2(\Omega)$ written as the weak
derivatives of order $0$.

This is `Elliptic.laplaceForm_apply_eq_dirichletForm_add` in another spelling; the two spellings
are definitionally equal. -/
theorem laplaceForm_apply_eq_dirichletForm_add_weakDeriv (u v : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω u v = dirichletForm Ω u v
      + ⟪SobolevMultiIndex.weakDeriv u 0, SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
  rw [laplaceForm_apply_inner, dirichletForm_apply_inner]

/-- For $u, v \in H^1(\Omega)$, the form of $-\Delta + 1$ is the integral (32):
$$a(u, v) = \int_\Omega (\nabla u \cdot \nabla v + u v).$$
-/
theorem laplaceForm_apply (u v : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ((∑ i : Fin N, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
        + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x) := by
  rw [laplaceForm, add_apply, add_apply,
    dirichletForm_apply, pairing_apply, ContinuousLinearMap.id_apply, L2.inner_eq_integral_mul,
    ← integral_add]
  · rfl
  · exact integrable_finsetSum _ fun i _ ↦
      (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i))
        (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))).congr
        (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])
  · exact (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv u 0)
      (SobolevMultiIndex.weakDeriv v 0)).congr
      (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])

/-- The form of $-\Delta + 1$ is the inner product of $H^1(\Omega)$:
$a(u, v) = \langle u, v \rangle_{H^1(\Omega)}$ for all $u, v \in H^1(\Omega)$.

The equation is `Elliptic.laplaceForm Ω = innerSL ℝ`. The inner product of $H^1(\Omega)$ is the
sum of the inner products in $L^2(\Omega)$ of the components indexed by the multi-indices $0$
and $e_i$ (`MultiIndexLE.sum_univ_one`). For this reason the Lax–Milgram theorem for this form
is the Riesz representation theorem, and Theorem 9.21 and Proposition 9.24 need no boundedness
of $\Omega$. -/
theorem laplaceForm_eq_innerSL : laplaceForm Ω = innerSL ℝ := by
  ext u v
  rw [laplaceForm_apply_inner, innerSL_apply_apply, Submodule.coe_inner, PiLp.inner_apply,
    MultiIndexLE.sum_univ_one, add_comm]
  rfl

/-- For $u, v \in H^1(\Omega)$, the form of $-\Delta + 1$ is
$a(u, v) = \langle u, v \rangle_{H^1(\Omega)}$. -/
theorem laplaceForm_apply_eq_inner (u v : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω u v = ⟪u, v⟫_ℝ := by
  rw [laplaceForm_eq_innerSL]
  rfl

/-- The form of $-\Delta + 1$ is coercive with constant $1$: $\|v\|^2 \le a(v, v)$ for
$v \in H^1(\Omega)$, and in fact $a(v, v) = \|v\|^2$. -/
theorem laplaceForm_isCoerciveWith_one : (laplaceForm Ω).IsCoerciveWith 1 := by
  rw [laplaceForm_eq_innerSL]
  exact SesqForm.innerSL_isCoerciveWith

/-- The form of $-\Delta + 1$ is symmetric. -/
theorem laplaceForm_isHermitian : (laplaceForm Ω).IsHermitian := by
  rw [laplaceForm_eq_innerSL]
  exact SesqForm.innerSL_isHermitian

/-- The form of $-\Delta + 1$ is bounded with constant $1$: $|a(u, v)| \le \|u\| \, \|v\|$ for
$u, v \in H^1(\Omega)$. -/
theorem laplaceForm_isBoundedWith_one : (laplaceForm Ω).IsBoundedWith 1 := fun u v ↦ by
  rw [laplaceForm_apply_eq_inner, one_mul]
  exact norm_inner_le_norm u v

/-! ### The load functional -/

/-- Let $f \in L^2(\Omega)$. The **load functional** of $f$ is the bounded linear functional on
$H^1(\Omega)$
$$v \mapsto \int_\Omega f v = \langle f, v \rangle_{L^2(\Omega)}.$$

It is the analogue of `EllipticInterval.load`. -/
def load (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp
    (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)

/-- For $f \in L^2(\Omega)$ and $v \in H^1(\Omega)$, the load functional of $f$ at $v$ is the inner
product in $L^2(\Omega)$ of $f$ with the class of $v$. -/
theorem load_apply_inner (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) : load Ω f v = ⟪f, SobolevMultiIndex.weakDeriv v 0⟫_ℝ :=
  rfl

/-- For $f \in L^2(\Omega)$ and $v \in H^1(\Omega)$, the load functional of $f$ at $v$ is the
integral $\int_\Omega f v$. -/
theorem load_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) :
    load Ω f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x := by
  rw [load_apply_inner, L2.inner_eq_integral_mul]
  rfl

/-- For $f \in L^2(\Omega)$ and $v \in H^1(\Omega)$, $\left| \int_\Omega f v \right| \le \|f\|_2 \,
\|v\|_2$. -/
theorem abs_load_le (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) :
    |load Ω f v| ≤ ‖f‖ * ‖SobolevMultiIndex.weakDeriv v 0‖ := by
  rw [load_apply_inner]
  exact abs_real_inner_le_norm _ _

/-- For $f \in L^2(\Omega)$, the load functional of $f$ has norm at most $\|f\|_2$ on $H^1(\Omega)$.
-/
theorem norm_load_le (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖load Ω f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  rw [Real.norm_eq_abs]
  exact (abs_load_le Ω f v).trans (by gcongr; exact SobolevMultiIndex.norm_weakDeriv_le v 0)

/-- The load functional is additive in the datum: the load of $f + g$ at $v$ is the sum of the loads
of $f$ and $g$ at $v$. -/
theorem load_add (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) : load Ω (f + g) v = load Ω f v + load Ω g v := by
  simp only [load_apply_inner, inner_add_left]

/-- The load functional is homogeneous in the datum: the load of $c f$ at $v$ is $c$ times the load
of $f$ at $v$. -/
theorem load_smul (c : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) : load Ω (c • f) v = c * load Ω f v := by
  simp only [load_apply_inner, real_inner_smul_left]

/-- The load of $f - g$ at $v$ is the load of $f$ at $v$ minus the load of $g$ at $v$. -/
theorem load_sub (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) : load Ω (f - g) v = load Ω f v - load Ω g v := by
  simp only [load_apply_inner, inner_sub_left]

variable {Ω} in
/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$, let $V$ be a subspace of $H^1(\Omega)$, and
let $f \in L^2(\Omega)$. An element $u \in H^1(\Omega)$ is a **weak solution with test space
$V$** if
$$a(u, \varphi) = \int_\Omega f \varphi \quad \text{for all } \varphi \in V.$$
For $a$ the form of $-\Delta + 1$ and $V = H^1_0(\Omega)$, this is the weak Dirichlet problem
(34) for $-\Delta u + u = f$ of [brezis2011functional], §9.5. For $a$ the Dirichlet form, it is
the weak problem for $-\Delta u = f$.

The definition does not require $u \in V$. A boundary condition, if any, is a separate
hypothesis on $u$. -/
def IsWeakSolution (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
    (V : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) (u : SobolevEuclidean N 1 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop :=
  ∀ φ ∈ V, a u φ = load Ω f φ

variable {Ω} in
/-- `Elliptic.IsWeakSolution a V u f` holds if and only if $a(u, \varphi) = \int_\Omega f \varphi$
for every $\varphi \in V$. -/
theorem isWeakSolution_iff {a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω)}
    {V : Submodule ℝ (SobolevEuclidean N 1 2 Ω)} {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} :
    IsWeakSolution a V u f ↔ ∀ φ ∈ V, a u φ = load Ω f φ :=
  Iff.rfl

/-- Let $K$ be a subspace of $H^1(\Omega)$. The **restricted load map** of $K$ is the bounded linear
map from $L^2(\Omega)$ to the dual of $K$ that sends $f$ to the functional
$v \mapsto \int_\Omega f v$ on $K$.

It makes the solution map of the weak Dirichlet problem a continuous linear map of $f$. -/
def loadL (K : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ] (K →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ K
      (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ℝ).flip
    ((SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume).comp
      K.subtypeL)).comp (innerSL ℝ)

/-- For a subspace $K$ of $H^1(\Omega)$, $f \in L^2(\Omega)$ and $v \in K$, the restricted load map
of $K$ sends $f$ to the functional with value $\langle f, v \rangle_{L^2(\Omega)}$ at $v$. -/
theorem loadL_apply (K : Submodule ℝ (SobolevEuclidean N 1 2 Ω))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (v : K) :
    loadL Ω K f v = ⟪f, SobolevMultiIndex.weakDeriv (v : SobolevEuclidean N 1 2 Ω) 0⟫_ℝ :=
  rfl

/-- For a subspace $K$ of $H^1(\Omega)$ and $f \in L^2(\Omega)$, the restricted load map of $K$
sends $f$ to the restriction to $K$ of `Elliptic.load Ω f`. -/
theorem loadL_eq (K : Submodule ℝ (SobolevEuclidean N 1 2 Ω))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    loadL Ω K f = (load Ω f).comp K.subtypeL :=
  rfl


/-! ### Theorem 9.21 (Dirichlet's principle) and Proposition 9.24 (the Neumann problem) -/

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and let $f \in L^2(\Omega)$. There is exactly one
$u \in H^1_0(\Omega)$ with
$$\int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v = \int_\Omega f v \quad \text{for all }
  v \in H^1_0(\Omega).$$
This is the existence and uniqueness of the weak solution, in the weak formulation (32), of the
Dirichlet problem $-\Delta u + u = f$ in $\Omega$, $u = 0$ on $\partial\Omega$. It is **Theorem
9.21** of [brezis2011functional] (Dirichlet, Riemann, Poincaré, Hilbert).

The proof is the Lax–Milgram theorem on $H^1_0(\Omega)$ for the form of $-\Delta + 1$, which is
the inner product of $H^1(\Omega)$. No boundedness of $\Omega$ is needed; Example 5 (a) and (b)
of the source use this. -/
theorem existsUnique_isGalerkinSolution_laplace
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u :=
  IsGalerkinSolution.existsUnique one_pos (laplaceForm_isCoerciveWith_one Ω)

/-- The **stability estimate** for $-\Delta + 1$. Let $K$ be a subspace of $H^1(\Omega)$ and let
$f \in L^2(\Omega)$. If $u \in K$ and $a(u, v) = \int_\Omega f v$ for all $v \in K$, where $a$
is the form of $-\Delta + 1$, then $\|u\| \le \|f\|_2$.

The main case is $K = H^1_0(\Omega)$. The proof of Theorem 9.25 of [brezis2011functional] quotes
this estimate as "$\|u\|_{H^1} \le \|f\|_{L^2}$ by (48)". -/
theorem norm_le_of_isGalerkinSolution_laplace
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {K : Submodule ℝ (SobolevEuclidean N 1 2 Ω)} {u : SobolevEuclidean N 1 2 Ω}
    (hu : IsGalerkinSolution (laplaceForm Ω) (load Ω f) K u) : ‖u‖ ≤ ‖f‖ := by
  have hcoer : ((laplaceForm Ω).restrict K).IsCoerciveWith 1 := fun v ↦
    laplaceForm_isCoerciveWith_one Ω (v : SobolevEuclidean N 1 2 Ω)
  have h := ((laplaceForm Ω).restrict K).norm_le_of_forall_apply_eq ((load Ω f).comp K.subtypeL)
    one_pos hcoer (u := ⟨u, hu.1⟩) fun v ↦ hu.2 v v.2
  rw [div_one] at h
  calc ‖u‖ = ‖(⟨u, hu.1⟩ : K)‖ := rfl
    _ ≤ ‖(load Ω f).comp K.subtypeL‖ := h
    _ ≤ ‖load Ω f‖ * ‖K.subtypeL‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖f‖ * 1 :=
        mul_le_mul (norm_load_le Ω f) (Submodule.norm_subtypeL_le K) (norm_nonneg _)
          (norm_nonneg _)
    _ = ‖f‖ := mul_one _

/-- Let $f \in L^2(\Omega)$. For $v \in H^1(\Omega)$, the **energy** of the Dirichlet problem for
$-\Delta + 1$ with datum $f$ is
$$E(v) = \frac12 \int_\Omega (|\nabla v|^2 + v^2) - \int_\Omega f v.$$
This is the functional of Theorem 9.21 of [brezis2011functional].

The energy is `SesqForm.energy`, the function $v \mapsto \frac12 a(v, v) - \ell(v)$ for the form
of $-\Delta + 1$ and the load of $f$. -/
theorem energy_laplace_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) :
    (laplaceForm Ω).energy (load Ω f) v
      = (1 / 2 : ℝ) * (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          ((∑ i : Fin N, SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
            * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
            + SobolevMultiIndex.fn v x * SobolevMultiIndex.fn v x))
        - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x := by
  rw [SesqForm.energy, laplaceForm_apply, load_apply]
  simp only [RCLike.re_to_real]

/-- **Dirichlet's principle**. Let $f \in L^2(\Omega)$ and $u \in H^1_0(\Omega)$. Then $u$ minimizes
the energy $E(v) = \frac12 \int_\Omega (|\nabla v|^2 + v^2) - \int_\Omega f v$ over
$H^1_0(\Omega)$ if and only if $u$ is the weak solution of the Dirichlet problem for
$-\Delta + 1$ with datum $f$. This is the second half of Theorem 9.21 of [brezis2011functional].

The energy is computed by `Elliptic.energy_laplace_apply`. The form is symmetric and coercive,
so the statement is `SesqForm.isMinOn_energy_iff`. -/
theorem isMinOn_energy_iff_isGalerkinSolution_laplace
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω) :
    IsMinOn ((laplaceForm Ω).energy (load Ω f)) (SobolevEuclideanZero N 1 2 Ω) u
      ↔ IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u := by
  rw [SesqForm.isMinOn_energy_iff (load Ω f) (laplaceForm_isHermitian Ω) one_pos
    (laplaceForm_isCoerciveWith_one Ω) _ hu]
  exact ⟨fun h ↦ ⟨hu, h⟩, fun h ↦ h.2⟩

/-- The space $H^1(\Omega)$, as the top subspace of itself, is complete. It is the trial space of
the Neumann problem. -/
theorem completeSpace_top : CompleteSpace (⊤ : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) :=
  (isClosed_univ (X := SobolevEuclidean N 1 2 Ω)).completeSpace_coe

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and let $f \in L^2(\Omega)$. There is exactly one
$u \in H^1(\Omega)$ with
$$\int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v = \int_\Omega f v \quad \text{for all }
  v \in H^1(\Omega).$$
This is the existence and uniqueness of the weak solution, in the weak formulation (45), of the
homogeneous Neumann problem $-\Delta u + u = f$ in $\Omega$, $\partial u / \partial n = 0$ on
$\partial\Omega$. It is **Proposition 9.24** of [brezis2011functional].

The source assumes that $\Omega$ is bounded and of class $C^1$. This hypothesis is needed only
for the passage between the classical and the weak formulations (Green's formula), not for this
statement. Example 5 (a) and (c) of the source are the cases $\Omega = \mathbb{R}^N$ and
$\Omega = \mathbb{R}^N_+$. The proof is the Lax–Milgram theorem on $H^1(\Omega)$; since the form
is the inner product, it is the Riesz representation of the load. -/
theorem existsUnique_isGalerkinSolution_neumann
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, IsGalerkinSolution (laplaceForm Ω) (load Ω f) ⊤ u :=
  haveI := completeSpace_top Ω
  IsGalerkinSolution.existsUnique one_pos (laplaceForm_isCoerciveWith_one Ω)

/-- **Dirichlet's principle for the Neumann problem**. Let $f \in L^2(\Omega)$ and
$u \in H^1(\Omega)$. Then $u$ minimizes the energy $E(v) = \frac12 \int_\Omega (|\nabla v|^2 +
v^2) - \int_\Omega f v$ over $H^1(\Omega)$ if and only if $u$ is the weak solution of the
Neumann problem for $-\Delta + 1$ with datum $f$. This is part of Proposition 9.24 of
[brezis2011functional]. -/
theorem isMinOn_energy_iff_isGalerkinSolution_neumann
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (u : SobolevEuclidean N 1 2 Ω) :
    IsMinOn ((laplaceForm Ω).energy (load Ω f)) univ u
      ↔ IsGalerkinSolution (laplaceForm Ω) (load Ω f) ⊤ u := by
  have h := SesqForm.isMinOn_energy_iff (load Ω f) (laplaceForm_isHermitian Ω) one_pos
    (laplaceForm_isCoerciveWith_one Ω) ⊤ (Submodule.mem_top (x := u))
  rw [Submodule.top_coe] at h
  rw [h]
  exact ⟨fun h ↦ ⟨Submodule.mem_top, h⟩, fun h ↦ h.2⟩

/-! ### Proposition 9.22: inhomogeneous Dirichlet data -/

/-- Let $\tilde g \in H^1(\Omega)$. The **admissible set** of the inhomogeneous Dirichlet problem is
$$K = \{v \in H^1(\Omega) : v - \tilde g \in H^1_0(\Omega)\},$$
the set of functions of $H^1(\Omega)$ with the boundary values of $\tilde g$. This is the set
$K$ of Example 2 in §9.5 of [brezis2011functional]. -/
def admissibleSet (g : SobolevEuclidean N 1 2 Ω) : Set (SobolevEuclidean N 1 2 Ω) :=
  {v | v - g ∈ SobolevEuclideanZero N 1 2 Ω}

/-- An element $v \in H^1(\Omega)$ lies in the admissible set $K$ of $\tilde g$ if and only if
$v - \tilde g \in H^1_0(\Omega)$. -/
theorem mem_admissibleSet_iff {g v : SobolevEuclidean N 1 2 Ω} :
    v ∈ admissibleSet Ω g ↔ v - g ∈ SobolevEuclideanZero N 1 2 Ω :=
  Iff.rfl

/-- The function $\tilde g$ lies in its admissible set $K$. -/
theorem self_mem_admissibleSet (g : SobolevEuclidean N 1 2 Ω) : g ∈ admissibleSet Ω g := by
  rw [mem_admissibleSet_iff, sub_self]
  exact Submodule.zero_mem _

/-- The admissible set $K$ of $\tilde g$ is nonempty. -/
theorem admissibleSet_nonempty (g : SobolevEuclidean N 1 2 Ω) : (admissibleSet Ω g).Nonempty :=
  ⟨g, self_mem_admissibleSet Ω g⟩

/-- The admissible set $K$ of $\tilde g$ is closed in $H^1(\Omega)$, as the preimage of the closed
subspace $H^1_0(\Omega)$ under $v \mapsto v - \tilde g$. -/
theorem isClosed_admissibleSet (g : SobolevEuclidean N 1 2 Ω) : IsClosed (admissibleSet Ω g) :=
  SobolevMultiIndexZero.isClosed.preimage (continuous_id.sub continuous_const)

/-- The admissible set $K$ of $\tilde g$ is convex, as a translate of a subspace. -/
theorem convex_admissibleSet (g : SobolevEuclidean N 1 2 Ω) : Convex ℝ (admissibleSet Ω g) := by
  intro u hu v hv a b ha hb hab
  rw [mem_admissibleSet_iff] at hu hv ⊢
  have : a • u + b • v - g = a • (u - g) + b • (v - g) := by
    rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv)

/-- Let $\tilde g, \tilde g' \in H^1(\Omega)$ with $\tilde g - \tilde g' \in H^1_0(\Omega)$. Then
the admissible sets of $\tilde g$ and $\tilde g'$ are equal. So the admissible set depends only
on the boundary values of $\tilde g$: "$K$ is independent of the choice of $\tilde g$", Example
2 in §9.5 of [brezis2011functional].

When $\tilde g$ and $\tilde g'$ are continuous on $\bar\Omega$ and agree on $\partial\Omega$,
the condition $\tilde g - \tilde g' \in H^1_0(\Omega)$ is Theorem 9.17 of the source. -/
theorem admissibleSet_eq_of_sub_mem {g g' : SobolevEuclidean N 1 2 Ω}
    (h : g - g' ∈ SobolevEuclideanZero N 1 2 Ω) : admissibleSet Ω g = admissibleSet Ω g' := by
  ext v
  rw [mem_admissibleSet_iff, mem_admissibleSet_iff]
  constructor
  · intro hv
    have := Submodule.add_mem _ hv h
    rwa [sub_add_sub_cancel] at this
  · intro hv
    have := Submodule.sub_mem _ hv h
    rwa [sub_sub_sub_cancel_right] at this

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$, let $\ell$ be a bounded linear functional
on $H^1(\Omega)$, let $\tilde g \in H^1(\Omega)$, and let $u$ be in the admissible set $K$ of
$\tilde g$. Then
$$a(u, v) = \ell(v) \text{ for all } v \in H^1_0(\Omega) \iff \ell(v - u) \le a(u, v - u) \text{
  for all } v \in K.$$
So the weak formulation (34) of the inhomogeneous Dirichlet problem is equivalent to the
variational inequality (35), as in the proof of Proposition 9.22 of [brezis2011functional].

In one direction, the equality holds at $v - u \in H^1_0(\Omega)$. In the other direction,
$v = u \pm w$ with $w \in H^1_0(\Omega)$ gives (34). -/
theorem isWeakSolution_inhomogeneous_iff_forall_le (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
    (ℓ : SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ) {g u : SobolevEuclidean N 1 2 Ω}
    (hu : u ∈ admissibleSet Ω g) :
    (∀ v ∈ SobolevEuclideanZero N 1 2 Ω, a u v = ℓ v)
      ↔ ∀ v ∈ admissibleSet Ω g, ℓ (v - u) ≤ a u (v - u) := by
  rw [mem_admissibleSet_iff] at hu
  constructor
  · intro h v hv
    rw [mem_admissibleSet_iff] at hv
    have hvu : v - u ∈ SobolevEuclideanZero N 1 2 Ω := by
      have := Submodule.sub_mem _ hv hu
      rwa [sub_sub_sub_cancel_right] at this
    exact (h _ hvu).ge
  · intro h w hw
    have h1 := h (u + w) (by
      rw [mem_admissibleSet_iff, add_sub_right_comm]
      exact Submodule.add_mem _ hu hw)
    have h2 := h (u - w) (by
      rw [mem_admissibleSet_iff, sub_right_comm]
      exact Submodule.sub_mem _ hu hw)
    rw [add_sub_cancel_left] at h1
    rw [sub_sub_cancel_left, map_neg, map_neg, neg_le_neg_iff] at h2
    exact le_antisymm h2 h1

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $\tilde g \in H^1(\Omega)$ and let
$f \in L^2(\Omega)$. There is exactly one $u \in H^1(\Omega)$ with
$u - \tilde g \in H^1_0(\Omega)$ and
$$\int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v = \int_\Omega f v \quad \text{for all }
  v \in H^1_0(\Omega).$$
This is the existence and uniqueness of the weak solution, in the weak formulation (34), of the
Dirichlet problem with the inhomogeneous boundary condition of $\tilde g$. It is **Proposition
9.22** of [brezis2011functional].

The source argues through the variational inequality (35) and Stampacchia's theorem. The proof
here writes $u = \tilde g + w$, where $w \in H^1_0(\Omega)$ is the Galerkin solution for the
load $v \mapsto \int_\Omega f v - a(\tilde g, v)$, and uniqueness is the coercivity of the form
on the difference of two solutions, which lies in $H^1_0(\Omega)$. -/
theorem existsUnique_isWeakSolution_inhomogeneous (g : SobolevEuclidean N 1 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, u ∈ admissibleSet Ω g ∧
      ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u v = load Ω f v := by
  obtain ⟨w, ⟨hwK, hw⟩, -⟩ := IsGalerkinSolution.existsUnique (a := laplaceForm Ω)
    (ℓ := load Ω f - laplaceForm Ω g) (K := SobolevEuclideanZero N 1 2 Ω) one_pos
    (laplaceForm_isCoerciveWith_one Ω)
  refine ⟨g + w, ⟨?_, fun v hv ↦ ?_⟩, ?_⟩
  · rw [mem_admissibleSet_iff, add_sub_cancel_left]
    exact hwK
  · have e2 : laplaceForm Ω (g + w) = laplaceForm Ω g + laplaceForm Ω w := map_add _ _ _
    rw [e2, add_apply, hw v hv, sub_apply]
    ring
  · rintro u ⟨huK, hu⟩
    rw [mem_admissibleSet_iff] at huK
    have hdiff : u - (g + w) ∈ SobolevEuclideanZero N 1 2 Ω := by
      have := Submodule.sub_mem _ huK hwK
      rwa [sub_sub] at this
    have e1 : laplaceForm Ω (u - (g + w)) = laplaceForm Ω u - laplaceForm Ω (g + w) :=
      map_sub _ _ _
    have e2 : laplaceForm Ω (g + w) = laplaceForm Ω g + laplaceForm Ω w := map_add _ _ _
    have h0 : laplaceForm Ω (u - (g + w)) (u - (g + w)) = 0 := by
      rw [e1, sub_apply, hu _ hdiff, e2, add_apply, hw _ hdiff, sub_apply]
      ring
    rw [laplaceForm_apply_eq_inner, real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero,
      sub_eq_zero] at h0
    exact h0

/-- Let $f \in L^2(\Omega)$, let $\tilde g \in H^1(\Omega)$, and let $u$ be in the admissible set
$K$ of $\tilde g$. Then $u$ minimizes the energy $E(v) = \frac12 \int_\Omega (|\nabla v|^2 +
v^2) - \int_\Omega f v$ over $K$ if and only if $\int_\Omega \nabla u \cdot \nabla v +
\int_\Omega u v = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$. This is the minimization of
Proposition 9.22 of [brezis2011functional].

The proof applies `SesqForm.isMinOn_energy_iff_forall_le` on the convex set $K$ and the
equivalence of (34) and (35), `Elliptic.isWeakSolution_inhomogeneous_iff_forall_le`. -/
theorem isMinOn_energy_iff_isWeakSolution_inhomogeneous
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {g u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ admissibleSet Ω g) :
    IsMinOn ((laplaceForm Ω).energy (load Ω f)) (admissibleSet Ω g) u
      ↔ ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u v = load Ω f v := by
  rw [SesqForm.isMinOn_energy_iff_forall_le (laplaceForm_isHermitian Ω) (load Ω f) one_pos
    (laplaceForm_isCoerciveWith_one Ω) (convex_admissibleSet Ω g) hu,
    isWeakSolution_inhomogeneous_iff_forall_le Ω (laplaceForm Ω) (load Ω f) hu]


/-! ### The general second-order form (41) with $L^\infty$ coefficients -/

/-- Let $a_{ij} \in L^\infty(\Omega)$ for $i, j = 1, \dots, N$, and let $\alpha \in \mathbb{R}$. The
coefficients are **uniformly elliptic** with constant $\alpha$ if $\alpha > 0$ and, for almost
every $x \in \Omega$,
$$\sum_{i,j} a_{ij}(x) \xi_i \xi_j \ge \alpha |\xi|^2 \quad \text{for all } \xi \in
  \mathbb{R}^N.$$
This is the ellipticity condition (36) of Example 3 in §9.5 of [brezis2011functional].

The condition is stated almost everywhere because the coefficients are classes of functions. The
pointwise condition of the source implies it, by `Elliptic.isUniformlyElliptic_of_forall_mem`. -/
def IsUniformlyElliptic
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α : ℝ) : Prop :=
  0 < α ∧ ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    ∀ ξ : EuclideanSpace ℝ (Fin N), α * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j

/-- Let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$ for $i, j = 1, \dots, N$. The **general second-order
form** on $H^1(\Omega)$ is
$$a(u, v) = \sum_{i,j} \int_\Omega a_{ij} \, \partial_i u \, \partial_j v + \sum_i \int_\Omega
  a_i \, \partial_i u \, v + \int_\Omega a_0 u v.$$
This is the form (41) of [brezis2011functional], §9.5. The form (38) of the symmetric problem
(37) is the case $a_i = 0$.

The coefficient $a_{ij}$ is `A i j`, $a_i$ is `a₁ i`, and $a_0$ is `a₀`. The form is a sum of
pairings through `Elliptic.mulL`. -/
def generalForm
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    SesqForm ℝ (SobolevEuclidean N 1 2 Ω) :=
  (∑ i : Fin N, ∑ j : Fin N,
      pairing Ω (mulL Ω (A i j)) (MultiIndexLE.single i) (MultiIndexLE.single j))
    + (∑ i : Fin N, pairing Ω (mulL Ω (a₁ i)) (MultiIndexLE.single i) 0)
    + pairing Ω (mulL Ω a₀) 0 0

section GeneralForm

variable (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
  (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
  (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

/-- For $u, v \in H^1(\Omega)$, the general form is $a(u, v) = \sum_{i,j} \langle a_{ij} \partial_i
u, \partial_j v \rangle_{L^2} + \sum_i \langle a_i \partial_i u, v \rangle_{L^2} + \langle a_0
u, v \rangle_{L^2}$. -/
theorem generalForm_apply_inner (u v : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ a₀ u v
      = (∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (SobolevMultiIndex.weakDeriv u
          (MultiIndexLE.single i)), SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j)⟫_ℝ)
        + (∑ i : Fin N, ⟪mulL Ω (a₁ i) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)),
          SobolevMultiIndex.weakDeriv v 0⟫_ℝ)
        + ⟪mulL Ω a₀ (SobolevMultiIndex.weakDeriv u 0), SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
  simp only [generalForm, add_apply, sum_apply, pairing_apply]

/-- For $u, v \in H^1(\Omega)$, the general form is the integral (41):
$$a(u, v) = \int_\Omega \Bigl( \sum_{i,j} a_{ij} \, \partial_i u \, \partial_j v + \sum_i a_i \,
  \partial_i u \, v + a_0 u v \Bigr).$$
-/
theorem generalForm_apply (u v : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ a₀ u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ((∑ i : Fin N, ∑ j : Fin N, A i j x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
        + (∑ i : Fin N, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.fn v x)
        + a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x) := by
  have h1 : ∀ i j, Integrable (fun x ↦ A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦ integrable_mul_mul Ω _ _ _
  have h2 : ∀ i, Integrable (fun x ↦ a₁ i x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v 0 x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦ integrable_mul_mul Ω _ _ _
  have h3 : Integrable (fun x ↦ a₀ x * SobolevMultiIndex.weakDeriv u 0 x
      * SobolevMultiIndex.weakDeriv v 0 x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := integrable_mul_mul Ω _ _ _
  have e1 : ∀ i, ∑ j, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ j, A i j x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x := fun i ↦
    (integral_finsetSum _ fun j _ ↦ h1 i j).symm
  have e2 : ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ j, A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, ∑ j, A i j x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x :=
    (integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h1 i j).symm
  have e3 : ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a₁ i x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v 0 x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, a₁ i x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v 0 x :=
    (integral_finsetSum _ fun i _ ↦ h2 i).symm
  have e4 : (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, ∑ j, A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      + (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, a₁ i x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v 0 x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ((∑ i, ∑ j, A i j x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
        + ∑ i, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v 0 x) :=
    (integral_add (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h1 i j)
      (integrable_finsetSum _ fun i _ ↦ h2 i)).symm
  have e5 : (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ((∑ i, ∑ j, A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      + ∑ i, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v 0 x))
      + (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a₀ x * SobolevMultiIndex.weakDeriv u 0 x
        * SobolevMultiIndex.weakDeriv v 0 x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (((∑ i, ∑ j, A i j x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
        + ∑ i, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v 0 x)
        + a₀ x * SobolevMultiIndex.weakDeriv u 0 x * SobolevMultiIndex.weakDeriv v 0 x) :=
    (integral_add ((integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h1 i j).add
      (integrable_finsetSum _ fun i _ ↦ h2 i)) h3).symm
  rw [generalForm_apply_inner]
  simp only [inner_mulL_eq_integral]
  simp only [e1]
  rw [e2, e3, e4, e5]
  rfl

/-- For $u, v \in H^1(\Omega)$, the general form is the sum of three integrals, the left-hand side
of (40) in §9.5 of [brezis2011functional]:
$$a(u, v) = \int_\Omega \sum_{i,j} a_{ij} \, \partial_i u \, \partial_j v + \int_\Omega \sum_i
  a_i \, \partial_i u \, v + \int_\Omega a_0 u v.$$

Each integrand is integrable, as a product of a coefficient in $L^\infty(\Omega)$ and two
functions in $L^2(\Omega)$. `Elliptic.generalForm_apply` writes the same value as one integral. -/
theorem generalForm_apply_three (u v : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ a₀ u v
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, ∑ j, A i j x
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
        + (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, a₁ i x
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x * SobolevMultiIndex.fn v x)
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x := by
  have h1 : Integrable (fun x ↦ ∑ i, ∑ j, A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ integrable_mul_mul Ω _ _ _
  have h2 : Integrable (fun x ↦ ∑ i, a₁ i x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x * SobolevMultiIndex.fn v x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    integrable_finsetSum _ fun i _ ↦
      integrable_mul_mul Ω _ _ (SobolevMultiIndex.weakDeriv v 0)
  have h3 : Integrable (fun x ↦ a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    integrable_mul_mul Ω _ (SobolevMultiIndex.weakDeriv u 0) (SobolevMultiIndex.weakDeriv v 0)
  have h12 : Integrable (fun x ↦ (∑ i, ∑ j, A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      + ∑ i, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.fn v x) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    h1.add h2
  rw [generalForm_apply, integral_add h12 h3, integral_add h1 h2]

/-- For $u, v \in H^1(\Omega)$, the general form with $a_i = 0$ is
$$a(u, v) = \int_\Omega \sum_{i,j} a_{ij} \, \partial_i u \, \partial_j v + \int_\Omega a_0 u
  v.$$
This is the left-hand side of (78) in §9.7 of [brezis2011functional] with $a_i = 0$. -/
theorem generalForm_zero_drift_apply (u v : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A 0 a₀ u v
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, ∑ j, A i j x
          * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x := by
  rw [generalForm_apply_three]
  have hzero : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), ∀ i,
      ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) i :
        EuclideanSpace ℝ (Fin N) → ℝ) x = 0 := by
    filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))]
      with x hx i
    simpa only [Pi.zero_apply] using hx
  have e2 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) i :
        EuclideanSpace ℝ (Fin N) → ℝ) x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (0 : ℝ) :=
    integral_congr_ae (hzero.mono fun x hx ↦ by simp only [hx, zero_mul,
      Finset.sum_const_zero])
  rw [e2, integral_zero, add_zero]

/-- Let $a_{ij} \colon \mathbb{R}^N \to \mathbb{R}$ be functions and let $\alpha > 0$ with $\alpha
|\xi|^2 \le \sum_{i,j} a_{ij}(x) \xi_i \xi_j$ for every $x \in \Omega$ and every
$\xi \in \mathbb{R}^N$. If the classes $A_{ij} \in L^\infty(\Omega)$ agree with $a_{ij}$ almost
everywhere on $\Omega$, then the $A_{ij}$ are uniformly elliptic with constant $\alpha$. So the
pointwise ellipticity condition (36) of [brezis2011functional], §9.5, gives the condition almost
everywhere. -/
theorem isUniformlyElliptic_of_forall_mem {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    {α : ℝ} (hα : 0 < α)
    (h : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin N), α * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j)
    (hA : ∀ i j, (A i j : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a i j) :
    IsUniformlyElliptic Ω A α := by
  refine ⟨hα, ?_⟩
  have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ i j, (A i j : EuclideanSpace ℝ (Fin N) → ℝ) x = a i j x :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ hA i j
  filter_upwards [hall, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ ξ
  simp only [hx]
  exact h x hxΩ ξ


/-- The general form is bounded with constant $M = \sum_{i,j} \|a_{ij}\|_\infty + \sum_i
\|a_i\|_\infty + \|a_0\|_\infty$: $|a(u, v)| \le M \|u\| \, \|v\|$ for $u, v \in H^1(\Omega)$. -/
theorem generalForm_isBoundedWith :
    (generalForm Ω A a₁ a₀).IsBoundedWith ((∑ i, ∑ j, ‖A i j‖) + ∑ i, ‖a₁ i‖ + ‖a₀‖) := by
  intro u v
  rw [Real.norm_eq_abs, generalForm_apply_inner]
  have key : ∀ (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      (α β : MultiIndexLE (Fin N) 1),
      |⟪mulL Ω a (SobolevMultiIndex.weakDeriv u α), SobolevMultiIndex.weakDeriv v β⟫_ℝ|
        ≤ ‖a‖ * ‖u‖ * ‖v‖ := fun a α β ↦ by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖mulL Ω a (SobolevMultiIndex.weakDeriv u α)‖ * ‖SobolevMultiIndex.weakDeriv v β‖
        ≤ ‖a‖ * ‖SobolevMultiIndex.weakDeriv u α‖ * ‖SobolevMultiIndex.weakDeriv v β‖ := by
          gcongr; exact norm_mulL_apply_le Ω a _
      _ ≤ ‖a‖ * ‖u‖ * ‖v‖ := by
          gcongr
          · exact SobolevMultiIndex.norm_weakDeriv_le u α
          · exact SobolevMultiIndex.norm_weakDeriv_le v β
  calc |(∑ i, ∑ j, ⟪mulL Ω (A i j) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)),
          SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j)⟫_ℝ)
        + (∑ i, ⟪mulL Ω (a₁ i) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)),
          SobolevMultiIndex.weakDeriv v 0⟫_ℝ)
        + ⟪mulL Ω a₀ (SobolevMultiIndex.weakDeriv u 0), SobolevMultiIndex.weakDeriv v 0⟫_ℝ|
      ≤ (∑ i, ∑ j, ‖A i j‖ * ‖u‖ * ‖v‖) + (∑ i, ‖a₁ i‖ * ‖u‖ * ‖v‖) + ‖a₀‖ * ‖u‖ * ‖v‖ := by
        refine (abs_add_three _ _ _).trans (add_le_add (add_le_add ?_ ?_) (key _ _ _))
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ key _ _ _)
        · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ key _ _ _)
    _ = ((∑ i, ∑ j, ‖A i j‖) + ∑ i, ‖a₁ i‖ + ‖a₀‖) * ‖u‖ * ‖v‖ := by
        rw [add_mul, add_mul, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
          Finset.sum_mul]
        congr 2
        exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.sum_mul, Finset.sum_mul]

/-- The multiplication by the zero coefficient is the zero operator on $L^2(\Omega)$. -/
@[simp]
theorem mulL_zero : mulL Ω 0 = 0 := map_zero _

/-- A pairing through the zero operator is the zero form. -/
@[simp]
theorem pairing_zero (α β : MultiIndexLE (Fin N) 1) : pairing Ω 0 α β = 0 :=
  ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun v ↦ by
    rw [pairing_apply]
    simp

/-- If $a_{ij} = a_{ji}$ for all $i, j$, then the form (38), the general form with $a_i = 0$, is
symmetric. -/
theorem generalForm_isHermitian_of_symm (hA : ∀ i j, A i j = A j i) :
    (generalForm Ω A 0 a₀).IsHermitian := fun u v ↦ by
  rw [conj_trivial, generalForm_apply_inner, generalForm_apply_inner]
  simp only [Pi.zero_apply, mulL_zero, zero_apply, inner_zero_left,
    Finset.sum_const_zero, add_zero, inner_mulL_eq_integral]
  rw [Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hA i j]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  · exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

end GeneralForm



/-! ### Lax–Milgram on a subspace -/

/-- Let $V$ be a real inner product space, let $a$ be a bounded bilinear form on $V$, let $\ell$ be
a bounded linear functional on $V$, and let $K$ be a complete subspace of $V$. If $c > 0$ and
$c \|v\|^2 \le a(v, v)$ for all $v \in K$, then there is exactly one $u \in K$ with
$a(u, v) = \ell(v)$ for all $v \in K$.

This is the variant of `IsGalerkinSolution.existsUnique` whose coercivity hypothesis is on the
restriction `a.restrict K` of the form, not on the whole space. It covers a form that is
coercive on $H^1_0(\Omega)$ by Poincaré's inequality but not on $H^1(\Omega)$. Its natural place
is beside `IsGalerkinSolution.existsUnique` in `Numlib.Variational.Galerkin`. -/
theorem _root_.IsGalerkinSolution.existsUnique_of_restrict {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} {ℓ : V →L[ℝ] ℝ} {K : Submodule ℝ V} {c : ℝ}
    (hc : 0 < c) (ha : (a.restrict K).IsCoerciveWith c) [CompleteSpace K] :
    ∃! u, IsGalerkinSolution a ℓ K u := by
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram (a.restrict K) (ℓ.comp K.subtypeL) hc ha
  refine ⟨(w : V), ⟨w.2, fun v hv ↦ hw ⟨v, hv⟩⟩, ?_⟩
  rintro y ⟨hyK, hy⟩
  exact congrArg Subtype.val (hwu ⟨y, hyK⟩ fun z ↦ hy (z : V) z.2)

/-- **Dirichlet's principle on a subspace**. Let $V$ be a real inner product space, let $a$ be a
bounded bilinear form on $V$, let $\ell$ be a bounded linear functional on $V$, and let $K$ be a
subspace of $V$. Suppose that the restriction of $a$ to $K$ is symmetric and that
$c \|v\|^2 \le a(v, v)$ for all $v \in K$, with $c > 0$. Then $u \in K$ minimizes the energy
$v \mapsto \frac12 a(v, v) - \ell(v)$ over $K$ if and only if $a(u, v) = \ell(v)$ for all
$v \in K$.

This is the variant of `SesqForm.isMinOn_energy_iff` with its hypotheses on `a.restrict K`. Its
natural place is beside that lemma in `Numlib.Variational.LaxMilgram`. -/
theorem _root_.SesqForm.isMinOn_energy_iff_of_restrict {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} (ℓ : V →L[ℝ] ℝ) {K : Submodule ℝ V}
    (ha : (a.restrict K).IsHermitian) {c : ℝ} (hc : 0 < c)
    (hcoer : (a.restrict K).IsCoerciveWith c) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u v = ℓ v := by
  have key := SesqForm.isMinOn_energy_iff (K := ⊤) (ℓ.comp K.subtypeL) ha hc hcoer (u := ⟨u, hu⟩)
    Submodule.mem_top
  rw [Submodule.top_coe, isMinOn_iff] at key
  rw [isMinOn_iff]
  have he : ∀ w : K, (a.restrict K).energy (ℓ.comp K.subtypeL) w = a.energy ℓ (w : V) :=
    fun w ↦ rfl
  simp only [he] at key
  constructor
  · intro hmin v hv
    exact key.1 (fun w _ ↦ hmin w w.2) ⟨v, hv⟩ Submodule.mem_top
  · intro h w hw
    exact key.2 (fun v _ ↦ h v v.2) ⟨w, hw⟩ (mem_univ _)

/-! ### Ellipticity, Gårding's inequality and coercivity on $H^1_0(\Omega)$ -/

section Ellipticity

variable {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

/-- Let the coefficients $a_{ij}$ be uniformly elliptic with constant $\alpha$. Then the principal
part of the general form satisfies, for $v \in H^1(\Omega)$,
$$\sum_{i,j} \int_\Omega a_{ij} \, \partial_i v \, \partial_j v \ge \alpha \sum_i \|\partial_i
  v\|_2^2.$$

The proof applies the ellipticity condition to $\xi = \nabla v(x)$ under the integral. -/
theorem sum_inner_mulL_ge (hA : IsUniformlyElliptic Ω A α) (v : SobolevEuclidean N 1 2 Ω) :
    α * ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2
      ≤ ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (SobolevMultiIndex.weakDeriv v
        (MultiIndexLE.single i)), SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
  have hint : ∀ i j, Integrable (fun x ↦ A i j x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦ integrable_mul_mul Ω _ _ _
  have hsq : ∀ i, Integrable (fun x ↦ SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))
      (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))).congr
      (Eventually.of_forall fun x ↦ by simp [sq])
  simp only [inner_mulL_eq_integral]
  have e : ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ∑ i : Fin N, SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x := by
    rw [integral_finsetSum _ fun i _ ↦ hsq i]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [← real_inner_self_eq_norm_sq, L2.inner_eq_integral_mul]
  rw [e, ← integral_const_mul]
  simp only [← integral_finsetSum _ fun j _ ↦ hint _ j]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  refine integral_mono_ae ((integrable_finsetSum _ fun i _ ↦ hsq i).const_mul α)
    (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j) ?_
  filter_upwards [hA.2] with x hx
  have h := hx (WithLp.toLp 2 fun i ↦ SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  simpa [sq] using h

/-- Let the coefficients $a_{ij}$ be uniformly elliptic with constant $\alpha$. Then the general
form satisfies, for $v \in H^1(\Omega)$,
$$a(v, v) \ge \alpha \sum_i \|\partial_i v\|_2^2 - \Bigl( \sum_i \|a_i\|_\infty \|\partial_i
  v\|_2 \Bigr) \|v\|_2 - \|a_0\|_\infty \|v\|_2^2.$$
-/
theorem generalForm_self_ge (hA : IsUniformlyElliptic Ω A α) (v : SobolevEuclidean N 1 2 Ω) :
    α * (∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2)
      - (∑ i : Fin N, ‖a₁ i‖ * ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖)
        * ‖SobolevMultiIndex.weakDeriv v 0‖
      - ‖a₀‖ * ‖SobolevMultiIndex.weakDeriv v 0‖ ^ 2
      ≤ generalForm Ω A a₁ a₀ v v := by
  rw [generalForm_apply_inner]
  have h1 := sum_inner_mulL_ge Ω hA v
  have h2 : -((∑ i : Fin N, ‖a₁ i‖ * ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖)
      * ‖SobolevMultiIndex.weakDeriv v 0‖)
      ≤ ∑ i : Fin N, ⟪mulL Ω (a₁ i) (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)),
        SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    refine le_trans ?_ (neg_abs_le (⟪mulL Ω (a₁ i)
      (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)), SobolevMultiIndex.weakDeriv v 0⟫_ℝ))
    refine neg_le_neg ((abs_real_inner_le_norm _ _).trans ?_)
    exact mul_le_mul_of_nonneg_right (norm_mulL_apply_le Ω _ _)
      (norm_nonneg (SobolevMultiIndex.weakDeriv v 0))
  have h3 : -(‖a₀‖ * ‖SobolevMultiIndex.weakDeriv v 0‖ ^ 2)
      ≤ ⟪mulL Ω a₀ (SobolevMultiIndex.weakDeriv v 0), SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
    refine le_trans ?_ (neg_abs_le (⟪mulL Ω a₀ (SobolevMultiIndex.weakDeriv v 0),
      SobolevMultiIndex.weakDeriv v 0⟫_ℝ))
    refine neg_le_neg ((abs_real_inner_le_norm _ _).trans ?_)
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_mulL_apply_le Ω _ _) (norm_nonneg _)
  linarith

/-- **Gårding's inequality** for the general form (41). Let the coefficients $a_{ij}$ be uniformly
elliptic with constant $\alpha$, let $a_i, a_0 \in L^\infty(\Omega)$, and let
$$\lambda = \frac{\bigl( \sum_i \|a_i\|_\infty \bigr)^2}{2 \alpha} + \|a_0\|_\infty +
  \frac{\alpha}{2}.$$
Then the form $a(u, v) + \lambda \int_\Omega u v$ is coercive on $H^1(\Omega)$ with constant
$\alpha / 2$:
$$\frac{\alpha}{2} \|v\|^2 \le a(v, v) + \lambda \|v\|_2^2 \quad \text{for all } v \in
  H^1(\Omega).$$

This makes explicit the step "fix $\lambda > 0$ large enough that $a(u, v) + \lambda \int u v$
is coercive" of the proof of Theorem 9.23 of [brezis2011functional]. No Poincaré inequality and
no boundedness of $\Omega$ enter. The proof combines `Elliptic.generalForm_self_ge` with $c
\sqrt{D} \, \|v\|_2 \le \frac{\alpha}{2} D + \frac{c^2}{2 \alpha} \|v\|_2^2$, where
$D = \sum_i \|\partial_i v\|_2^2$. -/
theorem generalForm_garding (hA : IsUniformlyElliptic Ω A α) :
    (generalForm Ω A a₁ a₀ + ((∑ i, ‖a₁ i‖) ^ 2 / (2 * α) + ‖a₀‖ + α / 2)
      • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0).IsCoerciveWith (α / 2) := by
  intro v
  have hα : 0 < α := hA.1
  simp only [RCLike.re_to_real, add_apply, smul_apply, pairing_apply, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq, smul_eq_mul]
  rw [norm_sq_eq]
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      D = ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ i, ‖a₁ i‖ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ Finset.sum_nonneg fun i _ ↦ norm_nonneg (a₁ i)
  have hS : ∑ i : Fin N, ‖a₁ i‖ * ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖
      ≤ c * √D := by
    rw [hc, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.le_sqrt (norm_nonneg _) hD0, hD]
    exact Finset.single_le_sum (f := fun i ↦
      ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2) (fun i _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  have hge := generalForm_self_ge Ω (a₁ := a₁) (a₀ := a₀) hA v
  rw [← hD] at hge ⊢
  rw [← hc]
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ‖SobolevMultiIndex.weakDeriv v 0‖ := ⟨_, rfl⟩
  rw [← hw] at hge ⊢
  have hw0 : 0 ≤ w := hw ▸ norm_nonneg _
  have hsq : √D ^ 2 = D := Real.sq_sqrt hD0
  have key : c * √D * w ≤ α / 2 * D + c ^ 2 / (2 * α) * w ^ 2 := by
    have h2α : 0 < 2 * α := by positivity
    have e : c ^ 2 / (2 * α) * w ^ 2 = (c * w) ^ 2 / (2 * α) := by ring
    rw [e, ← sub_le_iff_le_add', le_div_iff₀ h2α]
    have hsq2 : α ^ 2 * √D ^ 2 = α ^ 2 * D := by rw [hsq]
    nlinarith [sq_nonneg (α * √D - c * w), hsq2]
  have hSw : (∑ i : Fin N, ‖a₁ i‖ * ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖) * w
      ≤ c * √D * w := mul_le_mul_of_nonneg_right hS hw0
  nlinarith

end Ellipticity

/-! ### Example 3: the symmetric problem on a bounded domain -/

section Example3

variable {d : ℕ} {Ω' : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {A : Fin (d + 1) → Fin (d + 1) →
    Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))} {α : ℝ}

/-- Let $N = d + 1 \ge 1$, let $R \ge 0$ and $\Omega \subseteq B(0, R)$, let the coefficients
$a_{ij}$ be uniformly elliptic with constant $\alpha$, and let $a_0 \ge 0$ almost everywhere.
Then the form (38), the general form with $a_i = 0$, is coercive on $H^1_0(\Omega)$ with
constant $\alpha / (1 + (2R)^2)$:
$$\frac{\alpha}{1 + (2R)^2} \|v\|^2 \le a(v, v) \quad \text{for all } v \in H^1_0(\Omega).$$
This is the coercivity of Example 3 in §9.5 of [brezis2011functional].

For $v \in H^1_0(\Omega)$, $a(v, v) \ge \alpha \sum_i \|\partial_i v\|_2^2 + \int_\Omega a_0 v^2
\ge \alpha \sum_i \|\partial_i v\|_2^2$, and Poincaré's inequality (Corollary 9.19 of the
source, `SobolevEuclideanZero.norm_le_gradNorm`) gives $\|v\|^2 \le (1 + (2R)^2) \sum_i
\|\partial_i v\|_2^2$. The coefficients $a_{ij} \in C^1(\bar\Omega)$ and $a_0 \in C(\bar\Omega)$
of the source enter as $L^\infty$ classes. -/
theorem generalForm_isCoerciveWith_of_nonneg {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) (hA : IsUniformlyElliptic Ω' A α)
    (ha₀ : 0 ≤ a₀) :
    ((generalForm Ω' A 0 a₀).restrict (SobolevEuclideanZero (d + 1) 1 2 Ω')).IsCoerciveWith
      (α / (1 + (2 * R) ^ 2)) := by
  intro v
  have hα : 0 < α := hA.1
  rw [RCLike.re_to_real, SesqForm.restrict_apply, generalForm_apply_inner, ← Submodule.norm_coe]
  simp only [Pi.zero_apply, mulL_zero, zero_apply, inner_zero_left, Finset.sum_const_zero, add_zero]
  have h1 := sum_inner_mulL_ge Ω' hA (v : SobolevEuclidean (d + 1) 1 2 Ω')
  have h2 : 0 ≤ ⟪mulL Ω' a₀ (SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω') 0),
      SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω') 0⟫_ℝ := by
    rw [inner_mulL_eq_integral]
    refine integral_nonneg_of_ae ?_
    filter_upwards [(Lp.coeFn_nonneg a₀).2 ha₀] with x hx
    rw [mul_assoc, ← sq]
    exact mul_nonneg hx (sq_nonneg _)
  have hP := SobolevEuclideanZero.norm_le_gradNorm (p := 2) (by norm_num) hR hΩ v
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow] at hP
  have hP2 : ‖(v : SobolevEuclidean (d + 1) 1 2 Ω')‖ ^ 2
      ≤ (1 + (2 * R) ^ 2) * ∑ i, ‖SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω')
        (MultiIndexLE.single i)‖ ^ 2 := by
    calc ‖(v : SobolevEuclidean (d + 1) 1 2 Ω')‖ ^ 2
        ≤ (√(1 + (2 * R) ^ 2)
          * SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 2 Ω')) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hP 2
      _ = (1 + (2 * R) ^ 2) * ∑ i, ‖SobolevMultiIndex.weakDeriv
          (v : SobolevEuclidean (d + 1) 1 2 Ω') (MultiIndexLE.single i)‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), gradNorm_eq_sqrt,
            Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]
  calc α / (1 + (2 * R) ^ 2) * ‖(v : SobolevEuclidean (d + 1) 1 2 Ω')‖ ^ 2
      ≤ α / (1 + (2 * R) ^ 2) * ((1 + (2 * R) ^ 2) * ∑ i, ‖SobolevMultiIndex.weakDeriv
          (v : SobolevEuclidean (d + 1) 1 2 Ω') (MultiIndexLE.single i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hP2 (by positivity)
    _ = α * ∑ i, ‖SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω')
          (MultiIndexLE.single i)‖ ^ 2 := by
        field_simp
    _ ≤ _ := by linarith

/-- Let $N = d + 1 \ge 1$, let $R \ge 0$ and $\Omega \subseteq B(0, R)$, let the coefficients
$a_{ij}$ be uniformly elliptic with constant $\alpha$, and let $a_0 \ge 0$ almost everywhere.
For every $f \in L^2(\Omega)$ there is exactly one $u \in H^1_0(\Omega)$ with
$$\sum_{i,j} \int_\Omega a_{ij} \, \partial_i u \, \partial_j v + \int_\Omega a_0 u v =
  \int_\Omega f v \quad \text{for all } v \in H^1_0(\Omega).$$
This is the existence and uniqueness of the weak solution of the symmetric problem (37) in
Example 3 of §9.5 of [brezis2011functional].

The proof is the Lax–Milgram theorem with the coercivity of
`Elliptic.generalForm_isCoerciveWith_of_nonneg`. As the source notes, existence needs no
symmetry of $a_{ij}$. -/
theorem existsUnique_isGalerkinSolution_general_of_nonneg {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) (hA : IsUniformlyElliptic Ω' A α)
    (ha₀ : 0 ≤ a₀) (f : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃! u, IsGalerkinSolution (generalForm Ω' A 0 a₀) (load Ω' f)
      (SobolevEuclideanZero (d + 1) 1 2 Ω') u := by
  have hc : 0 < α / (1 + (2 * R) ^ 2) := div_pos hA.1 (by positivity)
  have hcoer := generalForm_isCoerciveWith_of_nonneg hR hΩ hA ha₀
  exact IsGalerkinSolution.existsUnique_of_restrict (ℓ := load Ω' f) hc hcoer

/-- Let $N = d + 1 \ge 1$, let $R \ge 0$ and $\Omega \subseteq B(0, R)$, let the coefficients
$a_{ij}$ be uniformly elliptic with constant $\alpha$ and symmetric ($a_{ij} = a_{ji}$), let
$a_0 \ge 0$ almost everywhere, and let $f \in L^2(\Omega)$. Then $u \in H^1_0(\Omega)$ minimizes
$$v \mapsto \frac12 \int_\Omega \Bigl( \sum_{i,j} a_{ij} \, \partial_i v \, \partial_j v + a_0
  v^2 \Bigr) - \int_\Omega f v$$
over $H^1_0(\Omega)$ if and only if $u$ is the weak solution of the symmetric problem (37). This
is the minimization of Example 3 in §9.5 of [brezis2011functional].

The form is symmetric and coercive on $H^1_0(\Omega)$, and the proof applies
`SesqForm.isMinOn_energy_iff_of_restrict`. -/
theorem isMinOn_energy_iff_isGalerkinSolution_general_of_symm {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) (hA : IsUniformlyElliptic Ω' A α)
    (hsymm : ∀ i j, A i j = A j i) (ha₀ : 0 ≤ a₀)
    {f : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω'} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω') :
    IsMinOn ((generalForm Ω' A 0 a₀).energy (load Ω' f)) (SobolevEuclideanZero (d + 1) 1 2 Ω') u
      ↔ IsGalerkinSolution (generalForm Ω' A 0 a₀) (load Ω' f)
        (SobolevEuclideanZero (d + 1) 1 2 Ω') u := by
  have hcoer := generalForm_isCoerciveWith_of_nonneg hR hΩ hA ha₀
  have hherm := (generalForm_isHermitian_of_symm Ω' A a₀ hsymm).restrict
    (SobolevEuclideanZero (d + 1) 1 2 Ω')
  rw [SesqForm.isMinOn_energy_iff_of_restrict (load Ω' f) hherm (div_pos hA.1 (by positivity))
    hcoer hu]
  exact ⟨fun h ↦ ⟨hu, h⟩, fun h ↦ h.2⟩

end Example3


/-! ### The solution operator on $L^2(\Omega)$ -/

section SolutionOperator

/-- Let $V$ be a real inner product space. A bounded bilinear form $a$ on $V$ that is coercive in
the sense of `SesqForm.IsCoercive` (there is $c > 0$ with $c \|v\|^2 \le a(v, v)$ for all $v$)
is coercive in the sense of Mathlib's `IsCoercive`.

This connects the forms of this library to Mathlib's Lax–Milgram equivalence
`IsCoercive.continuousLinearEquivOfBilin`. -/
theorem _root_.SesqForm.IsCoercive.isCoercive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} (ha : a.IsCoercive) :
    IsCoercive (a : V →L[ℝ] V →L[ℝ] ℝ) :=
  let ⟨c, hc, h⟩ := ha
  ⟨c, hc, fun u ↦ by rw [mul_assoc, ← sq]; exact h u⟩

/-- Let $K$ be a real Hilbert space. The **Riesz representation** is the continuous linear
equivalence from the dual of $K$ to $K$ that sends $\ell$ to the unique $w \in K$ with
$\langle w, v \rangle = \ell(v)$ for all $v \in K$.

Mathlib's `InnerProductSpace.toDual` is conjugate-linear; over $\mathbb{R}$ the type ascription
makes its inverse a real continuous linear equivalence. -/
def rieszEquiv (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] :
    (K →L[ℝ] ℝ) ≃L[ℝ] K :=
  (InnerProductSpace.toDual ℝ K).symm.toContinuousLinearEquiv

/-- For a real Hilbert space $K$, a bounded linear functional $\ell$ on $K$ and $v \in K$, the Riesz
representative $w$ of $\ell$ satisfies $\langle w, v \rangle = \ell(v)$. -/
theorem inner_rieszEquiv_apply {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (ℓ : K →L[ℝ] ℝ) (v : K) : ⟪rieszEquiv K ℓ, v⟫_ℝ = ℓ v :=
  InnerProductSpace.toDual_symm_apply

variable (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
  (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ whose restriction to $H^1_0(\Omega)$ is
coercive. The **solution map** of $a$ is the bounded linear map $L^2(\Omega) \to H^1_0(\Omega)$
that sends $f$ to the unique $u \in H^1_0(\Omega)$ with
$$a(u, v) = \int_\Omega f v \quad \text{for all } v \in H^1_0(\Omega).$$

It is the Riesz representative of the restricted load, pulled back through Mathlib's Lax–Milgram
equivalence `IsCoercive.continuousLinearEquivOfBilin` of the restricted form. -/
def solutionMap : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
    SobolevEuclideanZero N 1 2 Ω :=
  (((IsCoercive.continuousLinearEquivOfBilin ha.isCoercive).symm :
      SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclideanZero N 1 2 Ω) ∘L
    (rieszEquiv (SobolevEuclideanZero N 1 2 Ω) :
      (SobolevEuclideanZero N 1 2 Ω →L[ℝ] ℝ) →L[ℝ] SobolevEuclideanZero N 1 2 Ω)) ∘L
    loadL Ω (SobolevEuclideanZero N 1 2 Ω)

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ whose restriction to $H^1_0(\Omega)$ is
coercive. The **solution operator** of $a$ is the bounded linear operator
$T \colon L^2(\Omega) \to L^2(\Omega)$ that sends $f$ to the class in $L^2(\Omega)$ of the
unique $u \in H^1_0(\Omega)$ with $a(u, v) = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$.
This is the operator $T$ of the proofs of Theorem 9.23 and Theorem 9.31 of
[brezis2011functional].

The element $u$ is the value of `Elliptic.solutionMap`. -/
def solutionOperator : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume ∘L
    solutionMap Ω a ha

/-- For $f \in L^2(\Omega)$, $T f$ is the class in $L^2(\Omega)$ of the value of the solution map at
$f$. -/
theorem solutionOperator_apply
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    solutionOperator Ω a ha f = SobolevMultiIndexZero.fnL ℝ _ 1 2 Ω volume (solutionMap Ω a ha f) :=
  rfl

/-- The solution map solves the weak problem: for $f \in L^2(\Omega)$ and $v \in H^1_0(\Omega)$, the
value $u$ of the solution map at $f$ satisfies $a(u, v) = \int_\Omega f v$. -/
theorem restrict_apply_solutionMap
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 2 Ω) :
    a.restrict (SobolevEuclideanZero N 1 2 Ω) (solutionMap Ω a ha f) v
      = loadL Ω (SobolevEuclideanZero N 1 2 Ω) f v := by
  have h := IsCoercive.continuousLinearEquivOfBilin_apply ha.isCoercive (solutionMap Ω a ha f) v
  rw [← h]
  simp only [solutionMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact inner_rieszEquiv_apply _ _

/-- For $f \in L^2(\Omega)$, the value $u$ of the solution map at $f$ is the Galerkin solution in
$H^1_0(\Omega)$: $u \in H^1_0(\Omega)$ and $a(u, v) = \int_\Omega f v$ for all
$v \in H^1_0(\Omega)$. -/
theorem isGalerkinSolution_solutionMap
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) (solutionMap Ω a ha f) :=
  ⟨(solutionMap Ω a ha f).2, fun v hv ↦ restrict_apply_solutionMap Ω a ha f ⟨v, hv⟩⟩

/-- Uniqueness: let $f \in L^2(\Omega)$. If $u \in H^1_0(\Omega)$ and $a(u, v) = \int_\Omega f v$
for all $v \in H^1_0(\Omega)$, then $u$ is the value of the solution map at $f$. -/
theorem eq_solutionMap_of_isGalerkinSolution
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω}
    (hu : IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) :
    u = solutionMap Ω a ha f := by
  obtain ⟨c, hc, hcoer⟩ := id ha
  obtain ⟨w, -, hw⟩ := IsGalerkinSolution.existsUnique_of_restrict (ℓ := load Ω f) hc hcoer
  rw [hw u hu, hw _ (isGalerkinSolution_solutionMap Ω a ha f)]

/-- Uniqueness for the solution operator: let $f \in L^2(\Omega)$. If $u \in H^1_0(\Omega)$ and
$a(u, v) = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$, then the class of $u$ in
$L^2(\Omega)$ is $T f$. -/
theorem solutionOperator_eq_of_isGalerkinSolution
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω}
    (hu : IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) :
    SobolevMultiIndex.fnL ℝ _ 1 2 Ω volume u = solutionOperator Ω a ha f := by
  rw [solutionOperator_apply, SobolevMultiIndexZero.fnL_eq,
    ← eq_solutionMap_of_isGalerkinSolution Ω a ha hu]

/-- For $f \in L^2(\Omega)$, there is $u \in H^1_0(\Omega)$ whose class in $L^2(\Omega)$ is $T f$
and with $a(u, v) = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$. -/
theorem solutionOperator_spec (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃ u ∈ SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndex.fnL ℝ _ 1 2 Ω volume u = solutionOperator Ω a ha f ∧
        ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, a u v = load Ω f v :=
  ⟨solutionMap Ω a ha f, (solutionMap Ω a ha f).2, rfl,
    (isGalerkinSolution_solutionMap Ω a ha f).2⟩

/-- The stability bound of the solution map: if $c > 0$ and $c \|v\|^2 \le a(v, v)$ for all
$v \in H^1_0(\Omega)$, then the value $u$ of the solution map at $f \in L^2(\Omega)$ satisfies
$\|u\| \le \|f\|_2 / c$. -/
theorem norm_solutionMap_le {c : ℝ} (hc : 0 < c)
    (hcoer : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoerciveWith c)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖solutionMap Ω a ha f‖ ≤ ‖f‖ / c := by
  have h := (a.restrict (SobolevEuclideanZero N 1 2 Ω)).norm_le_of_forall_apply_eq
    (loadL Ω (SobolevEuclideanZero N 1 2 Ω) f) hc hcoer (restrict_apply_solutionMap Ω a ha f)
  refine h.trans (div_le_div_of_nonneg_right ?_ hc.le)
  rw [loadL_eq]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖load Ω f‖ * ‖(SobolevEuclideanZero N 1 2 Ω).subtypeL‖ ≤ ‖f‖ * 1 :=
        mul_le_mul (norm_load_le Ω f) (Submodule.norm_subtypeL_le _) (norm_nonneg _)
          (norm_nonneg _)
    _ = ‖f‖ := mul_one _

/-- The stability bound of the solution operator: if $c > 0$ and $c \|v\|^2 \le a(v, v)$ for all
$v \in H^1_0(\Omega)$, then $\|T f\|_2 \le \|f\|_2 / c$ for $f \in L^2(\Omega)$. -/
theorem norm_solutionOperator_apply_le {c : ℝ} (hc : 0 < c)
    (hcoer : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoerciveWith c)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖solutionOperator Ω a ha f‖ ≤ ‖f‖ / c :=
  (SobolevMultiIndexZero.norm_fnL_apply_le _).trans (norm_solutionMap_le Ω a ha hc hcoer f)

end SolutionOperator


/-! ### Classical and weak solutions: Steps A and D of Example 1 -/

section Classical

open Laplacian

variable {u : EuclideanSpace ℝ (Fin N) → ℝ}

/-- For every function $u \colon \mathbb{R}^N \to \mathbb{R}$ and every $x \in \mathbb{R}^N$, the
Laplacian is the sum of second derivatives in the standard basis:
$\Delta u(x) = \sum_i D^2 u(x)(e_i, e_i)$.

No differentiability is assumed: both sides are $0$ where $u$ is not twice differentiable. This
is `Elliptic.laplacian_eq_sum_fderiv_fderiv` without the $C^2$ hypothesis, and with the inner
derivative left uncurried. -/
theorem _root_.EuclideanSpace.laplacian_eq_sum_fderiv_fderiv_single
    (u : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    Δ u x
      = ∑ i, fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin N) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- Let $u$ be $C^2$ on the open set $\Omega$. For $x \in \Omega$, $\Delta u(x) = \sum_i \partial_i
(\partial_i u)(x)$, where $\partial_i u(y) = D u(y) e_i$.

The proof uses `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis` and
`fderiv_clm_apply`. -/
theorem laplacian_eq_sum_fderiv_fderiv (hu : ContDiffOn ℝ 2 u Ω)
    {x : EuclideanSpace ℝ (Fin N)} (hx : x ∈ Ω) :
    Δ u x = ∑ i : Fin N, fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_of_isOpen Ω.isOpen (m := 1) le_rfl).differentiableOn one_ne_zero).differentiableAt
      (Ω.isOpen.mem_nhds hx)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin N) ℝ)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- If $u$ is $C^2$ on the open set $\Omega$, then $\Delta u$ is continuous on $\Omega$. -/
theorem continuousOn_laplacian (hu : ContDiffOn ℝ 2 u Ω) : ContinuousOn (Δ u) Ω := by
  refine ContinuousOn.congr (continuousOn_finsetSum Finset.univ fun i _ ↦ ?_)
    fun x hx ↦ laplacian_eq_sum_fderiv_fderiv Ω hu hx
  have hg : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) Ω :=
    (hu.fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply contDiffOn_const
  exact (hg.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply continuousOn_const

/-- Let $u$ be $C^1$ on $\Omega$, and let $U \in H^1(\Omega)$ have a function that agrees with $u$
almost everywhere on $\Omega$. Then the weak partial derivatives of $U$ are the classical ones:
$\partial_i U = D u(\cdot) e_i$ almost everywhere on $\Omega$. -/
theorem weakDeriv_single_ae_eq_fderiv_of_contDiffOn (hu : ContDiffOn ℝ 1 u Ω)
    {U : SobolevEuclidean N 1 2 Ω}
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    (i : Fin N) :
    (SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :=
  SobolevEuclidean.weakDeriv_single_ae_eq U hU (hu.hasWeakIteratedLineDerivOn_single Ω i)

/-- Let $u$ be $C^2$ on $\Omega$, let $U \in H^1(\Omega)$ have a function that agrees with $u$
almost everywhere on $\Omega$, and let $V \in H^1(\Omega)$ have a function that agrees almost
everywhere on $\Omega$ with a test function $\varphi$ on $\Omega$. Then the form $a$ of
$-\Delta + 1$ satisfies
$$a(U, V) = \int_\Omega (-\Delta u + u) \varphi.$$

The proof integrates the $C^1$ function $\partial_i u$ by parts against $\varphi$ and sums over
$i$, with `Elliptic.laplacian_eq_sum_fderiv_fderiv`. -/
theorem laplaceForm_eq_integral_of_contDiffOn (hu : ContDiffOn ℝ 2 u Ω)
    {U : SobolevEuclidean N 1 2 Ω}
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    {V : SobolevEuclidean N 1 2 Ω} {φ : 𝓓(Ω, ℝ)}
    (hV : SobolevMultiIndex.fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) :
    laplaceForm Ω U V = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * φ x := by
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hu1 : ContDiffOn ℝ 1 u Ω := hu.of_le (by norm_num)
  have hUd := weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hu1 hU
  have hVd := fun i ↦ SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hV i
  -- `∂ᵢu` is `C^1` on `Ω`, so its weak derivative along `e_i` is `∂ᵢ∂ᵢu`
  have hg : ∀ i : Fin N, ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) Ω :=
    fun i ↦ (hu.fderiv_of_isOpen hΩo le_rfl).clm_apply contDiffOn_const
  have hibp : ∀ i : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x
        * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) := by
    intro i
    have h := ((hg i).hasWeakIteratedLineDerivOn_single Ω i).integral_smul_eq φ
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one,
      neg_one_mul] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  -- integrability of the pieces
  have hI1 : ∀ i : Fin N, Integrable (fun x ↦ φ x
      * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦ by
    have := ((hg i).hasWeakIteratedLineDerivOn_single Ω i).integrable_smul_weakDeriv φ
    simp only [smul_eq_mul] at this
    exact this.integrableOn
  have hI0 : Integrable (fun x ↦ u x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    have := (hu1.continuousOn.locallyIntegrableOn (μ := volume) hΩm)
      |>.integrable_smul_left_of_tsupport_subset φ.contDiff.continuous φ.hasCompactSupport
        φ.tsupport_subset
    simp only [smul_eq_mul] at this
    exact this.integrableOn.congr_fun (fun x _ ↦ mul_comm _ _) hΩm
  -- the left-hand side as integrals of classical derivatives
  have e1 : ∀ i : Fin N, ⟪SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i),
      SobolevMultiIndex.weakDeriv V (MultiIndexLE.single i)⟫_ℝ
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    fun i ↦ by
      rw [L2.inner_eq_integral_mul]
      refine integral_congr_ae ((hUd i).mul ?_)
      rw [← EuclideanSpace.basisFun_toBasis_apply i]
      exact hVd i
  have e0 : ⟪SobolevMultiIndex.weakDeriv U 0, SobolevMultiIndex.weakDeriv V 0⟫_ℝ
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * φ x := by
    rw [L2.inner_eq_integral_mul]
    exact integral_congr_ae (hU.mul hV)
  -- the right-hand side, split
  have e2 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * φ x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (-(∑ i : Fin N, φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + u x * φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hΩm] with x hx
    rw [laplacian_eq_sum_fderiv_fderiv Ω hu hx, ← Finset.mul_sum]
    ring
  have e3 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (-(∑ i : Fin N, φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + u x * φ x)
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          -(∑ i : Fin N, φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1)))
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * φ x :=
    integral_add (integrable_finsetSum _ fun i _ ↦ hI1 i).neg hI0
  have e4 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        -(∑ i : Fin N, φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1))
      = ∑ i : Fin N, -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1) := by
    rw [integral_neg, integral_finsetSum _ fun i _ ↦ hI1 i, Finset.sum_neg_distrib]
  rw [laplaceForm_apply_inner, e2, e3, e4, e0]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [e1, hibp]

/-- **Integration by parts against a test function**. Let $u$ be $C^2$ on $\Omega$, let
$U \in H^1(\Omega)$ have a function that agrees with $u$ almost everywhere on $\Omega$, and let
$V \in H^1(\Omega)$ have a function that agrees almost everywhere on $\Omega$ with a test
function $\varphi$ on $\Omega$. Then
$$\int_\Omega \nabla U \cdot \nabla V = \int_\Omega (-\Delta u) \varphi.$$

The Dirichlet form is the form of $-\Delta + 1$ minus the product in $L^2(\Omega)$, so this
follows from `Elliptic.laplaceForm_eq_integral_of_contDiffOn`. -/
theorem dirichletForm_eq_integral_neg_laplacian_mul (hu : ContDiffOn ℝ 2 u Ω)
    {U : SobolevEuclidean N 1 2 Ω}
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    {V : SobolevEuclidean N 1 2 Ω} {φ : 𝓓(Ω, ℝ)}
    (hV : SobolevMultiIndex.fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) :
    dirichletForm Ω U V
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), -Δ u x * φ x := by
  have h1 := laplaceForm_eq_integral_of_contDiffOn Ω hu hU hV
  have h2 := laplaceForm_apply_eq_dirichletForm_add_weakDeriv Ω U V
  have h3 : ⟪SobolevMultiIndex.weakDeriv U 0, SobolevMultiIndex.weakDeriv V 0⟫_ℝ
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * φ x := by
    rw [L2.inner_eq_integral_mul]
    exact integral_congr_ae (hU.mul hV)
  have hI1 : Integrable (fun x ↦ -Δ u x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    integrable_mul_testFunction (continuousOn_laplacian Ω hu).neg φ
  have hI2 : Integrable (fun x ↦ u x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    integrable_mul_testFunction (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn φ
  have e : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * φ x
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), -Δ u x * φ x)
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * φ x := by
    rw [← integral_add hI1 hI2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  linarith

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and bounded, let $u \in C^2(\bar\Omega)$, and let
$f \colon \mathbb{R}^N \to \mathbb{R}$ be in $L^2(\Omega)$ with $-\Delta u + u = f$ at every
point of $\Omega$. Then there is $U \in H^1(\Omega)$ whose function agrees with $u$ almost
everywhere on $\Omega$ and with
$$\int_\Omega \nabla U \cdot \nabla v + \int_\Omega U v = \int_\Omega f v \quad \text{for all }
  v \in H^1_0(\Omega).$$
This is the interior half of Step A of Example 1 in §9.5 of [brezis2011functional].

No boundary condition enters. Example 2 of the source uses this ("as above, any classical
solution is a weak solution"), and the homogeneous problem adds $U \in H^1_0(\Omega)$ by Theorem
9.17 (`Elliptic.isGalerkinSolution_laplace_of_classical`). The hypothesis
$u \in C^2(\bar\Omega)$ is `ContDiffOnClosure ℝ 2 u Ω`, and the class of $f$ in $L^2(\Omega)$ is
`hf.toLp f`. In the proof, $u \in W^{1,2}(\Omega)$ with its classical gradient as weak gradient
(`ContDiffOnClosure.memSobolevMultiIndex_of_isBounded`); for a test function $v$ the identity is
$\int_\Omega (-\Delta u + u) v = \int_\Omega f v$
(`Elliptic.laplaceForm_eq_integral_of_contDiffOn`), and it extends to $H^1_0(\Omega)$ by density
(`SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions`). -/
theorem exists_sobolev_forall_laplaceForm_eq_load_of_classical
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 2 u Ω) {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ x ∈ Ω, -Δ u x + u x = f x) :
    ∃ U : SobolevEuclidean N 1 2 Ω,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u ∧
        ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω U v = load Ω (hf.toLp f) v := by
  have hΩm := Ω.isOpen.measurableSet
  have hu1 : ContDiffOnClosure ℝ 1 u Ω := hu.of_le (by norm_num)
  obtain ⟨U, hU⟩ := (hu1.memSobolevMultiIndex_of_isBounded Ω hΩ 2).exists_sobolevMultiIndex
  refine ⟨U, hU, SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions (laplaceForm Ω U).continuous
    (load Ω (hf.toLp f)).continuous ?_⟩
  rintro V ⟨φ, hV⟩
  rw [laplaceForm_eq_integral_of_contDiffOn Ω hu.contDiffOn hU hV, load_apply]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hΩm, hf.coeFn_toLp, hV] with x hx hfx hVx
  rw [heq x hx, hfx, hVx]

/-- **A classical solution is a weak solution**. Let $\Omega \subseteq \mathbb{R}^N$ be open and
bounded, let $u \in C^2(\bar\Omega)$ be continuous on $\bar\Omega$ with $u = 0$ on
$\partial\Omega$, and let $f \colon \mathbb{R}^N \to \mathbb{R}$ be in $L^2(\Omega)$ with
$-\Delta u + u = f$ at every point of $\Omega$. Then there is $U \in H^1_0(\Omega)$ whose
function agrees with $u$ almost everywhere on $\Omega$, and $U$ is the weak solution of the
Dirichlet problem for $-\Delta + 1$ with datum $f$. This is Step A of Example 1 in §9.5 of
[brezis2011functional].

The hypothesis $u \in C^2(\bar\Omega)$ is `ContDiffOnClosure ℝ 2 u Ω` (footnote 16 of §9.3 of
the source), and the continuity of $u$ on $\bar\Omega$ makes its boundary values meaningful.
Mathlib's `ContDiffOn ℝ 2 u (closure Ω)` gives both hypotheses (`ContDiffOn.contDiffOnClosure`,
`ContDiffOn.continuousOn`). The identity on $H^1_0(\Omega)$ is
`Elliptic.exists_sobolev_forall_laplaceForm_eq_load_of_classical`, and $U \in H^1_0(\Omega)$ by
Theorem 9.17 (i) ⇒ (ii) of the source, which holds for every open $\Omega$ (Remark 19). -/
theorem isGalerkinSolution_laplace_of_classical
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 2 u Ω)
    (huc : ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (h0 : EqOn u 0 (frontier Ω)) {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ x ∈ Ω, -Δ u x + u x = f x) :
    ∃ U ∈ SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u ∧
        IsGalerkinSolution (laplaceForm Ω) (load Ω (hf.toLp f)) (SobolevEuclideanZero N 1 2 Ω)
          U := by
  obtain ⟨U, hU, hUw⟩ := exists_sobolev_forall_laplaceForm_eq_load_of_classical Ω hΩ hu hf heq
  have hU0 : U ∈ SobolevEuclideanZero N 1 2 Ω :=
    SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier (by norm_num) U hU huc h0
  exact ⟨U, hU0, hU, hU0, hUw⟩

/-- Let $U \in H^1(\Omega)$ and $f \in L^2(\Omega)$ satisfy $\int_\Omega \nabla U \cdot \nabla V +
\int_\Omega U V = \int_\Omega f V$ for every $V$ in the image of the test functions in
$H^1(\Omega)$, and let the function of $U$ agree almost everywhere on $\Omega$ with a function
$u$ that is $C^2$ on $\Omega$. Then $-\Delta u + u = f$ almost everywhere on $\Omega$. This is
Step D of Example 1 in §9.5 of [brezis2011functional].

The weak identity reads $\int_\Omega (-\Delta u + u - f) v = 0$ for every test function $v$
(`Elliptic.laplaceForm_eq_integral_of_contDiffOn`). Corollary 4.24 of the source is Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
theorem laplacian_ae_eq_of_forall_testFunction {U : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hUw : ∀ V ∈ SobolevMultiIndex.testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume, laplaceForm Ω U V = load Ω f V)
    (hu : ContDiffOn ℝ 2 u Ω)
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) :
    (fun x ↦ -Δ u x + u x) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] f := by
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hloc : LocallyIntegrableOn (fun x ↦ -Δ u x + u x - f x) Ω volume := by
    refine (((continuousOn_laplacian Ω hu).neg.add
      (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn).locallyIntegrableOn hΩm).sub
      ((Lp.memLp f).locallyIntegrableOn (by norm_num))
  have key := hΩo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc
    fun g hg hgc hgs ↦ by
    set φ : 𝓓(Ω, ℝ) := ⟨g, hg, hgc, hgs⟩ with hφ
    obtain ⟨V, hVT, hV⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
      (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
    have h1 := hUw V hVT
    rw [laplaceForm_eq_integral_of_contDiffOn Ω hu hU hV, load_apply] at h1
    have hI1 : Integrable (fun x ↦ (-Δ u x + u x) * g x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      have := (((continuousOn_laplacian Ω hu).neg.add
        (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn).locallyIntegrableOn
          (μ := volume) hΩm)
        |>.integrable_smul_left_of_tsupport_subset hg.continuous hgc hgs
      simp only [smul_eq_mul] at this
      exact this.integrableOn.congr_fun (fun x _ ↦ mul_comm _ _) hΩm
    have hI2 : Integrable (fun x ↦ f x * g x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      have := ((Lp.memLp f).locallyIntegrableOn (by norm_num) (Ω := Ω))
        |>.integrable_smul_left_of_tsupport_subset hg.continuous hgc hgs
      simp only [smul_eq_mul] at this
      exact this.integrableOn.congr_fun (fun x _ ↦ mul_comm _ _) hΩm
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs h), zero_smul]]
    have e : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x • (-Δ u x + u x - f x)
        = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * g x)
          - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * g x := by
      rw [← integral_sub hI1 hI2]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    have h1' : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * g x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * g x := by
      have h2 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * φ x
          = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * φ x := by
        rw [h1]
        exact integral_congr_ae (hV.mono fun x hx ↦ by dsimp only; rw [hx])
      exact h2
    rw [e, h1', sub_self]
  filter_upwards [(ae_restrict_iff' hΩm).2 key] with x hx
  exact sub_eq_zero.1 hx

/-- Let $U$ be the weak solution in $H^1_0(\Omega)$ of the Dirichlet problem for $-\Delta + 1$ with
datum $f \in L^2(\Omega)$, and let the function of $U$ agree almost everywhere on $\Omega$ with
a function $u$ that is $C^2$ on $\Omega$. Then $-\Delta u + u = f$ almost everywhere on
$\Omega$. This is Step D of Example 1 in §9.5 of [brezis2011functional]. -/
theorem laplacian_ae_eq_of_isGalerkinSolution {U : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hUw : IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) U)
    (hu : ContDiffOn ℝ 2 u Ω)
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) :
    (fun x ↦ -Δ u x + u x) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] f :=
  laplacian_ae_eq_of_forall_testFunction Ω
    (fun V hV ↦ hUw.2 V (SobolevMultiIndexZero.testFunctions_le hV)) hu hU

/-- Let $U$ be the weak solution in $H^1_0(\Omega)$ of the Dirichlet problem for $-\Delta + 1$ with
datum $f \in L^2(\Omega)$, and let the function of $U$ agree almost everywhere on $\Omega$ with
a function $u$ that is $C^2$ on $\Omega$. If $f$ agrees almost everywhere on $\Omega$ with a
function $g$ that is continuous on $\Omega$, then $-\Delta u(x) + u(x) = g(x)$ for every
$x \in \Omega$.

Two functions that are continuous on the open set $\Omega$ and agree almost everywhere agree
everywhere (`MeasureTheory.Measure.eqOn_open_of_ae_eq`). The statement of Step D in the source,
"$-\Delta u + u = f$ everywhere on $\Omega$, since $u \in C^2(\Omega)$", presumes such a
continuous representative of $f$. -/
theorem laplacian_eq_of_isGalerkinSolution_of_continuousOn {U : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hUw : IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) U)
    (hu : ContDiffOn ℝ 2 u Ω)
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    {g : EuclideanSpace ℝ (Fin N) → ℝ} (hg : ContinuousOn g Ω)
    (hfg : (f : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g) :
    ∀ x ∈ Ω, -Δ u x + u x = g x :=
  Measure.eqOn_open_of_ae_eq ((laplacian_ae_eq_of_isGalerkinSolution Ω hUw hu hU).trans hfg)
    Ω.isOpen ((continuousOn_laplacian Ω hu).neg.add
      (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn) hg

/-! ### Step A of Example 3: a classical solution of the general equation is a weak solution -/

/-- Let $u$ be $C^2$ on $\Omega$, let $a_{ij}$ be $C^1$ on $\Omega$, and let
$b_i, c \colon \mathbb{R}^N \to \mathbb{R}$. Let the coefficients $A_{ij}$, $a_i$, $a_0$ in
$L^\infty(\Omega)$ agree almost everywhere on $\Omega$ with $a_{ij}$, $b_i$ and $c$. Let
$U \in H^1(\Omega)$ have a function that agrees with $u$ almost everywhere on $\Omega$, and let
$V \in H^1(\Omega)$ have a function that agrees almost everywhere on $\Omega$ with a test
function $\varphi$ on $\Omega$. Then the general form $a$ of the coefficients $A_{ij}$, $a_i$,
$a_0$ satisfies
$$a(U, V) = \int_\Omega \Bigl( -\sum_{i,j} \partial_j (a_{ij} \partial_i u) + \sum_i b_i \,
  \partial_i u + c u \Bigr) \varphi,$$
where $\partial_j (a_{ij} \partial_i u)(x) = D(a_{ij} \partial_i u)(x) e_j$.

The proof integrates the $C^1$ function $a_{ij} \partial_i u$ by parts against $\varphi$ along
$e_j$ (`ContDiffOn.hasWeakIteratedLineDerivOn_single`) for each pair $(i, j)$, and reads off the
terms of order one and zero almost everywhere. -/
theorem generalForm_eq_integral_of_contDiffOn (hu : ContDiffOn ℝ 2 u Ω)
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hA : ∀ i j, (A i j : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a i j)
    {b : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₁ : ∀ i, (a₁ i : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] b i)
    {c : EuclideanSpace ℝ (Fin N) → ℝ}
    {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₀ : (a₀ : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] c)
    {U : SobolevEuclidean N 1 2 Ω}
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    {V : SobolevEuclidean N 1 2 Ω} {φ : 𝓓(Ω, ℝ)}
    (hV : SobolevMultiIndex.fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) :
    generalForm Ω A a₁ a₀ U V = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (-(∑ i : Fin N, ∑ j : Fin N, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
        + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + c x * u x) * φ x := by
  have hΩo := Ω.isOpen
  have hu1 : ContDiffOn ℝ 1 u Ω := hu.of_le (by norm_num)
  have hUd := weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hu1 hU
  have hVd : ∀ j : Fin N,
      (SobolevMultiIndex.weakDeriv V (MultiIndexLE.single j) : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
          fun x ↦ fderiv ℝ φ x (EuclideanSpace.single j 1) := fun j ↦ by
    have h := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hV j
    rwa [EuclideanSpace.basisFun_toBasis_apply] at h
  -- `a_ij ∂ᵢu` is `C^1` on `Ω`, so its weak derivative along `e_j` is `∂ⱼ(a_ij ∂ᵢu)`
  have hg : ∀ i j : Fin N,
      ContDiffOn ℝ 1 (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) Ω :=
    fun i j ↦ (ha i j).mul ((hu.fderiv_of_isOpen hΩo le_rfl).clm_apply contDiffOn_const)
  have hibp : ∀ i j : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      a i j x * fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single j 1)
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x
        * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) := by
    intro i j
    have h := ((hg i j).hasWeakIteratedLineDerivOn_single Ω j).integral_smul_eq φ
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one,
      neg_one_mul] at h
    rw [← h]
    congr 1
    funext x
    ring
  -- integrability of the pieces
  have hI2 : ∀ i j : Fin N, Integrable (fun x ↦ φ x
      * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦ by
    have := ((hg i j).hasWeakIteratedLineDerivOn_single Ω j).integrable_smul_weakDeriv φ
    simp only [smul_eq_mul] at this
    exact this.integrableOn
  have hI1 : ∀ i : Fin N, Integrable (fun x ↦ b i x * fderiv ℝ u x (EuclideanSpace.single i 1)
      * φ x) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    (integrable_mul_mul Ω (a₁ i) (SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i))
      (SobolevMultiIndex.weakDeriv V 0)).congr (((ha₁ i).mul (hUd i)).mul hV)
  have hI0 : Integrable (fun x ↦ c x * u x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (integrable_mul_mul Ω a₀ (SobolevMultiIndex.weakDeriv U 0)
      (SobolevMultiIndex.weakDeriv V 0)).congr ((ha₀.mul hU).mul hV)
  -- the left-hand side as integrals of classical quantities
  have e2 : ∀ i j : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), A i j x
      * SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv V (MultiIndexLE.single j) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a i j x
        * fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single j 1) :=
    fun i j ↦ integral_congr_ae (((hA i j).mul (hUd i)).mul (hVd j))
  have e1 : ∀ i : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a₁ i x
      * SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv V 0 x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x :=
    fun i ↦ integral_congr_ae (((ha₁ i).mul (hUd i)).mul hV)
  have e0 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a₀ x
      * SobolevMultiIndex.weakDeriv U 0 x * SobolevMultiIndex.weakDeriv V 0 x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), c x * u x * φ x :=
    integral_congr_ae ((ha₀.mul hU).mul hV)
  -- the right-hand side, split
  have e3 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (-(∑ i : Fin N, ∑ j : Fin N, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
        + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + c x * u x) * φ x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (-(∑ i : Fin N, ∑ j : Fin N, φ x * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
          + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
          + c x * u x * φ x) := by
    congr 1
    funext x
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have e4 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (-(∑ i : Fin N, ∑ j : Fin N, φ x * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
          + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
          + c x * u x * φ x)
      = (∑ i : Fin N, ∑ j : Fin N, -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          φ x * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1))
        + (∑ i : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), c x * u x * φ x := by
    have hs2 : Integrable (fun x ↦ ∑ i : Fin N, ∑ j : Fin N, φ x
        * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hI2 i j
    have hs1 : Integrable (fun x ↦ ∑ i : Fin N,
        b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      integrable_finsetSum _ fun i _ ↦ hI1 i
    have h2n : Integrable (fun x ↦ -(∑ i : Fin N, ∑ j : Fin N, φ x
        * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1))) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      hs2.neg
    have h12 : Integrable (fun x ↦ -(∑ i : Fin N, ∑ j : Fin N, φ x
        * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1))
        + ∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := h2n.add hs1
    rw [integral_add h12 hI0, integral_add h2n hs1, integral_neg,
      integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hI2 i j,
      integral_finsetSum _ fun i _ ↦ hI1 i]
    simp only [Finset.sum_neg_distrib]
    congr 3
    exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hI2 i j
  rw [generalForm_apply_inner]
  simp only [inner_mulL_eq_integral]
  rw [e3, e4, e0]
  congr 2
  · exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [e2, hibp]
  · exact Finset.sum_congr rfl fun i _ ↦ e1 i

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and bounded, let $u \in C^2(\bar\Omega)$, let
$a_{ij}$ be $C^1$ on $\Omega$, and let $b_i, c \colon \mathbb{R}^N \to \mathbb{R}$. Let the
coefficients $A_{ij}$, $a_i$, $a_0$ in $L^\infty(\Omega)$ agree almost everywhere on $\Omega$
with $a_{ij}$, $b_i$ and $c$. Let $f \colon \mathbb{R}^N \to \mathbb{R}$ be in $L^2(\Omega)$
with
$$-\sum_{i,j} \partial_j (a_{ij} \partial_i u) + \sum_i b_i \, \partial_i u + c u = f$$
at every point of $\Omega$. Then there is $U \in H^1(\Omega)$ whose function agrees with $u$
almost everywhere on $\Omega$ and with $a(U, v) = \int_\Omega f v$ for every
$v \in H^1_0(\Omega)$, where $a$ is the general form (41) of $A_{ij}$, $a_i$, $a_0$. This is the
interior half of Step A of Example 3 in §9.5 of [brezis2011functional] ("as above, any classical
solution is a weak solution").

No boundary condition enters; the homogeneous Dirichlet problem adds $U \in H^1_0(\Omega)$ by
Theorem 9.17 (`Elliptic.isGalerkinSolution_general_of_classical`). The hypothesis
$u \in C^2(\bar\Omega)$ is `ContDiffOnClosure ℝ 2 u Ω`. In the proof, $u \in W^{1,2}(\Omega)$
(`ContDiffOnClosure.memSobolevMultiIndex_of_isBounded`); for a test function the identity is the
integration by parts `Elliptic.generalForm_eq_integral_of_contDiffOn`, and it extends to
$H^1_0(\Omega)$ by density (`SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions`). -/
theorem exists_sobolev_forall_generalForm_eq_load_of_classical
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 2 u Ω)
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hA : ∀ i j, (A i j : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a i j)
    {b : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₁ : ∀ i, (a₁ i : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] b i)
    {c : EuclideanSpace ℝ (Fin N) → ℝ}
    {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₀ : (a₀ : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] c)
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ x ∈ Ω, -(∑ i : Fin N, ∑ j : Fin N, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + c x * u x = f x) :
    ∃ U : SobolevEuclidean N 1 2 Ω,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u ∧
        ∀ v ∈ SobolevEuclideanZero N 1 2 Ω,
          generalForm Ω A a₁ a₀ U v = load Ω (hf.toLp f) v := by
  have hΩm := Ω.isOpen.measurableSet
  have hu1 : ContDiffOnClosure ℝ 1 u Ω := hu.of_le (by norm_num)
  obtain ⟨U, hU⟩ := (hu1.memSobolevMultiIndex_of_isBounded Ω hΩ 2).exists_sobolevMultiIndex
  refine ⟨U, hU, SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions
    (generalForm Ω A a₁ a₀ U).continuous (load Ω (hf.toLp f)).continuous ?_⟩
  rintro V ⟨φ, hV⟩
  rw [generalForm_eq_integral_of_contDiffOn Ω hu.contDiffOn ha hA ha₁ ha₀ hU hV, load_apply]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hΩm, hf.coeFn_toLp, hV] with x hx hfx hVx
  rw [heq x hx, hfx, hVx]

/-- **A classical solution of the general second-order equation is a weak solution**. Let
$\Omega \subseteq \mathbb{R}^N$ be open and bounded, let $u \in C^2(\bar\Omega)$ be continuous
on $\bar\Omega$ with $u = 0$ on $\partial\Omega$, let $a_{ij}$ be $C^1$ on $\Omega$, and let
$b_i, c \colon \mathbb{R}^N \to \mathbb{R}$. Let the coefficients $A_{ij}$, $a_i$, $a_0$ in
$L^\infty(\Omega)$ agree almost everywhere on $\Omega$ with $a_{ij}$, $b_i$ and $c$. Let
$f \colon \mathbb{R}^N \to \mathbb{R}$ be in $L^2(\Omega)$ with
$$-\sum_{i,j} \partial_j (a_{ij} \partial_i u) + \sum_i b_i \, \partial_i u + c u = f$$
at every point of $\Omega$. Then there is $U \in H^1_0(\Omega)$ whose function agrees with $u$
almost everywhere on $\Omega$, and $U$ is the weak solution of the Dirichlet problem for the
general form (41) of $A_{ij}$, $a_i$, $a_0$ with datum $f$. This is Step A of Example 3 in §9.5
of [brezis2011functional] ("as above, any classical solution is a weak solution").

The problem (37) of the source is the case $a_i = 0$ and $b_i = 0$, with
$a_{ij} \in C^1(\bar\Omega)$ and $a_0 \in C(\bar\Omega)$ supplying the $L^\infty$ classes. The
identity on $H^1_0(\Omega)$ is
`Elliptic.exists_sobolev_forall_generalForm_eq_load_of_classical`, and $U \in H^1_0(\Omega)$ by
Theorem 9.17 (i) ⇒ (ii) of the source, which needs no regularity of $\Omega$. -/
theorem isGalerkinSolution_general_of_classical
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 2 u Ω)
    (huc : ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (h0 : EqOn u 0 (frontier Ω))
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hA : ∀ i j, (A i j : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a i j)
    {b : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₁ : ∀ i, (a₁ i : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] b i)
    {c : EuclideanSpace ℝ (Fin N) → ℝ}
    {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₀ : (a₀ : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] c)
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ x ∈ Ω, -(∑ i : Fin N, ∑ j : Fin N, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + c x * u x = f x) :
    ∃ U ∈ SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u ∧
        IsGalerkinSolution (generalForm Ω A a₁ a₀) (load Ω (hf.toLp f))
          (SobolevEuclideanZero N 1 2 Ω) U := by
  obtain ⟨U, hU, hUw⟩ :=
    exists_sobolev_forall_generalForm_eq_load_of_classical Ω hΩ hu ha hA ha₁ ha₀ hf heq
  have hU0 : U ∈ SobolevEuclideanZero N 1 2 Ω :=
    SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier (by norm_num) U hU huc h0
  exact ⟨U, hU0, hU, hU0, hUw⟩

end Classical

/-! ### The weak Laplacian of an $H^2$ weak solution -/

section WeakLaplacian

variable {Ω}

/-- The standard basis of $\mathbb{R}^N$, as a local notation. -/
local notation "𝔅" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- Let $u \in H^2(\Omega)$, and let $V \in H^1(\Omega)$ have a function that agrees almost
everywhere on $\Omega$ with a test function $\varphi$ on $\Omega$. Then the form $a$ of
$-\Delta + 1$, at $u$ viewed in $H^1(\Omega)$, satisfies
$$a(u, V) = \int_\Omega (-\Delta_w u + u) \varphi,$$
where $\Delta_w u = \sum_i \partial_i (\partial_i u)$ is the weak Laplacian.

This is the analogue of `Elliptic.laplaceForm_eq_integral_of_contDiffOn` for $u \in H^2(\Omega)$
instead of $u \in C^2(\Omega)$. The space $H^2(\Omega)$ is `SobolevEuclidean N 2 2 Ω`, the
inclusion into $H^1(\Omega)$ is `SobolevMultiIndex.toLowerOrderL`, and
$\partial_i u \in H^1(\Omega)$ is `SobolevMultiIndex.partialDerivL`. The proof integrates
$\partial_i u \in H^1(\Omega)$ by parts against $\varphi$. -/
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

/-- Let $u \in H^2(\Omega)$ and $f \in L^2(\Omega)$. If $\int_\Omega \nabla u \cdot \nabla \varphi +
\int_\Omega u \varphi = \int_\Omega f \varphi$ for every $\varphi$ in the image of the test
functions in $H^1(\Omega)$, then
$$-\Delta_w u + u = f$$
almost everywhere on $\Omega$, where $\Delta_w u = \sum_i \partial_i (\partial_i u)$ is the weak
Laplacian.

The proof applies `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` to the residual, which
lies in $L^2(\Omega)$. -/
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

end WeakLaplacian

/-! ### The Fredholm alternative for a second-kind equation, abstractly -/

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- Let $X$ be a real inner product space, $T$ a bounded operator on $X$ and $\mu \in \mathbb{R}$.
Then $(1 \cdot I - \mu T) v = v - \mu T v$ for $v \in X$. -/
theorem one_smul_one_sub_smul_apply (T : X →L[ℝ] X) (μ : ℝ) (v : X) :
    ((1 : ℝ) • (1 : X →L[ℝ] X) - μ • T) v = v - μ • T v := by
  simp

/-- The **Fredholm alternative** for a solvability predicate. Let $X$ be a real Hilbert space, let
$K$ be a compact operator on $X$, let $\mu \neq 0$, and let $P$ be a property of elements of $X$
such that $P(f)$ holds if and only if $f$ is in the range of $\mu I - K$. Then there is a
finite-dimensional subspace $F$ of $X$ with $\dim F = \dim \ker (\mu I - K)$ such that, for
every $f \in X$,
$$P(f) \iff \langle f, v \rangle = 0 \text{ for all } v \in F.$$

The subspace is $F = \ker (\mu I - K^*)$, by
`IsCompactOperator.range_smul_sub_eq_orthogonal_ker_adjoint` and
`IsCompactOperator.finrank_ker_eq_finrank_ker_adjoint`. This is Theorem 6.6 (b) and (d) of
[brezis2011functional], in Hilbert space. -/
theorem exists_finiteDimensional_forall_iff_inner_eq_zero {K : X →L[ℝ] X}
    (hK : IsCompactOperator K) {μ : ℝ} (hμ : μ ≠ 0) {P : X → Prop}
    (hP : ∀ f, P f ↔ f ∈ (μ • (1 : X →L[ℝ] X) - K).range) :
    ∃ F : Submodule ℝ X, FiniteDimensional ℝ F ∧
      finrank ℝ F = finrank ℝ (μ • (1 : X →L[ℝ] X) - K).ker ∧
        ∀ f, P f ↔ ∀ v ∈ F, ⟪f, v⟫_ℝ = 0 := by
  refine ⟨((starRingEnd ℝ) μ • (1 : X →L[ℝ] X) - ContinuousLinearMap.adjoint K).ker, ?_, ?_,
    fun f ↦ ?_⟩
  · have h1 := hK.adjoint.finiteDimensional_ker_pow
      (by simpa using hμ : (starRingEnd ℝ) μ ≠ 0) 1
    rwa [pow_one] at h1
  · exact (hK.finrank_ker_eq_finrank_ker_adjoint hμ).symm
  · rw [hP, hK.range_smul_sub_eq_orthogonal_ker_adjoint hμ, Submodule.mem_orthogonal]
    exact forall₂_congr fun v _ ↦ by rw [real_inner_comm]

/-- The **Fredholm alternative**, existence from uniqueness. Let $X$ be a real Hilbert space, let
$K$ be a compact operator on $X$, and let $\mu \neq 0$. If $\ker (\mu I - K) = \{0\}$, then
$\mu I - K$ is surjective.

This is `IsCompactOperator.injective_iff_surjective_smul_one_sub`. -/
theorem surjective_smul_one_sub_of_ker_eq_bot {K : X →L[ℝ] X} (hK : IsCompactOperator K) {μ : ℝ}
    (hμ : μ ≠ 0) (h : (μ • (1 : X →L[ℝ] X) - K).ker = ⊥) :
    Function.Surjective (μ • (1 : X →L[ℝ] X) - K) :=
  (hK.injective_iff_surjective_smul_one_sub hμ).1 (LinearMap.ker_eq_bot.1 h)

end Abstract

/-! ### Theorem 9.23: the Fredholm alternative for (40), modulo compactness of $T$ -/

section Fredholm

variable (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$. The **space of homogeneous solutions** of
$a$ is the subspace of $H^1(\Omega)$
$$N = \{u \in H^1_0(\Omega) : a(u, v) = 0 \text{ for all } v \in H^1_0(\Omega)\}.$$
This is the space $N$ of solutions of (40) with $f = 0$ in Theorem 9.23 of
[brezis2011functional]. -/
def homogeneousKernel : Submodule ℝ (SobolevEuclidean N 1 2 Ω) where
  carrier := {u | u ∈ SobolevEuclideanZero N 1 2 Ω ∧
    ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, a u v = 0}
  zero_mem' := ⟨zero_mem _, fun v _ ↦ by simp⟩
  add_mem' {u w} hu hw := ⟨add_mem hu.1 hw.1, fun v hv ↦ by
    have e : a (u + w) = a u + a w := map_add _ _ _
    rw [e, add_apply, hu.2 v hv, hw.2 v hv, add_zero]⟩
  smul_mem' c u hu := ⟨Submodule.smul_mem _ c hu.1, fun v hv ↦ by
    have e : a (c • u) = c • a u := by rw [map_smulₛₗ, conj_trivial]
    rw [e, smul_apply, hu.2 v hv, smul_zero]⟩

/-- An element $u \in H^1(\Omega)$ lies in the space $N$ of homogeneous solutions of $a$ if and only
if $u \in H^1_0(\Omega)$ and $a(u, v) = 0$ for all $v \in H^1_0(\Omega)$. -/
theorem mem_homogeneousKernel_iff {u : SobolevEuclidean N 1 2 Ω} :
    u ∈ homogeneousKernel Ω a ↔ u ∈ SobolevEuclideanZero N 1 2 Ω ∧
      ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, a u v = 0 :=
  Iff.rfl

/-- The space of homogeneous solutions of $a$ is contained in $H^1_0(\Omega)$. -/
theorem homogeneousKernel_le : homogeneousKernel Ω a ≤ SobolevEuclideanZero N 1 2 Ω :=
  fun _ hu ↦ hu.1

/-- An element $u \in H^1(\Omega)$ lies in the space of homogeneous solutions of $a$ if and only if
it is the Galerkin solution in $H^1_0(\Omega)$ of the problem with form $a$ and datum $0$. -/
theorem mem_homogeneousKernel_iff_isGalerkinSolution {u : SobolevEuclidean N 1 2 Ω} :
    u ∈ homogeneousKernel Ω a ↔
      IsGalerkinSolution a (load Ω 0) (SobolevEuclideanZero N 1 2 Ω) u := by
  simp only [mem_homogeneousKernel_iff, IsGalerkinSolution, load_apply_inner, inner_zero_left]

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ and $\mu \in \mathbb{R}$. The shifted form
$a_\mu = a + \mu \langle \cdot, \cdot \rangle_{L^2(\Omega)}$ satisfies $a_\mu(u, v) = a(u, v) +
\mu \langle u, v \rangle_{L^2(\Omega)}$ for $u, v \in H^1(\Omega)$. -/
theorem add_smul_pairing_apply (μ : ℝ) (u v : SobolevEuclidean N 1 2 Ω) :
    (a + μ • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0) u v
      = a u v + μ * ⟪SobolevMultiIndex.weakDeriv u 0, SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
  simp only [add_apply, smul_apply, pairing_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- For $f, g \in L^2(\Omega)$, $\mu \in \mathbb{R}$ and $v \in H^1(\Omega)$, the load of
$f + \mu g$ at $v$ is $\int_\Omega f v + \mu \int_\Omega g v$. -/
theorem load_add_smul (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (μ : ℝ) (v : SobolevEuclidean N 1 2 Ω) :
    load Ω (f + μ • g) v = load Ω f v + μ * load Ω g v := by
  simp only [load_apply_inner, inner_add_left, real_inner_smul_left]

variable {μ : ℝ}
  (ha : ((a + μ • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0).restrict
    (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ and $\mu \in \mathbb{R}$, such that the
shifted form $a_\mu = a + \mu \langle \cdot, \cdot \rangle_{L^2(\Omega)}$ is coercive on
$H^1_0(\Omega)$, and let $S_\mu \colon L^2(\Omega) \to H^1_0(\Omega)$ be the solution map of
$a_\mu$. For $f \in L^2(\Omega)$ and $u \in H^1(\Omega)$, $u$ is a weak solution in
$H^1_0(\Omega)$ of $a(u, v) = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$ if and only if
$$u = S_\mu (f + \mu u).$$
This is the sentence "$u$ is a solution of (40) if and only if $u = T(f + \lambda u)$" of the
proof of Theorem 9.23 of [brezis2011functional].

On the right-hand side, $u$ is its class in $L^2(\Omega)$, and $S_\mu$ is
`Elliptic.solutionMap`. -/
theorem isGalerkinSolution_iff_eq_solutionMap
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : SobolevEuclidean N 1 2 Ω) :
    IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u ↔
      u = solutionMap Ω _ ha
        (f + μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume u) := by
  have key : IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u ↔
      IsGalerkinSolution (a + μ • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0)
        (load Ω (f + μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume u)) (SobolevEuclideanZero N 1 2 Ω) u := by
    refine and_congr_right fun _ ↦ forall₂_congr fun v hv ↦ ?_
    rw [add_smul_pairing_apply, load_add_smul, load_apply_inner, load_apply_inner,
      SobolevMultiIndex.fnL_eq_weakDeriv_zero, add_left_inj]
  rw [key]
  constructor
  · exact eq_solutionMap_of_isGalerkinSolution Ω _ ha
  · intro h
    have := isGalerkinSolution_solutionMap Ω _ ha
      (f + μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u)
    rwa [← h] at this

/-- Under the hypotheses of `Elliptic.isGalerkinSolution_iff_eq_solutionMap`, an element
$u \in H^1(\Omega)$ lies in the space of homogeneous solutions of $a$ if and only if
$u = S_\mu(\mu u)$, where $S_\mu$ is the solution map of the shifted form. -/
theorem mem_homogeneousKernel_iff_eq_solutionMap (u : SobolevEuclidean N 1 2 Ω) :
    u ∈ homogeneousKernel Ω a ↔
      u = solutionMap Ω _ ha
        (μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume u) := by
  rw [mem_homogeneousKernel_iff_isGalerkinSolution, isGalerkinSolution_iff_eq_solutionMap Ω a ha,
    zero_add]

/-- The linear map from the space of homogeneous solutions of $a$ to $L^2(\Omega)$ that sends $u$ to
its class in $L^2(\Omega)$. -/
def homogeneousKernelToLp :
    homogeneousKernel Ω a →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume :
    SobolevEuclidean N 1 2 Ω →ₗ[ℝ] _) ∘ₗ (homogeneousKernel Ω a).subtype

/-- The map from the space of homogeneous solutions to $L^2(\Omega)$ sends $u$ to its class in
$L^2(\Omega)$. -/
theorem homogeneousKernelToLp_apply (u : homogeneousKernel Ω a) :
    homogeneousKernelToLp Ω a u
      = SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u :=
  rfl

/-- The map from the space of homogeneous solutions to $L^2(\Omega)$ is injective, because an
element of $H^1(\Omega)$ is determined by its class in $L^2(\Omega)$
(`SobolevMultiIndex.fnL_injective`). -/
theorem homogeneousKernelToLp_injective : Function.Injective (homogeneousKernelToLp Ω a) :=
  fun _ _ h ↦ Subtype.ext (SobolevMultiIndex.fnL_injective h)

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ and $\mu \in \mathbb{R}$, such that the
shifted form $a_\mu = a + \mu \langle \cdot, \cdot \rangle_{L^2(\Omega)}$ is coercive on
$H^1_0(\Omega)$, and let $T_\mu$ be the solution operator of $a_\mu$. The image in $L^2(\Omega)$
of the space of homogeneous solutions of $a$ is $\ker (I - \mu T_\mu)$. So the space of
solutions of the homogeneous problem (40) is isomorphic to the space $N(I - \lambda T)$ of the
proof of Theorem 9.23 of [brezis2011functional]. -/
theorem range_homogeneousKernelToLp :
    LinearMap.range (homogeneousKernelToLp Ω a)
      = ((1 : ℝ) • (1 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
          Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        - μ • solutionOperator Ω _ ha).ker := by
  ext w
  rw [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    one_smul_one_sub_smul_apply, sub_eq_zero]
  constructor
  · rintro ⟨u, rfl⟩
    have hu := (mem_homogeneousKernel_iff_eq_solutionMap Ω a ha u).1 u.2
    rw [homogeneousKernelToLp_apply, ← map_smul (solutionOperator Ω _ ha), solutionOperator_apply,
      SobolevMultiIndexZero.fnL_eq, ← hu]
  · intro hw
    have hT : SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (solutionMap Ω _ ha (μ • w)) = w := by
      rw [← SobolevMultiIndexZero.fnL_eq, ← solutionOperator_apply,
        map_smul (solutionOperator Ω _ ha), ← hw]
    refine ⟨⟨solutionMap Ω _ ha (μ • w), ?_⟩, hT⟩
    rw [mem_homogeneousKernel_iff_eq_solutionMap Ω a ha, hT]

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ and $\mu \in \mathbb{R}$, such that the
shifted form $a_\mu = a + \mu \langle \cdot, \cdot \rangle_{L^2(\Omega)}$ is coercive on
$H^1_0(\Omega)$. If the solution operator $T_\mu \colon L^2(\Omega) \to L^2(\Omega)$ of $a_\mu$
is compact, then the space of solutions of the homogeneous problem (40) is finite-dimensional.
This is the first half of Theorem 9.23 of [brezis2011functional], with the compactness of
$T_\mu$ as a hypothesis.

The space is isomorphic to $\ker (I - \mu T_\mu)$ (`Elliptic.range_homogeneousKernelToLp`),
which is finite-dimensional by the Riesz theory of compact operators
(`IsCompactOperator.finiteDimensional_ker_pow`; Theorem 6.6 (a) of the source). The compactness
hypothesis holds when $\Omega$ has finite measure, by
`Elliptic.solutionOperator_isCompactOperator`. -/
theorem finiteDimensional_homogeneousKernel_of_isCompactOperator
    (hT : IsCompactOperator (solutionOperator Ω _ ha)) :
    FiniteDimensional ℝ (homogeneousKernel Ω a) := by
  have hK : IsCompactOperator (μ • solutionOperator Ω _ ha) := hT.smul μ
  have h1 := hK.finiteDimensional_ker_pow one_ne_zero 1
  rw [pow_one] at h1
  have h2 : FiniteDimensional ℝ (LinearMap.range (homogeneousKernelToLp Ω a)) := by
    rw [range_homogeneousKernelToLp Ω a ha]
    exact h1
  exact (LinearEquiv.ofInjective _ (homogeneousKernelToLp_injective Ω a)).symm.finiteDimensional

/-- Under the hypotheses of `Elliptic.range_homogeneousKernelToLp`, the dimension of the space of
homogeneous solutions of $a$ is the dimension of $\ker (I - \mu T_\mu)$. -/
theorem finrank_homogeneousKernel :
    finrank ℝ (homogeneousKernel Ω a)
      = finrank ℝ (((1 : ℝ) • (1 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
          →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        - μ • solutionOperator Ω _ ha).ker) := by
  rw [← range_homogeneousKernelToLp Ω a ha]
  exact (LinearEquiv.ofInjective _ (homogeneousKernelToLp_injective Ω a)).finrank_eq

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ and $\mu \in \mathbb{R}$, such that the
shifted form $a_\mu = a + \mu \langle \cdot, \cdot \rangle_{L^2(\Omega)}$ is coercive on
$H^1_0(\Omega)$, and let $T_\mu$ be the solution operator of $a_\mu$. For $f \in L^2(\Omega)$,
the weak problem $a(u, v) = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$ has a solution
$u \in H^1_0(\Omega)$ if and only if $f$ is in the range of $I - \mu T_\mu$. This is the
reduction of the proof of Theorem 9.23 of [brezis2011functional].

If $w - \mu T_\mu w = f$, then the value of the solution map of $a_\mu$ at $w$ solves the
problem. Conversely, a solution $u$ gives $w = f + \mu u$. -/
theorem exists_isGalerkinSolution_iff_mem_range
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    (∃ u, IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) ↔
      f ∈ ((1 : ℝ) • (1 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
          Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        - μ • solutionOperator Ω _ ha).range := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    rw [isGalerkinSolution_iff_eq_solutionMap Ω a ha] at hu
    refine ⟨f + μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume u, ?_⟩
    rw [ContinuousLinearMap.coe_coe, one_smul_one_sub_smul_apply, solutionOperator_apply,
      SobolevMultiIndexZero.fnL_eq, ← hu, add_sub_cancel_right]
  · rintro ⟨v, hv⟩
    rw [ContinuousLinearMap.coe_coe, one_smul_one_sub_smul_apply, solutionOperator_apply,
      SobolevMultiIndexZero.fnL_eq, sub_eq_iff_eq_add] at hv
    refine ⟨solutionMap Ω _ ha v, ?_⟩
    rw [isGalerkinSolution_iff_eq_solutionMap Ω a ha, ← hv]

/-- The **Fredholm alternative** for (40), with the compactness of the solution operator as a
hypothesis. Let $a$ be a bounded bilinear form on $H^1(\Omega)$ and $\mu \in \mathbb{R}$, such
that the shifted form $a_\mu = a + \mu \langle \cdot, \cdot \rangle_{L^2(\Omega)}$ is coercive
on $H^1_0(\Omega)$ and its solution operator $T_\mu$ is compact. Then there is a
finite-dimensional subspace $F \subseteq L^2(\Omega)$, of the same dimension as the space of
homogeneous solutions of $a$, such that for every $f \in L^2(\Omega)$ the weak problem
$a(u, v) = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$ has a solution $u \in H^1_0(\Omega)$
if and only if $f$ is orthogonal to $F$ in $L^2(\Omega)$. This is the second half of Theorem
9.23 of [brezis2011functional].

The subspace is $F = \ker (I - \mu T_\mu^*)$, by the solvability criterion
`IsCompactOperator.range_smul_sub_eq_orthogonal_ker_adjoint` and the index formula
`IsCompactOperator.finrank_ker_eq_finrank_ker_adjoint` on the Hilbert space $L^2(\Omega)$
(Theorem 6.6 (b) and (d) of the source). -/
theorem exists_orthogonality_iff_exists_solution_of_isCompactOperator
    (hT : IsCompactOperator (solutionOperator Ω _ ha)) :
    ∃ F : Submodule ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
      FiniteDimensional ℝ F ∧ finrank ℝ F = finrank ℝ (homogeneousKernel Ω a) ∧
        ∀ f, (∃ u, IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) ↔
          ∀ v ∈ F, ⟪f, v⟫_ℝ = 0 := by
  obtain ⟨F, h1, h2, h3⟩ := exists_finiteDimensional_forall_iff_inner_eq_zero (hT.smul μ)
    one_ne_zero (exists_isGalerkinSolution_iff_mem_range Ω a ha)
  exact ⟨F, h1, h2.trans (finrank_homogeneousKernel Ω a ha).symm, h3⟩

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ and $\mu \in \mathbb{R}$, such that the
shifted form $a_\mu = a + \mu \langle \cdot, \cdot \rangle_{L^2(\Omega)}$ is coercive on
$H^1_0(\Omega)$ and its solution operator $T_\mu$ is compact. If the homogeneous problem (40)
has only the zero solution, then for every $f \in L^2(\Omega)$ there is exactly one
$u \in H^1_0(\Omega)$ with $a(u, v) = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$. This is
the first clause of Remark 23 in Chapter 9 of [brezis2011functional], with the compactness of
$T_\mu$ as a hypothesis.

Existence is the Fredholm alternative `IsCompactOperator.injective_iff_surjective_smul_one_sub`
for $I - \mu T_\mu$, whose kernel is the image of the homogeneous solutions (Theorem 6.6 (c) of
the source). Uniqueness holds because the difference of two solutions is a homogeneous solution. -/
theorem existsUnique_of_homogeneousKernel_eq_bot_of_isCompactOperator
    (hT : IsCompactOperator (solutionOperator Ω _ ha)) (h : homogeneousKernel Ω a = ⊥)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u := by
  have hker : ((1 : ℝ) • (1 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        - μ • solutionOperator Ω _ ha).ker = ⊥ := by
    rw [← range_homogeneousKernelToLp Ω a ha, LinearMap.range_eq_bot]
    ext u
    have hu : (u : SobolevEuclidean N 1 2 Ω) ∈ (⊥ : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) :=
      h ▸ u.2
    rw [Submodule.mem_bot] at hu
    rw [homogeneousKernelToLp_apply, hu, map_zero, LinearMap.zero_apply]
  have hsurj := surjective_smul_one_sub_of_ker_eq_bot (hT.smul μ) one_ne_zero hker
  obtain ⟨u, hu⟩ := (exists_isGalerkinSolution_iff_mem_range Ω a ha f).2
    (LinearMap.mem_range.2 (hsurj f))
  refine ⟨u, hu, fun w hw ↦ ?_⟩
  have hmem : w - u ∈ homogeneousKernel Ω a := by
    refine ⟨sub_mem hw.1 hu.1, fun v hv ↦ ?_⟩
    have e : a (w - u) = a w - a u := map_sub _ _ _
    rw [e, sub_apply, hw.2 v hv, hu.2 v hv, sub_self]
  rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

end Fredholm

/-!
### The solution operator is compact if $H^1_0(\Omega) \hookrightarrow L^2(\Omega)$ is compact
-/

/-- Let $a$ be a bounded bilinear form on $H^1(\Omega)$ whose restriction to $H^1_0(\Omega)$ is
coercive. If the inclusion $H^1_0(\Omega) \to L^2(\Omega)$ is a compact operator, then the
solution operator $T \colon L^2(\Omega) \to L^2(\Omega)$ of $a$ is compact.

The operator $T$ is the inclusion composed with the bounded solution map, and a compact operator
composed with a bounded one is compact (`IsCompactOperator.comp_clm`). With the
Rellich–Kondrachov theorem in the $W^{1,p}_0$ form of Remark 20 of [brezis2011functional], this
gives `Elliptic.solutionOperator_isCompactOperator`. -/
theorem solutionOperator_isCompactOperator_of_isCompactOperator_fnL
    (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
    (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)
    (h : IsCompactOperator
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)) :
    IsCompactOperator (solutionOperator Ω a ha) := by
  rw [solutionOperator, ContinuousLinearMap.coe_comp]
  exact h.comp_clm _


/-! ### Theorem 9.23 and Remark 23: the Fredholm alternative for the general Dirichlet problem -/

section Fredholm23

variable {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

/-- **Gårding's inequality on $H^1_0(\Omega)$**. Let the coefficients $a_{ij}$ be uniformly elliptic
with constant $\alpha$. Then the shifted form $a(u, v) + \lambda \int_\Omega u v$, with the
shift $\lambda$ of `Elliptic.generalForm_garding`, is coercive on $H^1_0(\Omega)$. So its
solution operator `Elliptic.solutionOperator` exists; it is the operator $T$ of the proof of
Theorem 9.23 of [brezis2011functional]. -/
theorem generalForm_garding_restrict_isCoercive (hA : IsUniformlyElliptic Ω A α) :
    ((generalForm Ω A a₁ a₀ + ((∑ i, ‖a₁ i‖) ^ 2 / (2 * α) + ‖a₀‖ + α / 2)
      • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0).restrict
        (SobolevEuclideanZero N 1 2 Ω)).IsCoercive :=
  SesqForm.IsCoercive.restrict ⟨α / 2, half_pos hA.1, generalForm_garding Ω hA⟩ _

/-- Let $\Omega$ be an open set of finite Lebesgue measure, and let $a$ be a bounded bilinear form
on $H^1(\Omega)$ whose restriction to $H^1_0(\Omega)$ is coercive. Then the solution operator
$T \colon L^2(\Omega) \to L^2(\Omega)$ of $a$ is compact. This is the sentence
"$T : L^2 \to L^2$ is a compact linear operator (since $\Omega$ is bounded, the injection
$H^1_0 \subset L^2$ is compact; see Theorem 9.16 and Remark 20)" of the proof of Theorem 9.23 of
[brezis2011functional], and the compactness of $T$ in the proof of Theorem 9.31.

The source assumes $\Omega$ bounded. The operator $T$ factors through the inclusion
$H^1_0(\Omega) \to L^2(\Omega)$, which is compact by the Rellich–Kondrachov theorem in the
$W^{1,p}_0$ form of Remark 20 of the source (`SobolevEuclideanZero.isCompactOperator_fnL`, with
no regularity of $\Omega$), and a compact operator composed with a bounded one is compact. -/
theorem solutionOperator_isCompactOperator
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
    (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive) :
    IsCompactOperator (solutionOperator Ω a ha) :=
  solutionOperator_isCompactOperator_of_isCompactOperator_fnL Ω a ha
    (SobolevEuclideanZero.isCompactOperator_fnL ENNReal.ofNat_ne_top hΩ)

/-- Let $\Omega$ be an open set of finite measure, let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$ with
$a_{ij}$ uniformly elliptic with constant $\alpha$, and let $a$ be the general form (41). Then
the space
$$N = \{u \in H^1_0(\Omega) : a(u, v) = 0 \text{ for all } v \in H^1_0(\Omega)\}$$
of weak solutions of the homogeneous problem (40) is finite-dimensional. This is the first half
of **Theorem 9.23** of [brezis2011functional].

The source assumes $\Omega$ bounded. In the proof, Gårding's inequality
(`Elliptic.generalForm_garding`) gives a $\lambda$ for which the shifted form is coercive on
$H^1_0(\Omega)$; its solution operator $T$ is compact
(`Elliptic.solutionOperator_isCompactOperator`), and $u \in N$ if and only if $u = \lambda T u$
in $L^2(\Omega)$. So $N$ is isomorphic to $\ker (I - \lambda T)$, which is finite-dimensional by
the Riesz theory (`Elliptic.finiteDimensional_homogeneousKernel_of_isCompactOperator`). -/
theorem finiteDimensional_ker_general (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hA : IsUniformlyElliptic Ω A α) :
    FiniteDimensional ℝ (homogeneousKernel Ω (generalForm Ω A a₁ a₀)) :=
  finiteDimensional_homogeneousKernel_of_isCompactOperator Ω _
    (generalForm_garding_restrict_isCoercive Ω hA) (solutionOperator_isCompactOperator Ω hΩ _ _)

/-- **The Fredholm alternative** for (40). Let $\Omega$ be an open set of finite measure, let
$a_{ij}, a_i, a_0 \in L^\infty(\Omega)$ with $a_{ij}$ uniformly elliptic with constant $\alpha$,
and let $a$ be the general form (41). Then there is a finite-dimensional subspace
$F \subseteq L^2(\Omega)$ with $\dim F = \dim N$, where $N$ is the space of homogeneous
solutions, such that for every $f \in L^2(\Omega)$ the weak problem $a(u, v) = \int_\Omega f v$
for all $v \in H^1_0(\Omega)$ has a solution $u \in H^1_0(\Omega)$ if and only if $f$ is
orthogonal to $F$ in $L^2(\Omega)$. This is the second half of Theorem 9.23 of
[brezis2011functional].

The source assumes $\Omega$ bounded and argues through its Theorem 6.6. Here
$F = \ker (I - \lambda T^*)$ for the compact solution operator $T$ of the shifted form, by the
Fredholm alternative in Hilbert space
(`IsCompactOperator.range_smul_sub_eq_orthogonal_ker_adjoint`,
`IsCompactOperator.finrank_ker_eq_finrank_ker_adjoint`). -/
theorem exists_orthogonality_iff_exists_solution
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hA : IsUniformlyElliptic Ω A α) :
    ∃ F : Submodule ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
      FiniteDimensional ℝ F ∧
        finrank ℝ F = finrank ℝ (homogeneousKernel Ω (generalForm Ω A a₁ a₀)) ∧
        ∀ f, (∃ u, IsGalerkinSolution (generalForm Ω A a₁ a₀) (load Ω f)
          (SobolevEuclideanZero N 1 2 Ω) u) ↔ ∀ v ∈ F, ⟪f, v⟫_ℝ = 0 :=
  exists_orthogonality_iff_exists_solution_of_isCompactOperator Ω _
    (generalForm_garding_restrict_isCoercive Ω hA) (solutionOperator_isCompactOperator Ω hΩ _ _)

/-- Let $\Omega$ be an open set of finite measure, let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$ with
$a_{ij}$ uniformly elliptic with constant $\alpha$, and let $a$ be the general form (41). If the
homogeneous problem (40) has only the zero solution, then for every $f \in L^2(\Omega)$ there is
exactly one $u \in H^1_0(\Omega)$ with $a(u, v) = \int_\Omega f v$ for all
$v \in H^1_0(\Omega)$. This is the first clause of Remark 23 in Chapter 9 of
[brezis2011functional].

The source assumes $\Omega$ bounded. Existence is the Fredholm alternative
(`IsCompactOperator.injective_iff_surjective_smul_one_sub` for $I - \lambda T$), and uniqueness
holds because the difference of two solutions is a homogeneous solution. The second clause of
the remark, that $a_0 \ge 0$ alone forces the trivial kernel, is the general case of Proposition
9.29, which the source cites from Gilbarg and Trudinger; it is not proved here. -/
theorem existsUnique_of_ker_eq_bot (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hA : IsUniformlyElliptic Ω A α) (h : homogeneousKernel Ω (generalForm Ω A a₁ a₀) = ⊥)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, IsGalerkinSolution (generalForm Ω A a₁ a₀) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u :=
  existsUnique_of_homogeneousKernel_eq_bot_of_isCompactOperator Ω _
    (generalForm_garding_restrict_isCoercive Ω hA) (solutionOperator_isCompactOperator Ω hΩ _ _)
    h f

end Fredholm23

end Elliptic
