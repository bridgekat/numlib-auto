/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# Atkinson and Han, Section 11.1: From variational equations to variational inequalities

This module formalizes Section 11.1 of [han2009theoretical]. The section motivates the chapter with
two problems. The obstacle problem (Example 11.1.1) minimizes the energy $E(v) = \int_\Omega
(\frac12 |\nabla v|^2 - f v) \, dx$ over the convex set $K = \{v \in H_0^1(\Omega) : v \ge \psi
\text{ a.e. in } \Omega\}$, which is not a subspace. A function $u \in K$ is the minimizer if and
only if it satisfies the variational inequality (11.1.7),
$$\int_\Omega \nabla u \cdot \nabla(v - u) \, dx \ge \int_\Omega f (v - u) \, dx \qquad \text{for
  all } v \in K,$$
and a smooth solution satisfies the complementarity conditions (11.1.9) at each point of $\Omega$.
The simplified friction problem (Example 11.1.2) minimizes over $H^1(\Omega)$ the energy (11.1.12),
which has the boundary term $g \int_\Gamma |v| \, ds$ that is not differentiable. Its minimizers are
the solutions of the variational inequality (11.1.13), and a smooth solution satisfies the boundary
value problem (11.1.14)–(11.1.15).

The obstacle problem uses the Dirichlet form and Poincaré's inequality of
`Numlib.Analysis.PDE.Elliptic.Dirichlet`. The friction problem uses the surface measure, the outward
normal and the trace of `Numlib.Analysis.Sobolev.Boundary.Data`, and Theorem 11.2.1 in the form
`isMinOn_energy_add_iff` of `Numlib.Variational.Inequality.Basic`.

## Main definitions

* (11.1.3), `AtkinsonHan.Chapter11.dirichletBilinForm`: the bilinear form $a(u, v) = \int_\Omega
  \nabla u \cdot \nabla v \, dx$ on $H_0^1(\Omega)$.
* (11.1.3), `AtkinsonHan.Chapter11.loadZero`: the linear functional
  $\ell(v) = \int_\Omega f v \, dx$ on $H_0^1(\Omega)$.
* (11.1.5), `AtkinsonHan.Chapter11.obstacleEnergy`: the energy $E(v) = \int_\Omega (\frac12 |\nabla
  v|^2 - f v) \, dx$.
* Example 11.1.1, `AtkinsonHan.Chapter11.obstacleSet`: the admissible set $K = \{v \in H_0^1(\Omega)
  : v \ge \psi \text{ a.e. in } \Omega\}$.
* Example 11.1.2, `AtkinsonHan.Chapter11.frictionFunctional`: the friction functional
  $j(v) = g \int_\Gamma |v| \, ds$ on $H^1(\Omega)$.
* (11.1.12), `AtkinsonHan.Chapter11.frictionEnergy`: the energy $E(v) = \int_\Omega (\frac12
  (|\nabla v|^2 + v^2) - f v) \, dx + j(v)$.
* Example 11.1.2, `AtkinsonHan.Chapter11.frictionBilinForm`: the bilinear form $a(u, v) =
  \int_\Omega (\nabla u \cdot \nabla v + u v) \, dx$ on $H^1(\Omega)$.

## Main results

* Example 11.1.1, `AtkinsonHan.Chapter11.example_11_1_1`: $u \in K$ minimizes the energy over $K$ if
  and only if it satisfies the variational inequality (11.1.7).
* Example 11.1.1, `AtkinsonHan.Chapter11.example_11_1_1_pointwise`: under the regularity (11.1.8),
  the minimizer satisfies $u \ge \psi$, $-\Delta u \ge f$ and $(u - \psi)(-\Delta u - f) = 0$ in
  $\Omega$, (11.1.9).
* Example 11.1.2, `AtkinsonHan.Chapter11.example_11_1_2`: $u$ minimizes the energy (11.1.12) over
  $H^1(\Omega)$ if and only if it satisfies the variational inequality (11.1.13).
* Example 11.1.2, `AtkinsonHan.Chapter11.example_11_1_2_pointwise`: a smooth solution of (11.1.13)
  on a bounded $C^1$ domain satisfies $-\Delta u + u = f$ in $\Omega$, and
  $|\partial u / \partial\nu| \le g$ and $(\partial u / \partial\nu) u + g |u| = 0$ on $\Gamma$,
  (11.1.14)–(11.1.15).

## Proof outline

The equivalences of Examples 11.1.1 and 11.1.2, which the source leaves as Exercises 11.1.1 and
11.1.2, are Theorem 8.3.3 on the convex set $K$ and Theorem 11.2.1 with $K = V$. The pointwise forms
test the variational inequality with $v = u \pm \varepsilon \varphi$ for smooth $\varphi$, integrate
by parts, and apply the fundamental lemma of the calculus of variations: in $\Omega$ in its
inequality form `nonneg_on_of_forall_integral_mul_testFunction_nonneg` and its local form
`eqOn_zero_of_forall_integral_mul_testFunction_eq_zero`, and on $\Gamma$ through bump functions on
the boundary (`BoundaryData.exists_bump_lt_integral_mul`).

## Implementation notes

* The obstacle problem is posed on a bounded open set $\Omega \subseteq B(0, R) \subseteq
  \mathbb{R}^{d+1}$. The space $V = H_0^1(\Omega)$ is `SobolevEuclideanZero (d + 1) 1 2 Ω`, the
  obstacle $\psi$ is an element of $H^1(\Omega)$, `SobolevEuclidean (d + 1) 1 2 Ω`, and
  $f \in L^2(\Omega)$.
* The space $H_0^1(\Omega)$ of Definition 7.2.9, `AtkinsonHan.Chapter07.definition_7_2_9`, is the
  same closure in the tensor formulation `Sobolev ℝ 1 2 Ω volume`. The Dirichlet form and Poincaré's
  inequality of the backbone are stated in the formulation with multi-indices, so the obstacle
  problem is posed there (see `AtkinsonHan.Chapter08.modelOperator`).
* The order $v \ge \psi$ in $K$ is the almost-everywhere order of $L^2(\Omega)$;
  `AtkinsonHan.Chapter11.mem_obstacleSet_iff` gives it pointwise.
* The friction problem is posed on an open set $\Omega \subseteq \mathbb{R}^N$ with boundary data
  `B : BoundaryData Ω` and a trace `𝒯 : B.TraceFamily`. These give the surface measure $\sigma$ on
  $\Gamma = \partial\Omega$, the outward normal $\nu$, and the trace
  $\gamma : H^1(\Omega) \to L^2(\sigma)$, `𝒯.traceL 2`. They exist on bounded $C^1$ domains
  (`IsContDiffDomain.traceFamily`) and on polygons without slits (`Triangulation.traceFamily`).

## Deviations from the source

* **Example 11.1.1** (reading). The condition $\psi \le 0$ on $\Gamma$ is the hypothesis that
  $\max(\psi, 0)$ is an element of $H_0^1(\Omega)$, which is how the source uses it. See
  `AtkinsonHan.Chapter11.obstacleSet_nonempty`.
* **Example 11.1.1** (generalization). The source assumes a Lipschitz boundary; the obstacle problem
  is stated on every bounded open set. See `AtkinsonHan.Chapter11.example_11_1_1`.
* **(11.1.9)** (generalization). The regularity (11.1.8) is stated on representatives of $f$, $\psi$
  and $u$ in $\Omega$, and the condition $u \in C(\overline\Omega)$ of the source is not needed. See
  `AtkinsonHan.Chapter11.example_11_1_1_pointwise`.
* **Example 11.1.2** (reading). The Lipschitz boundary of the source is replaced by boundary data
  with a trace, which exist for a bounded $C^1$ domain and for a polygon without slits. See
  `AtkinsonHan.Chapter11.example_11_1_2`.
* **(11.1.14)–(11.1.15)** (reading). The domain is a bounded $C^1$ domain, and a smooth solution is
  one with a representative in $C^2(\overline\Omega)$ whose gradient extends continuously to
  $\overline\Omega$. The boundary conditions hold at every point of $\Gamma$, where the source has
  the points at which the normal is defined. See `AtkinsonHan.Chapter11.example_11_1_2_pointwise`.
-/

open Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped ContDiff Distributions ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter11

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-! ### The bilinear form, the load and the energy of (11.1.3)–(11.1.5) -/

/-- The bilinear form of (11.1.3) of [han2009theoretical] on $H_0^1(\Omega)$, for an open set
$\Omega \subseteq \mathbb{R}^{d+1}$:
$$a(u, v) = \int_\Omega \nabla u \cdot \nabla v \, dx.$$

It is the operator `AtkinsonHan.Chapter08.modelOperator` of Example 8.2.6, read as a bilinear
form of Section 8.3. It is a `def` and not an `abbrev`, so that a rewrite at a value of the form
does not unfold `AtkinsonHan.Chapter08.modelOperator`. -/
noncomputable def dirichletBilinForm : BilinForm (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  BilinForm.ofCLM (Chapter08.modelOperator Ω)

/-- The form `AtkinsonHan.Chapter11.dirichletBilinForm` agrees with the Dirichlet form
`Elliptic.dirichletForm` of the backbone, $a(u, v) = \int_\Omega \nabla u \cdot \nabla v \, dx$. -/
theorem dirichletBilinForm_apply (u v : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    dirichletBilinForm Ω u v = Elliptic.dirichletForm Ω u v :=
  rfl

/-- The form (11.1.3) satisfies $|a(u, v)| \le \|u\|_{1,\Omega} \|v\|_{1,\Omega}$, so it is bounded
with constant $1$. -/
theorem dirichletBilinForm_isBoundedWith : (dirichletBilinForm Ω).IsBoundedWith 1 := fun u v ↦ by
  rw [dirichletBilinForm_apply, one_mul, ← Real.norm_eq_abs]
  have h := Elliptic.dirichletForm_isBoundedWith Ω u v
  rwa [one_mul] at h

/-- Let $R \ge 0$ and $\Omega \subseteq B(0, R)$. The form (11.1.3) is $V$-elliptic on
$H_0^1(\Omega)$:
$$a(v, v) \ge (1 + (2R)^2)^{-1} \|v\|_{1,\Omega}^2 \qquad \text{for all } v \in H_0^1(\Omega).$$

The bound is Poincaré's inequality, `Elliptic.dirichletForm_restrict_isCoerciveWith`. -/
theorem dirichletBilinForm_isEllipticWith {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) :
    (dirichletBilinForm Ω).IsEllipticWith (1 + (2 * R) ^ 2)⁻¹ := fun v ↦ by
  rw [dirichletBilinForm_apply]
  exact Elliptic.dirichletForm_restrict_isCoerciveWith Ω hR hΩ v

/-- The form (11.1.3) is symmetric: $a(u, v) = a(v, u)$. -/
theorem dirichletBilinForm_isSymm : LinearMap.BilinForm.IsSymm (dirichletBilinForm Ω) := by
  unfold dirichletBilinForm
  rw [BilinForm.isSymm_ofCLM_iff]
  intro u v
  have h := Elliptic.dirichletForm_isHermitian Ω u v
  rw [conj_trivial] at h
  exact h

/-- The linear functional of (11.1.3) of [han2009theoretical] on $H_0^1(\Omega)$, for
$f \in L^2(\Omega)$:
$$\ell(v) = \int_\Omega f v \, dx.$$

It is the functional `Elliptic.load Ω f` on $H^1(\Omega)$ restricted to $H_0^1(\Omega)$. -/
noncomputable def loadZero
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  (Elliptic.load Ω f).comp (SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL

/-- The functional `AtkinsonHan.Chapter11.loadZero Ω f` is $\ell(v) = \int_\Omega f v \, dx$. -/
theorem loadZero_apply
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    loadZero Ω f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      f x * SobolevMultiIndex.fn (v : SobolevEuclidean (d + 1) 1 2 Ω) x :=
  Elliptic.load_apply Ω f v

/-- The functional $\ell$ is linear in the datum: the functional for $f - g$ is the difference of
the functionals for $f$ and $g$. -/
theorem loadZero_sub
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    loadZero Ω (f - g) = loadZero Ω f - loadZero Ω g := by
  ext v
  exact Elliptic.load_sub (Ω := Ω) f g v

/-- The functional $\ell(v) = \int_\Omega f v \, dx$ on $H_0^1(\Omega)$ has norm at most
$\|f\|_{L^2(\Omega)}$. -/
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

/-- The functionals for two data $f, g \in L^2(\Omega)$ differ in norm by at most
$\|f - g\|_{L^2(\Omega)}$. -/
theorem norm_loadZero_sub_le
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ‖loadZero Ω f - loadZero Ω g‖ ≤ ‖f - g‖ := by
  rw [← loadZero_sub]
  exact norm_loadZero_le Ω _

/-- The energy functional (11.1.5) of [han2009theoretical] on $H_0^1(\Omega)$, for
$f \in L^2(\Omega)$:
$$E(v) = \int_\Omega \left( \frac12 |\nabla v|^2 - f v \right) dx.$$

It is the energy $E(v) = \frac12 a(v, v) - \ell(v)$ of Theorem 8.3.3 for the form (11.1.3) and
the functional $\ell(v) = \int_\Omega f v \, dx$. `AtkinsonHan.Chapter11.obstacleEnergy_apply`
gives the integral. -/
noncomputable def obstacleEnergy
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    SobolevEuclideanZero (d + 1) 1 2 Ω → ℝ :=
  (dirichletBilinForm Ω).energy (loadZero Ω f)

/-- For $v \in H^1(\Omega)$, the function $\sum_i (\partial_i v)^2$ is integrable on $\Omega$. -/
theorem integrable_sum_sq_weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω) :
    Integrable (fun x ↦ ∑ i, SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x ^ 2)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  refine integrable_finsetSum _ fun i _ ↦ ?_
  exact (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))
    (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))).congr
    (Eventually.of_forall fun x ↦ by simp [sq])

/-- For $f \in L^2(\Omega)$ and $v \in H^1(\Omega)$, the function $f v$ is integrable on $\Omega$.
-/
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

/-- The energy (11.1.5) is the integral
$$E(v) = \int_\Omega \left( \frac12 \sum_i (\partial_i v)^2 - f v \right) dx \qquad \text{for }
  v \in H_0^1(\Omega).$$
-/
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

/-! ### The admissible set $K$ -/

/-- The admissible set of the obstacle problem, Example 11.1.1 of [han2009theoretical]. For an
obstacle $\psi \in H^1(\Omega)$,
$$K = \{v \in H_0^1(\Omega) : v \ge \psi \text{ a.e. in } \Omega\}.$$

The order is the almost-everywhere order of the functions of $v$ and $\psi$ in $L^2(\Omega)$.
`AtkinsonHan.Chapter11.mem_obstacleSet_iff` gives it pointwise. -/
def obstacleSet (ψ : SobolevEuclidean (d + 1) 1 2 Ω) :
    Set (SobolevEuclideanZero (d + 1) 1 2 Ω) :=
  {v | SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume ψ
    ≤ SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume v}

/-- An element $v \in H_0^1(\Omega)$ lies in $K$ if and only if $\psi(x) \le v(x)$ for almost every
$x \in \Omega$. -/
theorem mem_obstacleSet_iff {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {v : SobolevEuclideanZero (d + 1) 1 2 Ω} :
    v ∈ obstacleSet Ω ψ ↔ ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      SobolevMultiIndex.fn ψ x ≤ SobolevMultiIndex.fn (v : SobolevEuclidean (d + 1) 1 2 Ω) x := by
  change SobolevMultiIndex.fnL ℝ _ 1 2 Ω volume ψ ≤ SobolevMultiIndexZero.fnL ℝ _ 1 2 Ω volume v ↔ _
  rw [← Lp.coeFn_le, SobolevMultiIndexZero.fnL_apply, SobolevMultiIndex.fnL_apply]
  exact Iff.rfl

/-- The admissible set $K$ is closed in $H_0^1(\Omega)$.

It is the preimage of the closed set $\{w \in L^2(\Omega) : \psi \le w\}$ under the continuous
inclusion $H_0^1(\Omega) \to L^2(\Omega)$. -/
theorem isClosed_obstacleSet (ψ : SobolevEuclidean (d + 1) 1 2 Ω) :
    IsClosed (obstacleSet Ω ψ) :=
  isClosed_Ici.preimage (SobolevMultiIndexZero.fnL ℝ _ 1 2 Ω volume).continuous

/-- The admissible set $K$ is convex.

It is the preimage of a convex set under a linear map. -/
theorem convex_obstacleSet (ψ : SobolevEuclidean (d + 1) 1 2 Ω) : Convex ℝ (obstacleSet Ω ψ) :=
  (Lp.convex_Ici _).linear_preimage
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume :
      SobolevEuclideanZero (d + 1) 1 2 Ω →ₗ[ℝ]
        Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))

/-- Let $\psi \in H^1(\Omega)$, and assume that $\max(\psi, 0)$ agrees almost everywhere on $\Omega$
with an element $w \in H_0^1(\Omega)$. Then $K$ is nonempty: it contains $w$.

**Reading.** The source assumes $\psi \le 0$ on $\Gamma$, a condition on the trace, and uses it
to show $\max(0, \psi) \in K$ (Example 11.2.3). The hypothesis here is that conclusion. If
$\psi$ has a representative that is continuous on $\overline\Omega$ and at most $0$ on
$\partial\Omega$, the hypothesis follows from Theorem 9.17 of [brezis2011functional]
(`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`) applied to
$\max(\psi, 0)$, which lies in $H^1(\Omega)$ by `MemSobolevMultiIndex.posPart`. -/
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

/-- **Example 11.1.1** of [han2009theoretical] (the obstacle problem), the variational inequality
(11.1.7). Let $\Omega \subseteq B(0, R) \subseteq \mathbb{R}^{d+1}$ be open, with $R \ge 0$, let
$\psi \in H^1(\Omega)$ and $f \in L^2(\Omega)$, and let $K = \{v \in H_0^1(\Omega) : v \ge \psi
\text{ a.e. in } \Omega\}$. Let $u \in K$. Then $u$ minimizes the energy $E(v) = \int_\Omega
(\frac12 |\nabla v|^2 - f v) \, dx$ over $K$, the principle of minimum energy (11.1.6), if and
only if
$$\int_\Omega \nabla u \cdot \nabla(v - u) \, dx \ge \int_\Omega f (v - u) \, dx \qquad
  \text{for all } v \in K.$$

**Generalization.** The source assumes a Lipschitz boundary. The statement holds on every
bounded open set.

The source leaves the equivalence as Exercise 11.1.1. It is the characterization (8.3.3) of
Theorem 8.3.3 (`AtkinsonHan.Chapter08.theorem_8_3_3_iff`) for the minimizer of the energy of a
symmetric $V$-elliptic form on a convex set; the form is (11.1.3), and its ellipticity is
Poincaré's inequality. The existence and uniqueness of the minimizer are Example 11.2.3
(`AtkinsonHan.Chapter11.example_11_2_3`) and Example 11.3.10
(`AtkinsonHan.Chapter11.example_11_3_10`). The pointwise form (11.1.9) is
`AtkinsonHan.Chapter11.example_11_1_1_pointwise`. -/
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

/-- Let $a$ be a bilinear form and $\ell$ a linear functional on a real inner product space $V$, let
$K \subseteq V$, and let $u \in V$ satisfy $\ell(v - u) \le a(u, v - u)$ for all $v \in K$. If
$u + w \in K$, then $\ell(w) \le a(u, w)$. -/
theorem le_of_forall_sub_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : BilinForm V} {ℓ : StrongDual ℝ V} {K : Set V} {u : V}
    (hvi : ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u)) {w : V} (hw : u + w ∈ K) : ℓ w ≤ a u w := by
  have := hvi (u + w) hw
  rwa [add_sub_cancel_left] at this

/-- Let $a$ be a bilinear form and $\ell$ a linear functional on a real inner product space $V$, and
let $u, w \in V$ and $\varepsilon \in \mathbb{R}$. If
$\ell(\varepsilon w) \le a(u, \varepsilon w)$, then
$\varepsilon \ell(w) \le \varepsilon a(u, w)$. -/
theorem smul_le_of_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : BilinForm V} {ℓ : StrongDual ℝ V} {u w : V} {ε : ℝ} (h : ℓ (ε • w) ≤ a u (ε • w)) :
    ε * ℓ w ≤ ε * a u w := by
  rwa [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h

end Pointwise

section PointwiseMain

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open Laplacian in
/-- The test-function step of Example 11.1.1. Let $\psi \in H^1(\Omega)$ and $f \in L^2(\Omega)$,
and let $u \in H_0^1(\Omega)$ satisfy the variational inequality $\ell(v - u) \le a(u, v - u)$
for all $v \in K$. Let $\tilde f$, $\tilde\psi$ and $\tilde u$ be functions that agree almost
everywhere on $\Omega$ with $f$, $\psi$ and $u$, with $\tilde u$ of class $C^2$ on $\Omega$. Let
$\varphi \in C_0^\infty(\Omega)$ and $\varepsilon \in \mathbb{R}$ with
$\tilde\psi \le \tilde u + \varepsilon\varphi$ almost everywhere on $\Omega$. Then
$$\varepsilon \int_\Omega \tilde f \varphi \, dx \le \varepsilon \int_\Omega (-\Delta\tilde u)
  \varphi \, dx.$$

The proof tests the inequality with $v = u + \varepsilon\varphi$ and integrates by parts
(`Elliptic.dirichletForm_eq_integral_neg_laplacian_mul`). -/
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
/-- **Example 11.1.1** of [han2009theoretical], the pointwise form (11.1.9). Let $\Omega \subseteq
B(0, R) \subseteq \mathbb{R}^{d+1}$ be open, with $R \ge 0$, let $\psi \in H^1(\Omega)$ and
$f \in L^2(\Omega)$, and let $u \in K$ minimize the energy over $K = \{v \in H_0^1(\Omega) : v
\ge \psi \text{ a.e. in } \Omega\}$. Assume the regularity (11.1.8) in the following form: $f$,
$\psi$ and $u$ agree almost everywhere on $\Omega$ with functions $\tilde f$, $\tilde\psi$ and
$\tilde u$, where $\tilde f$ and $\tilde\psi$ are continuous on $\Omega$ and $\tilde u$ is of
class $C^2$ on $\Omega$. Then at every point of $\Omega$
$$\tilde u - \tilde\psi \ge 0, \qquad -\Delta\tilde u - \tilde f \ge 0, \qquad (\tilde u -
  \tilde\psi)(-\Delta\tilde u - \tilde f) = 0.$$

**Generalization.** The source also assumes $u \in C(\overline\Omega)$. The relations in
$\Omega$ do not need it.

The proof is that of the source. The choice $v = u + \varphi$ with
$0 \le \varphi \in C_0^\infty(\Omega)$ in (11.1.7) and an integration by parts give $\int_\Omega
(-\Delta\tilde u - \tilde f) \varphi \, dx \ge 0$, hence $-\Delta\tilde u - \tilde f \ge 0$ by
the fundamental lemma of the calculus of variations
(`nonneg_on_of_forall_integral_mul_testFunction_nonneg`). Where
$\tilde u(x_0) > \tilde\psi(x_0)$, both $v = u \pm \delta\varphi$ are admissible for $\varphi$
supported in a neighbourhood of $x_0$ on which $\tilde u > \tilde\psi + \delta$; so
$-\Delta\tilde u - \tilde f = 0$ there
(`eqOn_zero_of_forall_integral_mul_testFunction_eq_zero`). -/
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

/-- The space $\mathbb{R}^N$, as local notation. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- Let $\sigma$ be the surface measure of the boundary data, a finite measure. For
$k \in L^2(\sigma)$,
$$\int |k| \, d\sigma \le \|1\|_{L^2(\sigma)} \|k\|_{L^2(\sigma)}.$$

This is Hölder's inequality with $p = 2$
(`MeasureTheory.integral_norm_rpow_sub_one_mul_norm_le`). -/
theorem integral_abs_le_mul_norm (k : Lp ℝ 2 B.σ) :
    ∫ x, |k x| ∂B.σ ≤ (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal * ‖k‖ := by
  have h := MeasureTheory.integral_norm_rpow_sub_one_mul_norm_le (p := 2) ENNReal.ofNat_ne_top
    (Lp.memLp k) (memLp_const (μ := B.σ) (1 : ℝ))
  have h2 : ((2 : ℝ≥0∞).toReal - 1) = 1 := by norm_num
  simp only [h2, Real.rpow_one, norm_one, mul_one, Real.norm_eq_abs] at h
  rw [Lp.norm_def, mul_comm]
  exact h

/-- The map $k \mapsto \int |k| \, d\sigma$ is Lipschitz on $L^2(\sigma)$ with constant
$\|1\|_{L^2(\sigma)}$. -/
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

/-- The friction functional of Example 11.1.2 of [han2009theoretical] on $V = H^1(\Omega)$, for
$g \in \mathbb{R}$:
$$j(v) = g \int_\Gamma |\gamma v| \, d\sigma,$$
where $\sigma$ is the surface measure on $\Gamma$ and $\gamma : H^1(\Omega) \to L^2(\sigma)$ is
the trace.

The source writes $g \int_\Gamma |v| \, ds$. The trace is `𝒯.traceL 2` of the boundary data; it
exists on a bounded $C^1$ domain (`IsContDiffDomain.traceFamily`) and on a polygon without slits
(`Triangulation.traceFamily`). -/
noncomputable def frictionFunctional (g : ℝ) (v : SobolevEuclidean N 1 2 Ω) : ℝ :=
  g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ

/-- The friction functional is $j(v) = g \int |\gamma v| \, d\sigma$. -/
theorem frictionFunctional_apply (g : ℝ) (v : SobolevEuclidean N 1 2 Ω) :
    frictionFunctional B 𝒯 g v = g * ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ :=
  rfl

/-- The friction functional depends only on the trace: if $\gamma v = \gamma w$, then $j(v) = j(w)$.
-/
theorem frictionFunctional_eq_of_traceL_eq (g : ℝ) {v w : SobolevEuclidean N 1 2 Ω}
    (h : 𝒯.traceL 2 ENNReal.ofNat_ne_top v = 𝒯.traceL 2 ENNReal.ofNat_ne_top w) :
    frictionFunctional B 𝒯 g v = frictionFunctional B 𝒯 g w := by
  simp only [frictionFunctional, h]

/-- The friction functional satisfies $j(0) = 0$. -/
theorem frictionFunctional_zero (g : ℝ) : frictionFunctional B 𝒯 g 0 = 0 := by
  simp only [frictionFunctional, map_zero]
  rw [integral_congr_ae ((Lp.coeFn_zero ℝ 2 B.σ).mono fun x hx ↦ by rw [hx, Pi.zero_apply,
    abs_zero]), integral_zero, mul_zero]

/-- The friction functional satisfies $j(2u) = 2 j(u)$. -/
theorem frictionFunctional_two_smul (g : ℝ) (u : SobolevEuclidean N 1 2 Ω) :
    frictionFunctional B 𝒯 g ((2 : ℝ) • u) = 2 * frictionFunctional B 𝒯 g u := by
  simp only [frictionFunctional, map_smul]
  rw [integral_congr_ae ((Lp.coeFn_smul (2 : ℝ) (𝒯.traceL 2 ENNReal.ofNat_ne_top u)).mono
    fun x hx ↦ by rw [hx, Pi.smul_apply, smul_eq_mul, abs_mul, abs_two]), integral_const_mul]
  ring

/-- For $g \ge 0$ and $u, w \in H^1(\Omega)$, the friction functional satisfies $j(u + w) - j(u) \le
g \int |\gamma w| \, d\sigma$. -/
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

/-- The friction functional is continuous on $H^1(\Omega)$.

The map $k \mapsto \int |k| \, d\sigma$ is Lipschitz on $L^2(\sigma)$, and the trace is bounded. -/
theorem continuous_frictionFunctional (g : ℝ) : Continuous (frictionFunctional B 𝒯 g) :=
  continuous_const.mul
    ((lipschitzWith_integral_abs B).continuous.comp (𝒯.traceL 2 ENNReal.ofNat_ne_top).continuous)

/-- For $g \ge 0$, the friction functional is convex on $H^1(\Omega)$.

The absolute value is convex and the trace is linear. -/
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

/-- The energy (11.1.12) of [han2009theoretical] of the simplified friction problem on
$V = H^1(\Omega)$, for $g \in \mathbb{R}$ and $f \in L^2(\Omega)$:
$$E(v) = \int_\Omega \left( \frac12 (|\nabla v|^2 + v^2) - f v \right) dx + g \int_\Gamma |v| \,
  ds.$$

It is the energy $\frac12 a(v, v) - \ell(v)$ of the form $a(u, v) = \int_\Omega (\nabla u \cdot
\nabla v + u v) \, dx$ (`Elliptic.laplaceForm Ω`) and the functional
$\ell(v) = \int_\Omega f v \, dx$, plus the friction functional $j$.
`AtkinsonHan.Chapter11.frictionEnergy_apply` gives the integrals. -/
noncomputable def frictionEnergy (g : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : SobolevEuclidean N 1 2 Ω → ℝ :=
  (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) + frictionFunctional B 𝒯 g

/-- The energy (11.1.12) is
$$E(v) = \int_\Omega \left( \frac12 \Big( \sum_i (\partial_i v)^2 + v^2 \Big) - f v \right) dx +
  g \int |\gamma v| \, d\sigma \qquad \text{for } v \in H^1(\Omega).$$
-/
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

/-- The bilinear form of Example 11.1.2 of [han2009theoretical] on $H^1(\Omega)$:
$$a(u, v) = \int_\Omega (\nabla u \cdot \nabla v + u v) \, dx.$$

It is `Elliptic.laplaceForm Ω` read as a bilinear form of Section 8.3, so that Theorems 11.2.2
and 11.3.9 apply to the friction problem. -/
noncomputable def frictionBilinForm : BilinForm (SobolevEuclidean N 1 2 Ω) :=
  BilinForm.ofCLM (Elliptic.laplaceForm Ω)

/-- The form `AtkinsonHan.Chapter11.frictionBilinForm` is `Elliptic.laplaceForm Ω`. -/
theorem frictionBilinForm_apply (u v : SobolevEuclidean N 1 2 Ω) :
    frictionBilinForm (Ω := Ω) u v = Elliptic.laplaceForm Ω u v := rfl

/-- The form of Example 11.1.2 satisfies $|a(u, v)| \le \|u\|_{1,\Omega} \|v\|_{1,\Omega}$, so it is
bounded with constant $1$ (`Elliptic.laplaceForm_isBoundedWith_one`). -/
theorem frictionBilinForm_isBoundedWith : (frictionBilinForm (Ω := Ω)).IsBoundedWith 1 :=
  fun u v ↦ by
    rw [frictionBilinForm_apply, ← Real.norm_eq_abs]
    exact Elliptic.laplaceForm_isBoundedWith_one Ω u v

/-- The form of Example 11.1.2 is $V$-elliptic with constant $1$: $a(v, v) \ge \|v\|_{1,\Omega}^2$,
since it is the inner product of $H^1(\Omega)$ (`Elliptic.laplaceForm_isCoerciveWith_one`). -/
theorem frictionBilinForm_isEllipticWith : (frictionBilinForm (Ω := Ω)).IsEllipticWith 1 :=
  fun v ↦ Elliptic.laplaceForm_isCoerciveWith_one Ω v

/-- The form of Example 11.1.2 is symmetric: $a(u, v) = a(v, u)$. -/
theorem frictionBilinForm_isSymm : LinearMap.BilinForm.IsSymm (frictionBilinForm (Ω := Ω)) := by
  unfold frictionBilinForm
  rw [BilinForm.isSymm_ofCLM_iff]
  intro u v
  have h := Elliptic.laplaceForm_isHermitian Ω u v
  rw [conj_trivial] at h
  exact h

/-- The variational inequality (11.1.13) at one element $v$, in two forms. For $g \in \mathbb{R}$,
$f \in L^2(\Omega)$ and $u, v \in H^1(\Omega)$, the inequality
$$\int_\Omega f (v - u) \, dx \le \int_\Omega \big( \nabla u \cdot \nabla(v - u) + u (v - u)
  \big) \, dx + g \int_\Gamma (|v| - |u|) \, ds$$
holds if and only if $\ell(v - u) \le a(u, v - u) + j(v) - j(u)$. Here the form $a$ is
`Elliptic.laplaceForm Ω`, and the functional is `Elliptic.load Ω f`. -/
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

/-- **Example 11.1.2** of [han2009theoretical] (the simplified friction problem), the variational
inequality (11.1.13). Let $\Omega \subseteq \mathbb{R}^N$ be open with boundary data: a surface
measure $\sigma$ on $\Gamma = \partial\Omega$ and a trace
$\gamma : H^1(\Omega) \to L^2(\sigma)$. Let $g > 0$, $f \in L^2(\Omega)$ and
$u \in V = H^1(\Omega)$. Then $u$ minimizes the energy (11.1.12),
$$E(v) = \int_\Omega \left( \frac12 (|\nabla v|^2 + v^2) - f v \right) dx + g \int_\Gamma |v| \,
  ds,$$
over $V$ if and only if
$$\int_\Omega \big( \nabla u \cdot \nabla(v - u) + u (v - u) \big) \, dx + g \int_\Gamma (|v| -
  |u|) \, ds \ge \int_\Omega f (v - u) \, dx \qquad \text{for all } v \in V.$$

**Reading.** The source assumes a Lipschitz boundary. Here the boundary enters through the
boundary data `B : BoundaryData Ω` and the trace `𝒯 : B.TraceFamily`, which exist on a bounded
$C^1$ domain (`IsContDiffDomain.traceFamily`) and on a polygon without slits
(`Triangulation.traceFamily`).

The source leaves the equivalence as Exercise 11.1.2. It is Theorem 11.2.1
(`isMinOn_energy_add_iff`) with $K = V$, for the differentiable convex part
$\frac12 a(v, v) - \ell(v)$ of the energy and the convex continuous friction functional $j$
(`AtkinsonHan.Chapter11.convexOn_frictionFunctional`,
`AtkinsonHan.Chapter11.continuous_frictionFunctional`). The pointwise form (11.1.14)–(11.1.15)
is `AtkinsonHan.Chapter11.example_11_1_2_pointwise`. -/
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

/-! ### Tools for the pointwise form -/

open Laplacian in
/-- Green's formula for the form of Example 11.1.2. Let $u \in H^1(\Omega)$ agree almost everywhere
on $\Omega$ with a function $\tilde u$ of class $C^2(\overline\Omega)$, and let $G$ be
continuous on $\overline\Omega$ and equal to the derivative of $\tilde u$ on $\Omega$. Let
$W \in H^1(\Omega)$ agree almost everywhere on $\Omega$ with a $C^1$ function $\psi$ on
$\mathbb{R}^N$. Then
$$a(u, W) = \int_\Gamma G(\nu) \, \psi \, d\sigma + \int_\Omega (-\Delta\tilde u + \tilde u)
  \psi \, dx,$$
where $a(u, W) = \int_\Omega (\nabla u \cdot \nabla W + u W) \, dx$ and $\nu$ is the outward
normal.

The function $G$ gives the boundary values of $\nabla\tilde u$. The identity is
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
    simp only [hxU, hxW, hUx, hWx, EuclideanSpace.inner_gradient_eq_sum]
  have hR : ∫ x in (Ω : Set 𝔼), (-Δ ũ x + ũ x) * ψ x
      = (∫ x in (Ω : Set 𝔼), -(Δ ũ x * ψ x)) + ∫ x in (Ω : Set 𝔼), ũ x * ψ x := by
    have hI₃' : Integrable (fun x ↦ -(Δ ũ x * ψ x)) (volume.restrict (Ω : Set 𝔼)) := hI₃.neg
    rw [← integral_add hI₃' hI₂]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    ring
  rw [hL, hR, integral_neg]
  linarith

/-- Let $g \ge 0$ and $h : \mathbb{R}^N \to \mathbb{R}$, and let $u \in H^1(\Omega)$ satisfy
$$0 \le \int_\Gamma h \, \gamma(v - u) \, d\sigma + j(v) - j(u) \qquad \text{for all } v \in
  H^1(\Omega).$$
Then $|\int_\Gamma h \psi \, d\sigma| \le g \int_\Gamma \psi \, d\sigma$ for every smooth,
compactly supported $\psi \ge 0$ on $\mathbb{R}^N$.

The proof tests with $v = u \pm W$, where $W$ is the element of $H^1(\Omega)$ with function
$\psi$, whose trace is $\psi$ (`BoundaryData.TraceFamily.traceL_ae_eq`), and uses the bound
$j(u + w) - j(u) \le g \int |\gamma w| \, d\sigma$. -/
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

/-- Assume that every open set that meets $\Gamma$ has positive surface measure. Let $g \ge 0$, let
$h$ be continuous on $\Gamma$, and let $u \in H^1(\Omega)$ satisfy
$$0 \le \int_\Gamma h \, \gamma(v - u) \, d\sigma + j(v) - j(u) \qquad \text{for all } v \in
  H^1(\Omega).$$
Then $|h(x)| \le g$ for every $x \in \Gamma$.

Where $|h(x_0)| > g$, a bump function on the boundary
(`BoundaryData.exists_bump_lt_integral_mul`) contradicts
`AtkinsonHan.Chapter11.abs_integral_mul_le_of_forall_le`. -/
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
    obtain ⟨ψ, hψ, hψc, hψ0, -, hψi⟩ := B.exists_bump_lt_integral_mul hpos hc.neg hx₀ (c := g)
      (by simp only [Pi.neg_apply]; linarith)
    have := abs_integral_mul_le_of_forall_le B 𝒯 hg hvi hψ hψc hψ0
    simp only [Pi.neg_apply, neg_mul, integral_neg] at hψi
    rw [abs_le] at this
    linarith [this.1]
  · by_contra hlt
    push Not at hlt
    obtain ⟨ψ, hψ, hψc, hψ0, -, hψi⟩ := B.exists_bump_lt_integral_mul hpos hc hx₀ (c := g) hlt
    have := abs_integral_mul_le_of_forall_le B 𝒯 hg hvi hψ hψc hψ0
    rw [abs_le] at this
    linarith [this.2]

/-- Assume that every open set that meets $\Gamma$ has positive surface measure. Let $h$ be
continuous on $\Gamma$ with $|h| \le g$ on $\Gamma$, let $u \in H^1(\Omega)$ have trace
$\gamma u = \tilde u$ $\sigma$-almost everywhere for a function $\tilde u$ continuous on
$\overline\Omega$, and let
$$0 \le \int_\Gamma h \, \gamma(v - u) \, d\sigma + j(v) - j(u) \qquad \text{for all } v \in
  H^1(\Omega).$$
Then $h(x) \tilde u(x) + g |\tilde u(x)| = 0$ for every $x \in \Gamma$.

The choices $v = 0$ and $v = 2u$ give $\int_\Gamma (h\tilde u + g |\tilde u|) \, d\sigma = 0$.
The integrand is nonnegative because $|h| \le g$, and it is continuous, so a bump function shows
that it vanishes on $\Gamma$. -/
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
  have hh : MemLp h 2 B.σ := (B.memLp_top_of_continuousOn_frontier hc).mono_exponent le_top
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
  obtain ⟨ψ, hψ, -, -, hψ1, hψi⟩ := B.exists_bump_lt_integral_mul hpos hk hx₀ (c := 0) hgt
  rw [zero_mul] at hψi
  have hIk : Integrable (fun x ↦ h x * ũ x + g * |ũ x|) B.σ :=
    (B.memLp_top_of_continuousOn_frontier hk).integrable le_top
  have hIkψ : Integrable (fun x ↦ (h x * ũ x + g * |ũ x|) * ψ x) B.σ :=
    (B.memLp_top_of_continuousOn_frontier hk).integrable_mul
      (B.memLp_of_continuous hψ.continuous 1)
  have hmono : ∫ x, (h x * ũ x + g * |ũ x|) * ψ x ∂B.σ
      ≤ ∫ x, (h x * ũ x + g * |ũ x|) ∂B.σ := by
    refine integral_mono_ae hIkψ hIk ?_
    filter_upwards [B.ae_mem_frontier] with x hx
    exact mul_le_of_le_one_right (hk0 x hx) (hψ1 x)
  linarith

end Friction

/-! ### Example 11.1.2: the pointwise form (11.1.14)–(11.1.15) on a bounded $C^1$ domain -/

section FrictionPointwise

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The space $\mathbb{R}^{d+1}$, as local notation. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

open Laplacian in
/-- The identity behind (11.1.15). Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$
domain, with surface measure $\sigma$, outward normal $\nu$ and trace $\gamma$. Let
$u \in H^1(\Omega)$ agree almost everywhere on $\Omega$ with a function $\tilde u$ of class
$C^2(\overline\Omega)$, let $G$ be continuous on $\overline\Omega$ and equal to the derivative
of $\tilde u$ on $\Omega$, and let $-\Delta\tilde u + \tilde u = f$ almost everywhere on
$\Omega$ for some $f \in L^2(\Omega)$. Then for every $W \in H^1(\Omega)$
$$a(u, W) - \ell(W) = \int_\Gamma G(\nu) \, \gamma W \, d\sigma,$$
where $a(u, W) = \int_\Omega (\nabla u \cdot \nabla W + u W) \, dx$ and
$\ell(W) = \int_\Omega f W \, dx$.

Green's formula (`AtkinsonHan.Chapter11.laplaceForm_eq_integral_add_of_contDiffOnClosure`) gives
the identity for smooth $W$. Both sides are continuous in $W$, and smooth functions are dense in
$H^1(\Omega)$ (`IsContDiffDomain.hasSmoothDensity`). -/
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
    ((hΩ.boundaryData hb).memLp_top_of_continuousOn_frontier hc).mono_exponent le_top
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
/-- **Example 11.1.2** of [han2009theoretical], the pointwise form (11.1.14)–(11.1.15). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain, with surface measure $\sigma$ on
$\Gamma = \partial\Omega$, outward normal $\nu$ and trace $\gamma$. Let $g > 0$ and
$f \in L^2(\Omega)$, and let $u \in H^1(\Omega)$ satisfy the variational inequality (11.1.13).
Let $u$ agree almost everywhere on $\Omega$ with a function $\tilde u$ that is continuous on
$\overline\Omega$ and of class $C^2(\overline\Omega)$, and let $G$ be continuous on
$\overline\Omega$ and equal to the derivative of $\tilde u$ on $\Omega$, so that
$\partial\tilde u / \partial\nu = G(\nu)$ is defined on $\Gamma$. Then
$$-\Delta\tilde u + \tilde u = f \quad \text{a.e. in } \Omega, \qquad (11.1.14)$$
and at every point of $\Gamma$
$$\left| \frac{\partial\tilde u}{\partial\nu} \right| \le g, \qquad \frac{\partial\tilde
  u}{\partial\nu} \, \tilde u + g |\tilde u| = 0. \qquad (11.1.15)$$

**Reading.** The source assumes a Lipschitz boundary and a smooth solution (Exercise 11.1.3).
Here the domain is $C^1$, which is where the library has the surface measure, the outward normal
and the trace, and a smooth solution is one with the representative $\tilde u$ above. The source
states (11.1.15) at the points of $\Gamma$ where the outward normal is defined; on a $C^1$
domain this is every point of $\Gamma$.

The proof is that of the source. The choice $v = u \pm \varphi$ with
$\varphi \in C_c^\infty(\Omega)$, whose trace vanishes
(`BoundaryData.TraceFamily.traceL_eq_zero_of_mem_zero`), gives the weak equation and hence
(11.1.14) (`Elliptic.laplacian_ae_eq_of_forall_testFunction`). Green's formula
(`AtkinsonHan.Chapter11.laplaceForm_sub_load_eq_integral`) turns (11.1.13) into $\int_\Gamma
(\partial\tilde u / \partial\nu)(\gamma v - \gamma u) \, d\sigma + g \int_\Gamma (|\gamma v| -
|\gamma u|) \, d\sigma \ge 0$ for all $v \in H^1(\Omega)$. The normal derivative is continuous
on $\Gamma$ (`IsContDiffDomain.continuousOn_outwardNormal`) and every open set that meets
$\Gamma$ has positive surface measure (`IsContDiffDomain.boundaryMeasure_pos_of_isOpen`), so
`AtkinsonHan.Chapter11.abs_le_of_forall_le` gives the first relation of (11.1.15) and
`AtkinsonHan.Chapter11.mul_add_abs_eq_zero_of_forall_le` the second. -/
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
