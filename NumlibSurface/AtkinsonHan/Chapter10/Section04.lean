/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.CurvilinearLaplacian
import Numlib.Variational.Galerkin
import Numlib.FiniteElement.Triangle
import NumlibSurface.AtkinsonHan.Chapter09.Section01
import NumlibSurface.AtkinsonHan.Chapter10.Section03

/-!
# Atkinson and Han, Section 10.4: Convergence and error estimates

This module formalizes Section 10.4 of [han2009theoretical]. The section combines the abstract
theory of Chapter 9 (the Lax–Milgram lemma and Céa's inequality) with the interpolation estimates of
Section 10.3, for the finite element method for a second-order elliptic problem on a polygon
$\Omega \subseteq \mathbb{R}^2$. On a regular family of triangulations with a $\mathbb{P}_k$
element, the Galerkin solution $u_h$ satisfies $\|u - u_h\|_V \le c h^k |u|_{k+1,\Omega}$ and
converges to the solution $u$ (Theorem 10.4.1). Example 10.4.2 applies this to the Dirichlet problem
for the Poisson equation. The Aubin–Nitsche lemma (Theorem 10.4.3) bounds the error in a weaker norm
through the solutions $\varphi_g$ of a dual problem:
$$\|u - u_h\|_H \le M \|u - u_h\|_V \sup_{g \ne 0} \frac{1}{\|g\|_H} \inf_{v_h \in V_h}
  \|\varphi_g - v_h\|_V.$$
Exercise 10.4.5 writes the Laplacian in polar and in spherical coordinates.

The finite element results specialize `Numlib.FiniteElement.Triangle`, on the triangulations of
`Numlib.Geometry.Triangulation` and the finite element spaces of
`Numlib.Analysis.Sobolev.Triangulation`. The Aubin–Nitsche lemma specializes the duality estimates
of `Numlib.Variational.Galerkin`, and Exercise 10.4.5 specializes
`Numlib.Analysis.Calculus.CurvilinearLaplacian`.

## Main definitions

* Theorem 10.4.3, `AtkinsonHan.DualProblem`: the dual problem, $\varphi \in V$ with
  $a(v, \varphi) = (\iota v, g)_H$ for all $v \in V$.
* Example 10.4.2, `AtkinsonHan.Chapter10.poissonForm`: the bilinear form $a(u, v) = \int_\Omega
  \nabla u \cdot \nabla v \, dx$ on $H_0^1(\Omega)$.
* Example 10.4.2, `AtkinsonHan.Chapter10.poissonLoad`: the linear functional
  $\ell(v) = \int_\Omega f v \, dx$ on $H_0^1(\Omega)$.

## Main results

* Theorem 10.4.1, `AtkinsonHan.Chapter10.theorem_10_4_1`: the error estimate (10.4.4),
  $\|u - u_h\|_V \le c h^k |u|_{k+1,\Omega}$.
* Theorem 10.4.1, `AtkinsonHan.Chapter10.theorem_10_4_1_tendsto`: $\|u - u_h\|_V \to 0$ if smooth
  functions are dense in $V$.
* Example 10.4.2, `AtkinsonHan.Chapter10.example_10_4_2`: the Dirichlet problem for the Poisson
  equation and its finite element approximation have unique solutions, and $\|u - u_h\|_{1,\Omega}
  \le c h^k \|u\|_{k+1,\Omega}$.
* Theorem 10.4.3, `AtkinsonHan.Chapter10.theorem_10_4_3`: the Aubin–Nitsche lemma (10.4.5).
* Theorem 10.4.3, `AtkinsonHan.Chapter10.norm_le_of_dualProblem`: the dual solutions satisfy
  $\|\varphi_g\|_V \le (\|\iota\| / c_0) \|g\|_H$, so the supremum in (10.4.5) is finite.
* Corollary 10.4.4, `AtkinsonHan.Chapter10.corollary_10_4_4_abstract`: if for every $g \in H$ some
  solution $\varphi_g$ of the dual problem lies within $\delta \|g\|_H$ of $V_h$, then
  $\|u - u_h\|_H \le M \delta \|u - u_h\|_V$.
* Exercise 10.4.5, `AtkinsonHan.Chapter10.exercise_10_4_5_polar`: the Laplacian in polar coordinates
  on $\mathbb{R}^2$.
* Exercise 10.4.5, `AtkinsonHan.Chapter10.exercise_10_4_5_spherical`: the Laplacian in spherical
  coordinates on $\mathbb{R}^3$.

## Implementation notes

* A triangulation is a `Triangulation Ω`, and a regular family is
  `AtkinsonHan.Chapter10.IsRegularFamily` for the collections of open elements. A finite element is
  given by nodes and shape functions on the reference triangle, and $\Pi_h$ is
  `Triangulation.globalInterp`. The finite element spaces are `Triangulation.polySpace`
  ($X_h \subseteq H^1(\Omega)$) and `Triangulation.polySpaceZero` ($V_h \subseteq H_0^1(\Omega)$,
  the continuous piecewise polynomials that vanish on $\partial\Omega$).
* The membership $V_h \subseteq H_0^1(\Omega)$ needs no trace theorem: a continuous function in
  $H^1(\Omega)$ that vanishes on $\partial\Omega$ lies in $H_0^1(\Omega)$ on every open set, by
  Theorem 9.17 of [brezis2011functional], (i) implies (ii). The polygon enters through the
  hypothesis that $\partial\Omega$ is a union of element edges
  (`Triangulation.FrontierSubsetEdges`), so that an interpolant that vanishes at the boundary nodes
  vanishes on $\partial\Omega$.
* The space $V$ of Theorem 10.4.1 is a subspace of `SobolevEuclidean 2 1 2 Ω`, the space
  $H^1(\Omega)$ with the norm built from multi-indices. A function $u \in V$ is related to a
  function $\tilde u$ on $\mathbb{R}^2$ by `SobolevMultiIndex.fn u =ᵐ ũ` on $\Omega$, and the
  seminorm $|\tilde u|_{k+1,\Omega}$ is the tensor seminorm `sobolevSeminorm` of Section 10.3.
  `FiniteElement.exists_norm_le_sobolevNorm` compares the two norms on $H^1(\Omega)$.
* Theorem 10.4.1 and the estimate of Example 10.4.2 are
  `FiniteElement.norm_sub_le_of_isGalerkinSolution`,
  `FiniteElement.tendsto_norm_sub_of_isGalerkinSolution` and
  `FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm`. These are stated for the
  backbone's `SesqForm` and `IsGalerkinSolution`; the form `AtkinsonHan.BilinForm` and the problem
  `AtkinsonHan.GalerkinProblem` of the source are connected to them by
  `AtkinsonHan.BilinForm.toCLM`.
* In Theorem 10.4.3 the supremum over the data $g \in H$ and the infimum over $V_h$ are those of the
  source. Both are real suprema and infima: the quantities are nonnegative, and they are bounded
  above by `AtkinsonHan.Chapter10.norm_le_of_dualProblem`.

## Deviations from the source

* **Theorem 10.4.1** (reading). The constant $c$ depends on an upper bound $H$ on the mesh
  parameters, as in Corollary 10.3.7, and $u \in H^{k+1}(\Omega)$ is taken on a representative that
  is continuous up to the boundary. See `AtkinsonHan.Chapter10.theorem_10_4_1`.
* **Theorem 10.4.1** (generalization). The spaces $V_h$ are any subspaces of $V$ that contain the
  interpolant $\Pi_h u$, not only the finite element spaces. See
  `AtkinsonHan.Chapter10.theorem_10_4_1`.
* **Theorem 10.4.1**, convergence (reading). The density of smooth functions in $V$, which the
  argument of the source uses, is a hypothesis. See `AtkinsonHan.Chapter10.theorem_10_4_1_tendsto`.
* **Example 10.4.2** (reading). The regularity $u \in H^{k+1}(\Omega)$ is taken on a representative
  $\tilde u$ that is continuous up to the boundary, with $\tilde u = 0$ on $\Gamma$ as a hypothesis.
  The domain is bounded, $\Omega \subseteq B(0, R)$, and $\partial\Omega$ is a union of element
  edges. See `AtkinsonHan.Chapter10.example_10_4_2`.
* **Theorem 10.4.3** (generalization). The source takes $V \subseteq H^1(\Omega)$ and
  $H = L^2(\Omega)$. The library takes real inner product spaces $V$ and $H$ and a continuous linear
  map $\iota : V \to H$ in place of the embedding. See `AtkinsonHan.Chapter10.theorem_10_4_3`.
* **Exercise 10.4.5** (reading). The source writes operator identities. The library states them at
  one point, for a $C^2$ function, with the coordinate derivatives as derivatives along the
  coordinate curves. See `AtkinsonHan.Chapter10.exercise_10_4_5_polar`.

## Not formalized

* **Corollary 10.4.4** in its stated form, with the $H^2$ regularity hypothesis (10.4.9), and
  **(10.4.11)**. The library does not have the regularity of the Dirichlet problem on a convex
  polygon; `Elliptic.regularity_dirichlet` proves it on $C^2$ domains. The abstract form is
  `AtkinsonHan.Chapter10.corollary_10_4_4_abstract`.
* **Exercises 10.4.1–10.4.4 and 10.4.6.** Each is posed on a specific domain.
-/

open scoped Laplacian

namespace AtkinsonHan

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

/-- The **dual problem** of Theorem 10.4.3 of [han2009theoretical]. Let $V$ and $H$ be real inner
product spaces, let $a$ be a bilinear form on $V$, let $\iota : V \to H$ be continuous and
linear, and let $g \in H$. An element $\varphi \in V$ solves the dual problem for $g$ if
$$a(v, \varphi) = (\iota v, g)_H \qquad \text{for all } v \in V.$$

It is the variational problem for the transposed form $a(\cdot, \cdot)^T$. For a bounded,
$V$-elliptic form on a complete $V$, the Lax–Milgram lemma (Theorem 8.3.4) applied to $a^T$
gives a unique solution. -/
def DualProblem (a : BilinForm V) (ι : V →L[ℝ] H) (g : H) (φ : V) : Prop :=
  ∀ v : V, a v φ = inner ℝ (ι v) g

namespace Chapter10

variable {a : BilinForm V} {ℓ : StrongDual ℝ V} {M c₀ δ : ℝ} {Vh : Submodule ℝ V} {u uh : V}

/-- For $w \in V$ and a subspace $K \subseteq V$, the distances $\|w - v\|$, $v \in K$, are bounded
below by $0$. -/
private theorem bddBelow_norm_sub (w : V) (K : Submodule ℝ V) :
    BddBelow (Set.range fun v : K => ‖w - (v : V)‖) :=
  ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩

/-- Let $a$ be a bilinear form on $V$ with $a(v, v) \ge c_0 \|v\|^2$ for all $v$, where $c_0 > 0$,
let $\iota : V \to H$ be continuous and linear, and let $\varphi_g$ solve the dual problem for
$g \in H$. Then
$$\|\varphi_g\| \le \frac{\|\iota\|}{c_0} \|g\|.$$

This bound makes the supremum in (10.4.5) finite. -/
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

/-- The supremum in (10.4.5) is finite: the dual solutions are approximated from $V_h$ at least as
well as by $0$, and their norms are at most $(\|\iota\| / c_0) \|g\|$. -/
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

/-- **Theorem 10.4.3** of [han2009theoretical] (the Aubin–Nitsche lemma, (10.4.5)). Let $V$ and $H$
be real inner product spaces and $\iota : V \to H$ continuous and linear. Let $a$ be a bilinear
form on $V$ with $|a(u, v)| \le M \|u\| \|v\|$ and $a(v, v) \ge c_0 \|v\|^2$ for all $u, v$,
where $c_0 > 0$, and let $\ell$ be a continuous linear functional on $V$. Let $u \in V$ satisfy
$a(u, v) = \ell(v)$ for all $v \in V$, let $u_h$ be the Galerkin solution on a subspace
$V_h \subseteq V$, and for each $g \in H$ let $\varphi_g$ solve the dual problem
$a(v, \varphi_g) = (\iota v, g)_H$ for all $v \in V$. Then
$$\|\iota(u - u_h)\|_H \le M \|u - u_h\|_V \sup_{g \in H,\, g \ne 0} \frac{1}{\|g\|_H} \inf_{v_h
  \in V_h} \|\varphi_g - v_h\|_V.$$

**Generalization.** The source takes $V \subseteq H^1(\Omega)$ and $H = L^2(\Omega)$, with
$\iota$ the embedding. The proof uses only that $\iota$ is continuous and linear.

The duality argument is `norm_map_sq_le_of_dual`. Ellipticity is used only to show that the
supremum is finite. If $H = \{0\}$, the supremum is over the empty set and has the value $0$. -/
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

/-- **Corollary 10.4.4** of [han2009theoretical], with the regularity hypothesis made abstract. Let
$V$, $H$, $\iota$, $\ell$, $u$, $V_h$ and $u_h$ be as in Theorem 10.4.3, with
$|a(u, v)| \le M \|u\| \|v\|$, and let $\delta \ge 0$. Assume that for every $g \in H$ the dual
problem has a solution $\varphi_g$ with $\operatorname{dist}(\varphi_g, V_h) \le \delta
\|g\|_H$. Then
$$\|\iota(u - u_h)\|_H \le M \delta \|u - u_h\|_V.$$

In the source, $\delta = c h$ follows from the $H^2$ regularity bound (10.4.9) and the
interpolation error estimate. The library does not have the regularity bound, so the
approximation property is the hypothesis. The distance is `Metric.infDist`, as in the backbone's
`norm_map_le_of_dual_approx`; `AtkinsonHan.Chapter09.iInf_norm_sub_eq_infDist` identifies it
with $\inf_{v_h \in V_h} \|\varphi_g - v_h\|_V$. Ellipticity is not needed. -/
theorem corollary_10_4_4_abstract (hM : a.IsBoundedWith M) (hδ : 0 ≤ δ) (ι : V →L[ℝ] H)
    (hu : ∀ v, a u v = ℓ v) (huh : GalerkinProblem a ℓ Vh uh)
    (hdual : ∀ g : H, ∃ φ : V, DualProblem a ι g φ ∧
      Metric.infDist φ (Vh : Set V) ≤ δ * ‖g‖) :
    ‖ι (u - uh)‖ ≤ M * δ * ‖u - uh‖ :=
  norm_map_le_of_dual_approx (BilinForm.isBoundedWith_toCLM hM) hδ ι
    (fun _ hv => Chapter09.galerkin_orthogonality hM hu huh hv) hdual


/-!
### Exercise 10.4.5: the Laplacian in polar and in spherical coordinates

The exercise is the chain rule for a $C^2$ function. The plane and space are
`EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`, and $\Delta$ is
`InnerProductSpace.laplacian`. The identities are `Curvilinear.laplacian_eq_polar` and
`Curvilinear.laplacian_eq_spherical` of the backbone for the standard orthonormal basis.

The source writes the two identities as identities of operators. Here they hold at one point, and
each coordinate derivative, such as $\partial / \partial r$, is the derivative of $f$ along the
coordinate curve through that point.
-/

/-- The point of $\mathbb{R}^2$ with polar coordinates $(r, \theta)$: $x_1 = r \cos\theta$ and
$x_2 = r \sin\theta$. -/
noncomputable def polarPt (r θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[r * Real.cos θ, r * Real.sin θ]

/-- The point `AtkinsonHan.Chapter10.polarPt r θ` is the backbone's `Curvilinear.polarPoint` for the
standard basis of $\mathbb{R}^2$. -/
theorem polarPt_eq (r θ : ℝ) :
    polarPt r θ = Curvilinear.polarPoint (EuclideanSpace.basisFun (Fin 2) ℝ) r θ := by
  ext i
  fin_cases i <;> simp [polarPt, Curvilinear.polarPoint, EuclideanSpace.basisFun_apply]

/-- **Exercise 10.4.5** of [han2009theoretical], in $\mathbb{R}^2$. Let
$f : \mathbb{R}^2 \to \mathbb{R}$ be $C^2$, and let $x_1 = r \cos\theta$, $x_2 = r \sin\theta$
with $r \ne 0$. Then
$$\Delta f = \frac{\partial^2 f}{\partial r^2} + \frac{1}{r} \frac{\partial f}{\partial r} +
  \frac{1}{r^2} \frac{\partial^2 f}{\partial \theta^2}$$
at the point $(x_1, x_2)$.

**Reading.** The source writes an identity of operators. Here it holds at each point, and
$\partial f / \partial r$ and $\partial f / \partial \theta$ are the derivatives of
$s \mapsto f(s \cos\theta, s \sin\theta)$ at $r$ and of $\psi \mapsto f(r \cos\psi, r \sin\psi)$
at $\theta$. -/
theorem exercise_10_4_5_polar {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ 2 f)
    {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    Δ f (polarPt r θ)
      = deriv (deriv fun s : ℝ => f (polarPt s θ)) r
        + r⁻¹ * deriv (fun s : ℝ => f (polarPt s θ)) r
        + (r ^ 2)⁻¹ * deriv (deriv fun ψ : ℝ => f (polarPt r ψ)) θ := by
  simp only [polarPt_eq]
  simpa using Curvilinear.laplacian_eq_polar _ hf hr θ

/-- The point of $\mathbb{R}^3$ with spherical coordinates $(r, \theta, \varphi)$:
$x_1 = r \cos\theta \sin\varphi$, $x_2 = r \sin\theta \sin\varphi$ and $x_3 = r \cos\varphi$. -/
noncomputable def sphericalPt (r θ φ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[r * Real.cos θ * Real.sin φ, r * Real.sin θ * Real.sin φ, r * Real.cos φ]

/-- The point `AtkinsonHan.Chapter10.sphericalPt r θ φ` is the backbone's
`Curvilinear.sphericalPoint` for the standard basis of $\mathbb{R}^3$. -/
theorem sphericalPt_eq (r θ φ : ℝ) :
    sphericalPt r θ φ = Curvilinear.sphericalPoint (EuclideanSpace.basisFun (Fin 3) ℝ) r θ φ := by
  ext i
  fin_cases i <;> simp [sphericalPt, Curvilinear.sphericalPoint, EuclideanSpace.basisFun_apply]

/-- **Exercise 10.4.5** of [han2009theoretical], in $\mathbb{R}^3$. Let
$f : \mathbb{R}^3 \to \mathbb{R}$ be $C^2$, and let $x_1 = r \cos\theta \sin\varphi$,
$x_2 = r \sin\theta \sin\varphi$, $x_3 = r \cos\varphi$ with $r \ne 0$ and $\sin\varphi \ne 0$.
Then
$$\Delta f = \frac{\partial^2 f}{\partial r^2} + \frac{2}{r} \frac{\partial f}{\partial r} +
  \frac{1}{r^2} \left( \frac{1}{\sin^2\varphi} \frac{\partial^2 f}{\partial \theta^2} +
  \cot\varphi \, \frac{\partial f}{\partial \varphi} + \frac{\partial^2 f}{\partial \varphi^2}
  \right)$$
at the point $(x_1, x_2, x_3)$.

**Reading.** The source writes an identity of operators. Here it holds at each point, and each
coordinate derivative is the derivative of $f$ along the coordinate curve through the point. The
factor $\cot\varphi$ is written $\cos\varphi / \sin\varphi$. -/
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
/-- **Theorem 10.4.1** of [han2009theoretical], the error estimate (10.4.4). Let
$\Omega \subseteq \mathbb{R}^2$ be open, and let $V$ be a subspace of $H^1(\Omega)$ with a
bilinear form $a$ such that $|a(u, v)| \le M \|u\|_V \|v\|_V$ and $a(v, v) \ge c_0 \|v\|_V^2$
for all $u, v \in V$, where $c_0 > 0$. Let $\{\mathcal{T}_h\}$ be a regular family of
triangulations of $\Omega$ (Definition 10.3.6) with mesh parameters at most $H$. Let $k \ge 1$,
and let the finite element have the reference triangle $\hat K$, nodes
$\hat x_i \in \overline{\hat K}$ and $C^1$ shape functions $\hat\varphi_i$, with $\hat\Pi q = q$
on $\hat K$ for every polynomial $q$ of degree at most $k$, and let it be conforming on every
triangulation of the family. Then there is a constant $c \ge 0$ with the following property. Let
$\ell$ be a continuous linear functional on $V$, let $u \in V$ solve $a(u, v) = \ell(v)$ for all
$v \in V$ (10.4.1), and let $u_h$ be the Galerkin solution (10.4.2) on a subspace
$V_h \subseteq V$ for each triangulation. Let $u$ agree almost everywhere on $\Omega$ with a
function $\tilde u \in H^{k+1}(\Omega)$ that is continuous on $\overline\Omega$, and let each
$V_h$ contain the interpolant $\Pi_h \tilde u$. Then
$$\|u - u_h\|_V \le c \, h^k \, |\tilde u|_{k+1,\Omega}$$
for every triangulation of the family, with mesh parameter $h$.

**Reading.** As in Theorem 10.3.9, the constant depends on the bound $H$ on the mesh parameters,
and $u$ is taken on a representative that is continuous up to the boundary.

**Generalization.** The source takes $V_h$ to be the finite element space. The proof uses only
$\Pi_h u \in V_h$. For $V = H^1(\Omega)$ this holds with $V_h = X_h$, the space
`Triangulation.polySpace`. For $V = H_0^1(\Omega)$ it is
`LagrangeElement.exists_mem_polySpaceZero_globalInterp` (Example 10.4.2).

The proof is that of the source: Céa's inequality (10.4.3) with $v_h = \Pi_h u$
(`AtkinsonHan.Chapter09.proposition_9_1_3_le`), and then the interpolation estimate (10.3.13)
with $m = 1$ (`AtkinsonHan.Chapter10.theorem_10_3_9`). The norm of $V$ is compared with the
tensor norm $\|\cdot\|_{1,\Omega}$ of Section 10.3 by
`FiniteElement.exists_norm_le_sobolevNorm`. The statement is
`FiniteElement.norm_sub_le_of_isGalerkinSolution` for the form `a.toCLM`. The convergence is
`AtkinsonHan.Chapter10.theorem_10_4_1_tendsto`. -/
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

/-- **Theorem 10.4.1** of [han2009theoretical], convergence. Let $\Omega$, $V$, $a$, the family
$\{\mathcal{T}_h\}$ and the finite element satisfy the hypotheses of
`AtkinsonHan.Chapter10.theorem_10_4_1`. Let $u \in V$ solve $a(u, v) = \ell(v)$ for all
$v \in V$, and let $u_h$ be the Galerkin solution on a subspace $V_h \subseteq V$ for each
triangulation. Assume that for every $\varepsilon > 0$ there is a $w \in V$ with
$\|u - w\|_V < \varepsilon$ that agrees almost everywhere on $\Omega$ with a function
$\tilde w \in H^{k+1}(\Omega)$ continuous on $\overline\Omega$, such that every $V_h$ contains
an element equal to $\Pi_h \tilde w$ almost everywhere on $\Omega$. Then $\|u - u_h\|_V \to 0$
along the family.

**Reading.** The source argues that smooth functions are dense in $V$. Here this density is the
hypothesis. For $V = H_0^1(\Omega)$ the approximants can be test functions, which are dense by
definition. For $V = H^1(\Omega)$ on an extension domain they can be the functions of
$C^\infty(\overline\Omega)$ of `AtkinsonHan.Chapter07.theorem_7_3_2`; the library does not show
that a polygon is an extension domain, although every triangle is one
(`isSobolevExtensionDomainAll_referenceTriangle`).

The convergence for an increasing sequence of subspaces with dense union is
`AtkinsonHan.Chapter09.corollary_9_1_4`. Here the family is indexed along an arbitrary filter,
so the $\varepsilon$-argument is done again. -/
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

/-!
### Example 10.4.2: the Dirichlet problem for the Poisson equation

This is Theorem 10.4.1 for $V = H_0^1(\Omega)$ with the $\mathbb{P}_k$ Lagrange element on the
principal lattice (`LagrangeElement.node`, `LagrangeElement.shape`) and the finite element space
$V_h = \{v_h \in C(\overline\Omega) : v_h|_K \in \mathbb{P}_k(K), \ v_h|_{\partial\Omega} = 0\}$
(`Triangulation.polySpaceZero`). The source leaves two properties of the element implicit, and the
backbone proves them. The lattice element is edge unisolvent (`LagrangeElement.isEdgeUnisolvent`),
so $\Pi_h u$ vanishes on $\partial\Omega$ when $u$ does. Its shape functions are polynomials of
degree at most $k$ (`LagrangeElement.shape_eq_eval`), so $\Pi_h u$ is piecewise polynomial.
-/

section Example1042

open MeasureTheory Set TopologicalSpace EuclideanSpace MvPolynomial
open scoped ENNReal

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)


variable (Ω : Opens 𝔼₂)

/-- The bilinear form of the Poisson problem on $V = H_0^1(\Omega)$, $\Omega \subseteq \mathbb{R}^2$
open:
$$a(u, v) = \int_\Omega \nabla u \cdot \nabla v \, dx.$$

It is the form of Example 8.3.5, `AtkinsonHan.Chapter08.modelOperator` read as an
`AtkinsonHan.BilinForm`. -/
noncomputable abbrev poissonForm : BilinForm (SobolevEuclideanZero 2 1 2 Ω) :=
  BilinForm.ofCLM (Chapter08.modelOperator (d := 1) Ω)

/-- The bilinear form `AtkinsonHan.Chapter10.poissonForm` is $a(u, v) = \int_\Omega \sum_i
\partial_i u \, \partial_i v \, dx$, with the weak derivatives $\partial_i u$ and
$\partial_i v$. -/
theorem poissonForm_apply (u v : SobolevEuclideanZero 2 1 2 Ω) :
    poissonForm Ω u v = ∫ x in (Ω : Set 𝔼₂),
      ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean 2 1 2 Ω) (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean 2 1 2 Ω) (MultiIndexLE.single i) x :=
  Elliptic.dirichletForm_apply Ω u v

/-- The **load functional** $\ell(v) = \int_\Omega f v \, dx$ on $H_0^1(\Omega)$, for
$f \in L^2(\Omega)$. -/
noncomputable def poissonLoad (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂))) :
    StrongDual ℝ (SobolevEuclideanZero 2 1 2 Ω) :=
  (Elliptic.load Ω f).comp (SobolevEuclideanZero 2 1 2 Ω).subtypeL

/-- The load functional `AtkinsonHan.Chapter10.poissonLoad` is $\ell(v) = \int_\Omega f v \, dx$. -/
theorem poissonLoad_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
    (v : SobolevEuclideanZero 2 1 2 Ω) :
    poissonLoad Ω f v = ∫ x in (Ω : Set 𝔼₂),
      f x * SobolevMultiIndex.fn (v : SobolevEuclidean 2 1 2 Ω) x :=
  Elliptic.load_apply Ω f v

/-- The bilinear form `AtkinsonHan.Chapter10.poissonForm` satisfies $|a(u, v)| \le \|u\|_{1,\Omega}
\|v\|_{1,\Omega}$, so it is bounded with $M = 1$. -/
theorem poissonForm_isBoundedWith : (poissonForm Ω).IsBoundedWith 1 := fun u v ↦ by
  have h := Elliptic.dirichletForm_isBoundedWith Ω u v
  rw [one_mul] at h ⊢
  exact h

/-- Let $R \ge 0$ and $\Omega \subseteq B(0, R)$. The bilinear form
`AtkinsonHan.Chapter10.poissonForm` is $V$-elliptic on $H_0^1(\Omega)$:
$$a(v, v) \ge (1 + (2R)^2)^{-1} \|v\|_{1,\Omega}^2 \qquad \text{for all } v \in H_0^1(\Omega).$$

The bound is Poincaré's inequality. -/
theorem poissonForm_isEllipticWith {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ Metric.ball 0 R) :
    (poissonForm Ω).IsEllipticWith (1 + (2 * R) ^ 2)⁻¹ := fun v ↦
  Elliptic.dirichletForm_restrict_isCoerciveWith (d := 1) Ω hR hΩ v

/-- **Example 10.4.2** of [han2009theoretical]. Consider the problem $-\Delta u = f$ in $\Omega$,
$u = 0$ on $\Gamma = \partial\Omega$, for an open set $\Omega \subseteq B(0, R) \subseteq
\mathbb{R}^2$ with $R \ge 0$ and $f \in L^2(\Omega)$. Let $k \ge 1$, and let $\{\mathcal{T}_h\}$
be a regular family of triangulations of $\Omega$ (Definition 10.3.6) with mesh parameters at
most $H$, such that $\partial\Omega$ is a union of element edges of each triangulation. Let
$$V_h = \{v_h \in C(\overline\Omega) : v_h|_K \in \mathbb{P}_k(K) \text{ for every } K \in
  \mathcal{T}_h, \ v_h|_{\partial\Omega} = 0\} \subseteq H_0^1(\Omega).$$
Then the following hold.

1. For every $f$, there is a unique $u \in H_0^1(\Omega)$ with $\int_\Omega \nabla u \cdot
   \nabla v \, dx = \int_\Omega f v \, dx$ for all $v \in H_0^1(\Omega)$.
2. For every $f$ and every triangulation of the family, there is a unique $u_h \in V_h$ with
   $\int_\Omega \nabla u_h \cdot \nabla v_h \, dx = \int_\Omega f v_h \, dx$ for all
   $v_h \in V_h$.
3. There is a constant $c \ge 0$ with the following property. Let $u$ and $u_h$ be the solutions
   of 1 and 2, and let $u$ agree almost everywhere on $\Omega$ with a function
   $\tilde u \in H^{k+1}(\Omega)$ that is continuous on $\overline\Omega$ and vanishes on
   $\Gamma$. Then $\|u - u_h\|_{1,\Omega} \le c \, h^k \, \|\tilde u\|_{k+1,\Omega}$ for every
   triangulation of the family, with mesh parameter $h$.

**Reading.** The regularity $u \in H^{k+1}(\Omega)$ is taken on a representative $\tilde u$ that
is continuous up to the boundary, as in Theorem 10.3.9, and the boundary condition
$\tilde u = 0$ on $\Gamma$ is a hypothesis. On a $C^1$ domain it follows from
$u \in H_0^1(\Omega)$ and the continuity of $\tilde u$, by Theorem 9.17 of
[brezis2011functional], (ii) implies (i)
(`SobolevEuclideanZero.eqOn_frontier_of_continuousOn_closure`); a polygon is not a $C^1$ domain.
The source assumes a polygon; the library assumes that $\Omega$ is bounded, which Poincaré's
inequality (Example 8.3.5) needs, and that $\partial\Omega$ is a union of element edges
(`Triangulation.FrontierSubsetEdges`).

Part 1 is the Lax–Milgram lemma with Example 8.3.5, and part 2 holds because $V_h$
(`Triangulation.polySpaceZero`) is finite-dimensional
(`LagrangeElement.finiteDimensional_polySpaceZero`). Part 3 is
`AtkinsonHan.Chapter10.theorem_10_4_1` with the $\mathbb{P}_k$ Lagrange element on the principal
lattice. Its interpolant $\Pi_h \tilde u$ lies in $V_h$ because the element is conforming,
polynomial and edge unisolvent, so that $\Pi_h \tilde u$ vanishes on $\partial\Omega$ with
$\tilde u$ (`LagrangeElement.exists_mem_polySpaceZero_globalInterp`). The statement is
`FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm` with $s = k$, and it bounds the
error by the norm $\|\tilde u\|_{k+1,\Omega}$ (the tensor norm `sobolevNorm`), as the source
writes it. -/
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
