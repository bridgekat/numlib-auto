/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Numlib.Analysis.Sobolev.Space
import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Operations on test functions: the $L^2$ class and the negative Laplacian

Let $\Omega \subseteq \mathbb{R}^N$ be open, and let $\mathcal{D}(\Omega)$ be the space of real test
functions on $\Omega$, the smooth functions with compact support in $\Omega$. This file gives three
constructions on test functions. A test function on an open $\Omega' \subseteq \Omega$ is a test
function on $\Omega$ (`TestFunction.ofLE`). A test function has a class in $L^2(\Omega)$
(`TestFunction.toL2`). The negative Laplacian $-\Delta \varphi = -\sum_i \partial_i \partial_i
\varphi$ of a test function is again a test function (`TestFunction.negLaplacian`). The last
construction rests on the fact that the Laplacian of a smooth compactly supported function is
smooth, has compact support, and has its support inside the support of the function
(`Elliptic.laplacianRep_props`). With these tools, `Numlib.Analysis.PDE.DirichletLaplacian` shows
that the test functions lie in every domain $D(A^\ell)$ of the Dirichlet Laplacian $A$.

The last section proves the fundamental lemma of the calculus of variations for a function $g$ that
is continuous on $\Omega$. If $\int_\Omega g \varphi \ge 0$ for every nonnegative test function
$\varphi$, then $g \ge 0$ on $\Omega$. If $\int_\Omega g \varphi = 0$ for every test function
$\varphi$ with support in an open $U \subseteq \Omega$, then $g = 0$ on $U$.

## Main definitions

* `TestFunction.ofLE`: a test function on $\Omega'$, read as a test function on an open
  $\Omega \supseteq \Omega'$.
* `TestFunction.toL2`: the class of a test function in $L^2(\Omega)$.
* `TestFunction.negLaplacian`: the negative Laplacian $-\sum_i \partial_i \partial_i \varphi$ of a
  test function, as a test function.

## Main results

* `Elliptic.laplacianRep_props`: the Laplacian of a smooth compactly supported function is smooth
  and compactly supported, with support inside the support of the function.
* `nonneg_on_of_forall_integral_mul_testFunction_nonneg`: a continuous $g$ with
  $\int_\Omega g \varphi \ge 0$ for all nonnegative test functions $\varphi$ is nonnegative on
  $\Omega$.
* `eqOn_zero_of_forall_integral_mul_testFunction_eq_zero`: a continuous $g$ with
  $\int_\Omega g \varphi = 0$ for all test functions supported in an open $U \subseteq \Omega$
  vanishes on $U$.

## Implementation notes

* The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)`, and $\mathcal{D}(\Omega)$ is Mathlib's
  `𝓓(Ω, ℝ)` for `Ω : Opens (EuclideanSpace ℝ (Fin N))`.
* The second partial derivative $\partial_i \partial_i \theta(x)$ is written `fderiv ℝ (fun z ↦
  fderiv ℝ θ z (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)`.
* The space $L^2(\Omega)$ is `Lp ℝ 2 (volume.restrict Ω)`.
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

namespace Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $E$ be a real normed space, let $\theta : E \to \mathbb{R}$ be smooth, and let $y \in E$.
Then the second directional derivative $x \mapsto \partial_y \partial_y \theta(x)$ is smooth.

The derivative $\partial_y \partial_y \theta(x)$ is `fderiv ℝ (fun z ↦ fderiv ℝ θ z y) x y`. -/
theorem contDiff_fderiv_fderiv_apply {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) (y : E) :
    ContDiff ℝ ∞ fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z y) x y :=
  (((hθ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).fderiv_right (m := ∞)
    le_rfl).clm_apply contDiff_const

variable {N : ℕ}

/-- For every function $\theta : \mathbb{R}^N \to \mathbb{R}$, the topological support of the
Laplacian $\Delta \theta = \sum_i \partial_i \partial_i \theta$ is contained in the topological
support of $\theta$.

The lemma has no hypothesis on $\theta$. The derivatives are Mathlib's `fderiv`, which is $0$ at
a point where the function is not differentiable. -/
theorem tsupport_laplacianRep_subset {θ : EuclideanSpace ℝ (Fin N) → ℝ} :
    tsupport (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ⊆ tsupport θ := by
  refine closure_minimal ((Finset.support_sum _ _).trans ?_) (isClosed_tsupport θ)
  refine Set.iUnion₂_subset fun i _ ↦ subset_closure.trans ?_
  exact (tsupport_fderiv_apply_subset ℝ _).trans (tsupport_fderiv_apply_subset ℝ _)

/-- Let $\theta : \mathbb{R}^N \to \mathbb{R}$ be smooth with compact support. Then its Laplacian
$\Delta \theta = \sum_i \partial_i \partial_i \theta$ is smooth, has compact support, and its
topological support is contained in the topological support of $\theta$.

This is the fact from which `TestFunction.negLaplacian` is built. -/
theorem laplacianRep_props {θ : EuclideanSpace ℝ (Fin N) → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) :
    ContDiff ℝ ∞ (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ∧
    HasCompactSupport (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ∧
    tsupport (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ⊆ tsupport θ :=
  ⟨ContDiff.sum fun _ _ ↦ contDiff_fderiv_fderiv_apply hθ _,
    hθc.of_isClosed_subset (isClosed_tsupport _) tsupport_laplacianRep_subset,
    tsupport_laplacianRep_subset⟩

end Elliptic

open Elliptic

/-- Let $\Omega' \subseteq \Omega$ be open subsets of a real normed space. A test function $\psi$ on
$\Omega'$ is a test function on $\Omega$, with the same values.

The hypothesis $\Omega' \subseteq \Omega$ is `h : Ω' ≤ Ω` in `Opens E`. -/
def TestFunction.ofLE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω' : Opens E}
    (ψ : 𝓓(Ω', ℝ)) (h : Ω' ≤ Ω) : 𝓓(Ω, ℝ) where
  toFun := ψ
  contDiff' := ψ.contDiff
  hasCompactSupport' := ψ.hasCompactSupport
  tsupport_subset' := ψ.tsupport_subset.trans h

/-- The test function `TestFunction.ofLE ψ h` on the larger set has the same underlying function as
$\psi$. -/
@[simp]
theorem TestFunction.ofLE_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω Ω' : Opens E} (ψ : 𝓓(Ω', ℝ)) (h : Ω' ≤ Ω) : (ψ.ofLE h : E → ℝ) = ψ :=
  rfl

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The class in $L^2(\Omega)$ of a test function $\varphi$ on an open
$\Omega \subseteq \mathbb{R}^N$.

Here $L^2(\Omega)$ is `Lp ℝ 2 (volume.restrict Ω)`, the space of square-integrable functions for
the Lebesgue measure restricted to $\Omega$. -/
def TestFunction.toL2 (φ : 𝓓(Ω, ℝ)) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (φ.memLp 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toLp φ

/-- The class `TestFunction.toL2 φ` agrees with $\varphi$ almost everywhere on $\Omega$. -/
theorem TestFunction.coeFn_toL2 (φ : 𝓓(Ω, ℝ)) :
    ⇑φ.toL2 =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ :=
  MemLp.coeFn_toLp _

/-- The **negative Laplacian** of a test function $\varphi$ on an open
$\Omega \subseteq \mathbb{R}^N$ is the test function
$$-\Delta \varphi = -\sum_{i=1}^N \partial_i \partial_i \varphi$$
on $\Omega$.

That $-\Delta \varphi$ is smooth, has compact support, and has its support in $\Omega$ follows
from `Elliptic.laplacianRep_props`. -/
def TestFunction.negLaplacian (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) where
  toFun x := -∑ i, fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single i 1)
  contDiff' := (laplacianRep_props φ.contDiff φ.hasCompactSupport).1.neg
  hasCompactSupport' := (laplacianRep_props φ.contDiff φ.hasCompactSupport).2.1.neg
  tsupport_subset' := by
    refine subset_trans ?_ ((laplacianRep_props φ.contDiff φ.hasCompactSupport).2.2.trans
      φ.tsupport_subset)
    exact (tsupport_neg _).subset

/-- The values of the negative Laplacian: `TestFunction.negLaplacian φ` is the function $x \mapsto
-\sum_i \partial_i \partial_i \varphi(x)$. -/
theorem TestFunction.negLaplacian_coe (φ : 𝓓(Ω, ℝ)) :
    (φ.negLaplacian : EuclideanSpace ℝ (Fin N) → ℝ)
      = fun x ↦ -∑ i, fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) :=
  rfl

/-! ### The fundamental lemma of the calculus of variations for continuous functions -/

section FundamentalLemma

/-- The **fundamental lemma of the calculus of variations**, inequality form. Let
$\Omega \subseteq \mathbb{R}^N$ be open, and let $g : \mathbb{R}^N \to \mathbb{R}$ be continuous
on $\Omega$. If
$$\int_\Omega g \varphi \, dx \ge 0$$
for every test function $\varphi$ on $\Omega$ with $\varphi \ge 0$, then $g(x) \ge 0$ for every
$x \in \Omega$.

The idea of the proof: if $g(x_0) < 0$, then a nonnegative bump function at $x_0$ with support
in the set where $g < g(x_0)/2$ gives a negative integral. -/
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
  have hint := integrable_mul_testFunction (μ := volume) hg φ
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

/-- The **fundamental lemma of the calculus of variations** on an open subset. Let
$\Omega \subseteq \mathbb{R}^N$ be open, let $g : \mathbb{R}^N \to \mathbb{R}$ be continuous on
$\Omega$, and let $U \subseteq \Omega$ be open. If
$$\int_\Omega g \varphi \, dx = 0$$
for every test function $\varphi$ on $\Omega$ whose topological support is contained in $U$,
then $g(x) = 0$ for every $x \in U$.

The proof applies Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, which gives
$g = 0$ almost everywhere on $U$, and then the continuity of $g$. -/
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

end FundamentalLemma
