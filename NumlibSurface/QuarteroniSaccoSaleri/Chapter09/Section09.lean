/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.TaylorSegment
import Numlib.Approximation.TriangleQuadrature
import Numlib.Probability.MonteCarlo

/-!
# Quarteroni, Sacco and Saleri, Section 9.9: Multidimensional numerical integration

This module formalizes Section 9.9 of [quarteroni2000numerical], on three methods for
$\int_\Omega f$ in several variables. The *reduction formula* (9.56) writes the integral over a
domain normal to the $x$ axis as an iterated integral, to which one-dimensional composite formulae
apply (Section 9.9.1). The *composite interpolatory formulae on a family of triangles* (Section
9.9.2) are (9.57), with the local weights $\alpha_T^{(j)} = 2|T| \int_{\hat T} \hat l_j$, and its
instances, the composite midpoint formula (9.58) and the composite trapezoidal formula (9.59).
Definition 9.1 defines the degree of exactness on the reference triangle $\hat T$, and Property 9.4
bounds the error of a formula that is exact on $\mathbb{P}_n$ and has nonnegative weights by
$K_n h^{n+1} |\Omega| M_{n+1}$. The section also gives the two symmetric formulae $I_3$ and $I_7$.
The *Monte Carlo method* (Section 9.9.3) writes the integral as $|\Omega|$ times a mean value,
approximates it by the sample mean (9.60), and rests on the strong law of large numbers and the
variance identity (9.61).

The backbone is `Numlib.Approximation.TriangleQuadrature` (the reference triangle
`Quadrature.refTriangle`, the Dirichlet integrals, the rules as `Approximation.IsExactOn
(volume.restrict refTriangle)`, which is Definition 9.1, and the affine transport
`Quadrature.isExactOn_affineImage`), `Numlib.Analysis.Calculus.TaylorSegment` (Taylor's theorem
along a segment, for Property 9.4) and `Numlib.Probability.MonteCarlo`. The reduction formula is
Fubini's theorem (`MeasureTheory.integral_prod`).

## Main definitions

* Section 9.9.1, `QuarteroniSaccoSaleri.Chapter09.normalDomain`: the domain $\{(x, y) : a \le x \le
  b,\ \varphi_1(x) \le y \le \varphi_2(x)\}$ normal to the $x$ axis.
* Section 9.9.2, `QuarteroniSaccoSaleri.Chapter09.triangleLinear`: the linear part $B_T$ of the
  affine map (8.34) from $\hat T$ onto a triangle $T$.
* Section 9.9.2, `QuarteroniSaccoSaleri.Chapter09.triangleMap`: the affine map $F_T(\hat x) = a_1 +
  \hat x_0 (a_2 - a_1) + \hat x_1 (a_3 - a_1)$.
* Section 9.9.2, `QuarteroniSaccoSaleri.Chapter09.triangle`: the triangle $T = F_T(\hat T)$.
* Section 9.9.2, `QuarteroniSaccoSaleri.Chapter09.area`: the area $|T|$.
* Equation (9.57), `QuarteroniSaccoSaleri.Chapter09.equation_9_57`: the composite formula with local
  weights $2|T| \hat w_j$ and local nodes $F_T(\hat z_j)$.
* Equation (9.58), `QuarteroniSaccoSaleri.Chapter09.equation_9_58`: the composite midpoint formula,
  with the weights $|T|$ at the centroids.
* Equation (9.59), `QuarteroniSaccoSaleri.Chapter09.equation_9_59`: the composite trapezoidal
  formula, with the weights $|T|/3$ at the vertices.
* Definition 9.1, `QuarteroniSaccoSaleri.Chapter09.definition_9_1`: degree of exactness $n$ on
  $\hat T$.

## Main results

* Equation (9.56), `QuarteroniSaccoSaleri.Chapter09.equation_9_56`: the reduction formula for double
  integrals.
* Section 9.9.2, `QuarteroniSaccoSaleri.Chapter09.area_eq`: $|T| = |\det B_T|/2$.
* Section 9.9.2, `QuarteroniSaccoSaleri.Chapter09.triangleWeight_eq`:
  $\int_T g = 2|T| \int_{\hat T} g \circ F_T$, and the integrals over $\hat T$ that give the local
  weights $|T|$ and $|T|/3$.
* Equation (9.58), `QuarteroniSaccoSaleri.Chapter09.equation_9_58_eq`: (9.58) is (9.57) with the
  centroid rule on $\hat T$.
* Equation (9.59), `QuarteroniSaccoSaleri.Chapter09.equation_9_59_eq`: (9.59) is (9.57) with the
  vertex rule on $\hat T$.
* Definition 9.1, `QuarteroniSaccoSaleri.Chapter09.definition_9_1_iff`: Definition 9.1 in the words
  of the book.
* Definition 9.1, `QuarteroniSaccoSaleri.Chapter09.definition_9_1_transport`: a rule exact on
  $\mathbb{P}_n(\hat T)$ gives a rule exact on $\mathbb{P}_n$ on every nondegenerate triangle.
* Section 9.9.2, `QuarteroniSaccoSaleri.Chapter09.equation_9_58_degreeOfExactness`: the formulae
  (9.58) and (9.59) have degree of exactness exactly $1$.
* Property 9.4, `QuarteroniSaccoSaleri.Chapter09.property_9_4_triangle`: the error bound on one
  triangle.
* Property 9.4, `QuarteroniSaccoSaleri.Chapter09.property_9_4`: the error bound
  $\frac{2}{(n+1)!} h^{n+1} |\Omega| M_{n+1}$ on a finite family of triangles.
* Section 9.9.2, `QuarteroniSaccoSaleri.Chapter09.symmetricFormulae`: the symmetric formulae $I_3$
  and $I_7$ have degrees of exactness $2$ and $3$.
* Section 9.9.3, `QuarteroniSaccoSaleri.Chapter09.monteCarlo_mean`:
  $\int_\Omega f = |\Omega|\, \mu(f)$ for the uniform distribution on $\Omega$.
* Equation (9.60), `QuarteroniSaccoSaleri.Chapter09.monteCarlo_strongLaw`: the sample mean converges
  almost surely to $|\Omega|^{-1} \int_\Omega f$.
* Equation (9.61), `QuarteroniSaccoSaleri.Chapter09.equation_9_61`:
  $\sigma(I_N(f)) = \sigma(f)/\sqrt{N}$, and the Chebyshev bound.

## Conventions

* Points of the plane are `Fin 2 → ℝ`, because the backbone's exactness predicate is stated on
  `ι → ℝ`. The exception is the reduction formula (9.56), whose iterated integral reads naturally on
  `ℝ × ℝ`. The map `QuarteroniSaccoSaleri.Chapter08.equation_8_34` of Chapter 8 is the same affine
  map on `ℝ × ℝ`.
* The space $\mathbb{P}_n(\hat T)$ of (8.35) is the set of polynomials `p : MvPolynomial (Fin 2) ℝ`
  with `p.totalDegree ≤ n`.
* A family of triangles is indexed by a finite type `ι`, and no triangulation structure is assumed.
* In Property 9.4, $M_{n+1}$ bounds the operator norm of `iteratedFDeriv ℝ (n + 1) f` for the sup
  norm on `Fin 2 → ℝ`, and $h$ bounds the sup norms of the two edge vectors at the first vertex of
  each triangle. The maximum Euclidean edge length is such an $h$.

## Deviations from the source

* **(9.56)** (reading). `QuarteroniSaccoSaleri.Chapter09.equation_9_56` assumes a Lebesgue-
  integrable integrand and allows coincident upper and lower boundary values. The source takes
  strict separation for simplicity.
* **(9.57)–(9.59)** (generalization). The formulae are weighted sums over arbitrary finite
  triangle families. Affine maps and area are defined even for degenerate triangles. The change
  of variables and error statements require nondegeneracy.
* **Property 9.4** (precision). `QuarteroniSaccoSaleri.Chapter09.property_9_4_triangle` and
  `QuarteroniSaccoSaleri.Chapter09.property_9_4` make the constant $2/(n+1)!$ explicit. They use
  two anchored edge bounds for $h$ and an operator-norm bound on the Fréchet derivative.
* **(9.61)** (generalization). `QuarteroniSaccoSaleri.Chapter09.equation_9_61` allows any common
  sample distribution with the stated second moment and adds a Chebyshev probability estimate.
* **Property 9.4** (generalization). The statement holds for any finite family of nondegenerate
  triangles that cover $\Omega$ and overlap only on null sets, not only for a triangulation. See
  `QuarteroniSaccoSaleri.Chapter09.property_9_4`.

## Not formalized

* **Programs 78 and 79**, the midpoint and trapezoidal reduction formulae. They are algorithms with
  no stated property.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory Function Quadrature
open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter09

/-! ### §9.9.1: the reduction formula -/

/-- **Section 9.9.1** of [quarteroni2000numerical] (Figure 9.5). For $a, b \in \mathbb{R}$ and
functions $\varphi_1, \varphi_2$, the **domain normal to the $x$ axis** is
$$\Omega = \{(x, y) : a \le x \le b,\ \varphi_1(x) \le y \le \varphi_2(x)\}.$$

**Reading.** Allows equality of boundary functions and closed domain including sides.
-/
def normalDomain (a b : ℝ) (φ₁ φ₂ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc a b ∧ φ₁ p.1 ≤ p.2 ∧ p.2 ≤ φ₂ p.1}

/-- If $\varphi_1$ and $\varphi_2$ are continuous on $[a, b]$, the normal domain is closed, and
hence measurable. -/
theorem isClosed_normalDomain {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ} (h₁ : ContinuousOn φ₁ (Icc a b))
    (h₂ : ContinuousOn φ₂ (Icc a b)) : IsClosed (normalDomain a b φ₁ φ₂) := by
  have hs : IsClosed (Icc a b ×ˢ (univ : Set ℝ)) := isClosed_Icc.prod isClosed_univ
  have hc₁ : ContinuousOn (fun p : ℝ × ℝ => (φ₁ p.1, p.2)) (Icc a b ×ˢ univ) :=
    (h₁.comp continuousOn_fst fun p (hp : p ∈ Icc a b ×ˢ univ) => hp.1).prodMk continuousOn_snd
  have hc₂ : ContinuousOn (fun p : ℝ × ℝ => (p.2, φ₂ p.1)) (Icc a b ×ˢ univ) :=
    continuousOn_snd.prodMk (h₂.comp continuousOn_fst fun p (hp : p ∈ Icc a b ×ˢ univ) => hp.1)
  have e : normalDomain a b φ₁ φ₂
      = (Icc a b ×ˢ univ ∩ (fun p : ℝ × ℝ => (φ₁ p.1, p.2)) ⁻¹' {q : ℝ × ℝ | q.1 ≤ q.2})
        ∩ (Icc a b ×ˢ univ ∩ (fun p : ℝ × ℝ => (p.2, φ₂ p.1)) ⁻¹' {q : ℝ × ℝ | q.1 ≤ q.2}) := by
    ext p
    simp only [normalDomain, Set.mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true,
      mem_preimage]
    tauto
  rw [e]
  exact (hc₁.preimage_isClosed_of_isClosed hs (isClosed_le continuous_fst continuous_snd)).inter
    (hc₂.preimage_isClosed_of_isClosed hs (isClosed_le continuous_fst continuous_snd))

/-- For every $x$, the slice of the normal domain at abscissa $x$ is the segment
$[\varphi_1(x), \varphi_2(x)]$ if $x \in [a, b]$, and empty otherwise. The statement is written
for the indicator function of the domain applied to a function $f$. -/
theorem normalDomain_indicator_slice {a b : ℝ} (φ₁ φ₂ : ℝ → ℝ) (f : ℝ × ℝ → ℝ) (x : ℝ) :
    (fun y => (normalDomain a b φ₁ φ₂).indicator f (x, y))
      = if x ∈ Icc a b then (Icc (φ₁ x) (φ₂ x)).indicator (fun y => f (x, y)) else 0 := by
  funext y
  by_cases hx : x ∈ Icc a b
  · rw [ite_eq_left hx]
    by_cases hy : y ∈ Icc (φ₁ x) (φ₂ x)
    · rw [indicator_of_mem hy, indicator_of_mem]
      exact ⟨hx, hy.1, hy.2⟩
    · rw [indicator_of_notMem hy, indicator_of_notMem]
      rintro ⟨-, h1, h2⟩
      exact hy ⟨h1, h2⟩
  · rw [ite_eq_right hx, Pi.zero_apply, indicator_of_notMem]
    rintro ⟨h1, -, -⟩
    exact hx h1

/-- **Equation (9.56)** of [quarteroni2000numerical], the reduction formula for double integrals.
Let $a \le b$, let $\varphi_1, \varphi_2$ be continuous on $[a, b]$ with
$\varphi_1 \le \varphi_2$, let $\Omega$ be the domain normal to the $x$ axis, and let $f$ be
integrable on $\Omega$. Then
$$I(f) = \int_\Omega f(x, y)\,dx\,dy = \int_a^b \Bigl(\int_{\varphi_1(x)}^{\varphi_2(x)} f(x,
  y)\,dy\Bigr) dx = \int_a^b F_f(x)\,dx.$$

The proof is Fubini's theorem (`MeasureTheory.integral_prod`) for the indicator function of
$\Omega$.

**Reading.** Uses Lebesgue integrability on the domain and nonstrict ordering of boundary functions.
-/
theorem equation_9_56 {a b : ℝ} (hab : a ≤ b) {φ₁ φ₂ : ℝ → ℝ} (h₁ : ContinuousOn φ₁ (Icc a b))
    (h₂ : ContinuousOn φ₂ (Icc a b)) (hφ : ∀ x ∈ Icc a b, φ₁ x ≤ φ₂ x) {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (normalDomain a b φ₁ φ₂)) :
    ∫ p in normalDomain a b φ₁ φ₂, f p = ∫ x in a..b, ∫ y in φ₁ x..φ₂ x, f (x, y) := by
  have hΩ : MeasurableSet (normalDomain a b φ₁ φ₂) :=
    (isClosed_normalDomain h₁ h₂).measurableSet
  have hint : Integrable ((normalDomain a b φ₁ φ₂).indicator f) volume :=
    (integrable_indicator_iff hΩ).2 hf
  rw [← MeasureTheory.integral_indicator hΩ, Measure.volume_eq_prod,
    integral_prod _ (by rwa [← Measure.volume_eq_prod])]
  have hinner : ∀ x : ℝ, (∫ y, (normalDomain a b φ₁ φ₂).indicator f (x, y))
      = (Icc a b).indicator (fun x => ∫ y in φ₁ x..φ₂ x, f (x, y)) x := by
    intro x
    rw [normalDomain_indicator_slice]
    by_cases hx : x ∈ Icc a b
    · rw [ite_eq_left hx, indicator_of_mem hx, MeasureTheory.integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hφ x hx)]
    · rw [ite_eq_right hx, indicator_of_notMem hx]
      simp
  rw [integral_congr_ae (Eventually.of_forall hinner),
    MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

/-! ### §9.9.2: composite quadratures on triangles -/

/-- **Section 9.9.2** of [quarteroni2000numerical], the linear part
$B_T = [a_2 - a_1 \mid a_3 - a_1]$ of the affine map (8.34) from the reference triangle onto the
triangle with vertices $a_1, a_2, a_3$. It is the linear map
$$\hat x \mapsto \hat x_0 (a_2 - a_1) + \hat x_1 (a_3 - a_1).$$

The vertices $a_1, a_2, a_3$ are `v 0`, `v 1`, `v 2`.

**Reading.** Defines the linear map for arbitrary vertices, including degenerate triangles.
-/
noncomputable def triangleLinear (v : Fin 3 → Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (LinearMap.proj 0).smulRight (v 1 - v 0) + (LinearMap.proj 1).smulRight (v 2 - v 0)

/-- **Section 9.9.2** of [quarteroni2000numerical], the affine map (8.34)
$$F_T(\hat x) = a_1 + \hat x_0 (a_2 - a_1) + \hat x_1 (a_3 - a_1)$$
from the reference triangle onto the triangle $T$ with vertices $a_1, a_2, a_3$, which are
`v 0`, `v 1` and `v 2`.

**Reading.** Total affine map including degenerate images.
-/
noncomputable def triangleMap (v : Fin 3 → Fin 2 → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  triangleLinear v x + v 0

/-- **Section 9.9.2** of [quarteroni2000numerical]. The **triangle** with vertices $a_1, a_2, a_3$
is $T = F_T(\hat T)$, the image of the reference triangle $\hat T = \{\hat x : \hat x_0 \ge 0,\
\hat x_1 \ge 0,\ \hat x_0 + \hat x_1 \le 1\}$.

**Reading.** Affine image of the closed reference triangle, allowing degeneracy.
-/
noncomputable def triangle (v : Fin 3 → Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  triangleMap v '' refTriangle

/-- **Section 9.9.2** of [quarteroni2000numerical]. The **area** $|T|$ of the triangle with vertices
$a_1, a_2, a_3$ is its Lebesgue measure.

**Reading.** Measure-based area, defined for degenerate vertices.
-/
noncomputable def area (v : Fin 3 → Fin 2 → ℝ) : ℝ :=
  (volume (triangle v)).toReal

/-- The affine map written out: $F_T(\hat x) = a_1 + \hat x_0 (a_2 - a_1) + \hat x_1 (a_3 - a_1)$.
-/
theorem triangleMap_apply (v : Fin 3 → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    triangleMap v x = v 0 + x 0 • (v 1 - v 0) + x 1 • (v 2 - v 0) := by
  simp only [triangleMap, triangleLinear, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]
  abel

/-- The map $F_T$ sends the reference vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ to $a_1$, $a_2$, $a_3$,
and the reference centroid $(1/3, 1/3)$ to the centroid $a_T = (a_1 + a_2 + a_3)/3$. -/
theorem triangleMap_vertex (v : Fin 3 → Fin 2 → ℝ) :
    triangleMap v ![0, 0] = v 0 ∧ triangleMap v ![1, 0] = v 1 ∧ triangleMap v ![0, 1] = v 2 ∧
      triangleMap v ![1 / 3, 1 / 3] = (v 0 + v 1 + v 2) / 3 := by
  simp only [triangleMap_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i; simp
  · funext i; simp
  · funext i; simp
  · funext i; simp; ring

/-- **Section 9.9.2** of [quarteroni2000numerical], the area of a triangle. For all vertices
$a_1, a_2, a_3$,
$$|T| = \frac{|\det B_T|}{2},$$
so the Jacobian $|\det B_T|$ of $F_T$ is $2|T|$.

The proof uses `Quadrature.volume_affineImage_refTriangle`. A degenerate triangle has area $0$.

**Reading.** Determinant area formula including zero on degenerate triangles.
-/
theorem area_eq (v : Fin 3 → Fin 2 → ℝ) : area v = |LinearMap.det (triangleLinear v)| / 2 := by
  rw [area, triangle, show triangleMap v = fun y => triangleLinear v y + v 0 from rfl,
    volume_affineImage_refTriangle, ENNReal.toReal_ofReal (by positivity)]

/-- **Section 9.9.2** of [quarteroni2000numerical], the local weights from the reference triangle.
Let $T$ be a nondegenerate triangle, that is, let $B_T$ be injective. Then for every $g$,
$$\int_T g(x)\,dx = 2|T| \int_{\hat T} g(F_T(\hat x))\,d\hat x.$$
Moreover $\int_{\hat T} 1 = 1/2$ and
$$\int_{\hat T} \hat x_0\,d\hat x = \int_{\hat T} \hat x_1\,d\hat x = \int_{\hat T} (1 - \hat
  x_0 - \hat x_1)\,d\hat x = \frac{1}{6}.$$

In particular the local weights are $\alpha_T^{(j)} = \int_T l_{j,T} = 2|T| \int_{\hat T} \hat
l_j$ for the basis functions $l_{j,T} = \hat l_j \circ F_T^{-1}$ of (8.38). The weight of the
constant rule ($k = 0$) is $2|T| \int_{\hat T} 1 = |T|$, and the weights of the vertex rule
($k = 1$) are $2|T| \int_{\hat T} \lambda_j = |T|/3$, where $\lambda_0 = 1 - \hat x - \hat y$,
$\lambda_1 = \hat x$ and $\lambda_2 = \hat y$ are the barycentric coordinates.

**Reading.** General change of variables for every g plus four basis integrals.
-/
theorem triangleWeight_eq (v : Fin 3 → Fin 2 → ℝ) (hv : Function.Injective (triangleLinear v)) :
    (∀ g : (Fin 2 → ℝ) → ℝ, ∫ x in triangle v, g x
        = 2 * area v * ∫ x in refTriangle, g (triangleMap v x)) ∧
      (∫ _x in refTriangle, (1 : ℝ)) = 1 / 2 ∧
      (∫ x in refTriangle, x 0) = 1 / 6 ∧ (∫ x in refTriangle, x 1) = 1 / 6 ∧
      (∫ x in refTriangle, (1 - x 0 - x 1)) = 1 / 6 := by
  have h00 : ∫ x in refTriangle, (1 : ℝ) = 1 / 2 := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, volume_refTriangle,
      ENNReal.toReal_ofReal (by norm_num)]
  have h10 := integral_refTriangle_pow_mul_pow 1 0
  have h01 := integral_refTriangle_pow_mul_pow 0 1
  simp only [pow_zero, pow_one, mul_one, one_mul] at h10 h01
  norm_num [Nat.factorial] at h10 h01
  refine ⟨fun g => ?_, h00, h10, h01, ?_⟩
  · have hinj : InjOn (triangleMap v) refTriangle := fun y _ z _ hyz =>
      hv (add_right_cancel hyz)
    have hderiv : ∀ y ∈ refTriangle, HasFDerivWithinAt (triangleMap v)
        (LinearMap.toContinuousLinearMap (triangleLinear v)) refTriangle y := fun y _ =>
      ((LinearMap.toContinuousLinearMap (triangleLinear v)).hasFDerivAt.add_const
        (v 0)).hasFDerivWithinAt
    rw [triangle, integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_refTriangle
      hderiv hinj]
    simp only [LinearMap.det_toContinuousLinearMap, smul_eq_mul]
    rw [MeasureTheory.integral_const_mul, area_eq]
    ring
  · have hi : IntegrableOn (fun _ : Fin 2 → ℝ => (1 : ℝ)) refTriangle :=
      continuousOn_const.integrableOn_compact isCompact_refTriangle
    have hx : IntegrableOn (fun x : Fin 2 → ℝ => x 0) refTriangle :=
      (continuous_apply 0).continuousOn.integrableOn_compact isCompact_refTriangle
    have hy : IntegrableOn (fun x : Fin 2 → ℝ => x 1) refTriangle :=
      (continuous_apply 1).continuousOn.integrableOn_compact isCompact_refTriangle
    have h1 : IntegrableOn (fun x : Fin 2 → ℝ => (1 : ℝ) - x 0) refTriangle :=
      (by fun_prop : Continuous fun x : Fin 2 → ℝ => (1 : ℝ) - x 0).continuousOn
        |>.integrableOn_compact isCompact_refTriangle
    rw [integral_sub h1 hy, integral_sub hi hx, h00, h10, h01]
    norm_num

/-- **Equation (9.57)** of [quarteroni2000numerical], the composite interpolatory formula on a
family of triangles. Let the triangles $T$ have the vertices `v T` and be indexed by a finite
type, and let a reference rule on $\hat T$ have weights $\hat w_j$ and nodes $\hat z_j$. The
**composite formula** is
$$I_k^c(f) = \sum_T \sum_j \alpha_j^T f(\tilde z_j^T), \qquad \alpha_j^T = 2|T| \hat w_j, \qquad
  \tilde z_j^T = F_T(\hat z_j).$$

The form of the local weights comes from `QuarteroniSaccoSaleri.Chapter09.triangleWeight_eq`.

**Generalization.** The weighted sum accepts an arbitrary finite triangle family and reference
rule. The displayed source derives it using Lagrange interpolation on a triangulation. -/
noncomputable def equation_9_57 {ι K : Type*} [Fintype ι] [Fintype K] (v : ι → Fin 3 → Fin 2 → ℝ)
    (w : K → ℝ) (z : K → Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℝ) : ℝ :=
  ∑ T, ∑ j, (2 * area (v T) * w j) * f (triangleMap (v T) (z j))

/-- **Equation (9.58)** of [quarteroni2000numerical]. The **composite midpoint formula** on a finite
family of triangles is
$$I_0^c(f) = \sum_T |T| f(a_T),$$
where $a_T = (a_1 + a_2 + a_3)/3$ is the centroid of $T$.

**Reading.** Exact centroid sum over arbitrary triangle family, beyond triangulations.
-/
noncomputable def equation_9_58 {ι : Type*} [Fintype ι] (v : ι → Fin 3 → Fin 2 → ℝ)
    (f : (Fin 2 → ℝ) → ℝ) : ℝ :=
  ∑ T, area (v T) * f ((v T 0 + v T 1 + v T 2) / 3)

/-- **Equation (9.59)** of [quarteroni2000numerical]. The **composite trapezoidal formula** on a
finite family of triangles is
$$I_1^c(f) = \frac{1}{3} \sum_T |T| \sum_{j=1}^{3} f(a_T^{(j)}),$$
where $a_T^{(j)}$ are the vertices of $T$.

**Generalization.** Exact sum of three vertex values per triangle as printed in PDF, extended to
arbitrary families.
-/
noncomputable def equation_9_59 {ι : Type*} [Fintype ι] (v : ι → Fin 3 → Fin 2 → ℝ)
    (f : (Fin 2 → ℝ) → ℝ) : ℝ :=
  1 / 3 * ∑ T, area (v T) * ∑ j, f (v T j)

/-- **Equation (9.58)** of [quarteroni2000numerical] as an instance of (9.57). The composite
midpoint formula is (9.57) with the centroid rule on $\hat T$, which has the single weight
$\hat w = 1/2$ at the node $(1/3, 1/3)$. -/
theorem equation_9_58_eq {ι : Type*} [Fintype ι] (v : ι → Fin 3 → Fin 2 → ℝ)
    (f : (Fin 2 → ℝ) → ℝ) :
    equation_9_58 v f
      = equation_9_57 v (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => ![1 / 3, 1 / 3]) f := by
  simp only [equation_9_58, equation_9_57, Fin.sum_univ_one, (triangleMap_vertex _).2.2.2]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

/-- **Equation (9.59)** of [quarteroni2000numerical] as an instance of (9.57). The composite
trapezoidal formula is (9.57) with the vertex rule on $\hat T$, which has the weights
$\hat w_j = 1/6$ at the three vertices of $\hat T$. -/
theorem equation_9_59_eq {ι : Type*} [Fintype ι] (v : ι → Fin 3 → Fin 2 → ℝ)
    (f : (Fin 2 → ℝ) → ℝ) :
    equation_9_59 v f
      = equation_9_57 v (fun _ : Fin 3 => (1 / 6 : ℝ)) ![![0, 0], ![1, 0], ![0, 1]] f := by
  simp only [equation_9_59, equation_9_57, Fin.sum_univ_three, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  have h := triangleMap_vertex (v T)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, h.1, h.2.1, h.2.2.1]
  ring

/-- **Definition 9.1** of [quarteroni2000numerical]. The quadrature formula (9.57) with reference
weights $\hat w_j$ and nodes $\hat z_j$ has **degree of exactness $n$** if
$I_k^{\hat T}(p) = \int_{\hat T} p$ for every $p \in \mathbb{P}_n(\hat T)$.

The definition is the backbone's `Approximation.IsExactOn (volume.restrict refTriangle) ŵ ẑ n`. -/
def definition_9_1 {K : Type*} [Fintype K] (w : K → ℝ) (z : K → Fin 2 → ℝ) (n : ℕ) : Prop :=
  Approximation.IsExactOn (volume.restrict refTriangle) w z n

/-- **Definition 9.1** of [quarteroni2000numerical] in the words of the book. The rule has degree of
exactness $n$ if and only if
$$\sum_j \hat w_j\, p(\hat z_j) = \int_{\hat T} p(\hat x)\,d\hat x$$
for every polynomial $p$ in two variables of total degree at most $n$, that is, for every $p$ in
the space $\mathbb{P}_n(\hat T)$ of (8.35). -/
theorem definition_9_1_iff {K : Type*} [Fintype K] (w : K → ℝ) (z : K → Fin 2 → ℝ) (n : ℕ) :
    definition_9_1 w z n ↔ ∀ p : MvPolynomial (Fin 2) ℝ, p.totalDegree ≤ n →
      ∑ j, w j * MvPolynomial.eval (z j) p = ∫ x in refTriangle, MvPolynomial.eval x p :=
  Iff.rfl

/-- **Definition 9.1** of [quarteroni2000numerical], transport to every triangle. Let the reference
rule $(\hat w_j, \hat z_j)$ have degree of exactness $n$, and let $T$ be a nondegenerate
triangle. Then the local rule of (9.57), with the weights $2|T| \hat w_j$ and the nodes
$F_T(\hat z_j)$, integrates every polynomial of total degree at most $n$ exactly over $T$.

This is the sense in which Property 9.4 speaks of the "degree of exactness on $\Omega$". The
proof is the backbone's `Quadrature.isExactOn_affineImage`. -/
theorem definition_9_1_transport {K : Type*} [Fintype K] {w : K → ℝ} {z : K → Fin 2 → ℝ} {n : ℕ}
    (h : definition_9_1 w z n) (v : Fin 3 → Fin 2 → ℝ)
    (hv : Function.Injective (triangleLinear v)) :
    Approximation.IsExactOn (volume.restrict (triangle v)) (fun j => 2 * area v * w j)
      (fun j => triangleMap v (z j)) n := by
  have := isExactOn_affineImage measurableSet_refTriangle (triangleLinear v) hv (v 0) h
  rw [area_eq]
  have e : (fun j => 2 * (|LinearMap.det (triangleLinear v)| / 2) * w j)
      = fun j => |LinearMap.det (triangleLinear v)| * w j := by
    funext j; ring
  rw [e]
  exact this

/-- **Section 9.9.2** of [quarteroni2000numerical], degree of exactness of (9.58) and (9.59). On the
reference triangle, the centroid rule and the vertex rule are exact on $\mathbb{P}_1$ and not on
$\mathbb{P}_2$.

The book says that "the composite formulae (9.58) and (9.59) both have degree of exactness equal
to $1$". -/
theorem equation_9_58_degreeOfExactness :
    (definition_9_1 (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => ![1 / 3, 1 / 3]) 1 ∧
        ¬ definition_9_1 (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => ![1 / 3, 1 / 3]) 2) ∧
      (definition_9_1 (fun _ : Fin 3 => (1 / 6 : ℝ)) ![![0, 0], ![1, 0], ![0, 1]] 1 ∧
        ¬ definition_9_1 (fun _ : Fin 3 => (1 / 6 : ℝ)) ![![0, 0], ![1, 0], ![0, 1]] 2) :=
  ⟨⟨isExactOn_centroid, not_isExactOn_centroid_two⟩, ⟨isExactOn_vertex, not_isExactOn_vertex_two⟩⟩

/-- **Section 9.9.2** of [quarteroni2000numerical], the symmetric formulae. On the reference
triangle, the formula
$$I_3(f) = \frac{|\hat T|}{3} \sum_{j=1}^{3} f(m_j)$$
at the three edge midpoints $m_j$ has degree of exactness $2$, and the formula
$$I_7(f) = \frac{|\hat T|}{60} \Bigl(3 \sum_{i=1}^{3} f(a^{(i)}) + 8 \sum_{j=1}^{3} f(m_j) + 27
  f(a_{\hat T})\Bigr)$$
at the vertices $a^{(i)}$, the edge midpoints and the centroid $a_{\hat T}$ has degree of
exactness $3$. Neither formula is exact one degree higher.

Here $|\hat T| = 1/2$, so the weights are $1/6$ for $I_3$ and $1/40$, $1/15$, $9/40$ for $I_7$.
Both formulae transport to every triangle by
`QuarteroniSaccoSaleri.Chapter09.definition_9_1_transport`. -/
theorem symmetricFormulae :
    (definition_9_1 (fun _ : Fin 3 => (1 / 6 : ℝ)) ![![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2]] 2 ∧
        ¬ definition_9_1 (fun _ : Fin 3 => (1 / 6 : ℝ))
          ![![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2]] 3) ∧
      (definition_9_1 ![1 / 40, 1 / 40, 1 / 40, 1 / 15, 1 / 15, 1 / 15, 9 / 40]
          ![![0, 0], ![1, 0], ![0, 1], ![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2], ![1 / 3, 1 / 3]]
          3 ∧
        ¬ definition_9_1 ![1 / 40, 1 / 40, 1 / 40, 1 / 15, 1 / 15, 1 / 15, 9 / 40]
          ![![0, 0], ![1, 0], ![0, 1], ![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2], ![1 / 3, 1 / 3]]
          4) :=
  ⟨⟨isExactOn_edgeMidpoint, not_isExactOn_edgeMidpoint_three⟩,
    ⟨isExactOn_sevenPoint, not_isExactOn_sevenPoint_four⟩⟩

/-! ### Property 9.4: the error of a composite formula with nonnegative weights -/

/-- The affine map (8.34) is its vertex $a_1$ plus a linear map: $F_T(\hat x) - a_1 = \hat x_0
(a_2 - a_1) + \hat x_1 (a_3 - a_1)$. -/
theorem triangleMap_sub_vertex (v : Fin 3 → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    triangleMap v x - v 0 = x 0 • (v 1 - v 0) + x 1 • (v 2 - v 0) := by
  rw [triangleMap_apply]
  abel

/-- A triangle $T$ is star-shaped with respect to its vertex $a_1$. For every $\hat x \in \hat T$
and every $s \in [0, 1]$, the point $a_1 + s (F_T(\hat x) - a_1)$ lies in $T$.

The reason is that the segment from $a_1$ to $F_T(\hat x)$ is the image under $F_T$ of the
segment from $(0, 0)$ to $\hat x$, which stays in $\hat T$. -/
theorem triangleMap_segment_mem (v : Fin 3 → Fin 2 → ℝ) {x : Fin 2 → ℝ} (hx : x ∈ refTriangle)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : v 0 + s • (triangleMap v x - v 0) ∈ triangle v := by
  obtain ⟨h0, h1, h2⟩ := hx
  refine ⟨s • x, ⟨mul_nonneg hs.1 h0, mul_nonneg hs.1 h1, ?_⟩, ?_⟩
  · calc s * x 0 + s * x 1 = s * (x 0 + x 1) := by ring
      _ ≤ 1 * 1 := mul_le_mul hs.2 h2 (add_nonneg h0 h1) zero_le_one
      _ = 1 := one_mul 1
  · rw [triangleMap_apply, triangleMap_sub_vertex]
    simp only [Pi.smul_apply, smul_eq_mul, smul_add, smul_smul]
    abel

/-- Let $h$ bound the norms $\|a_2 - a_1\|$ and $\|a_3 - a_1\|$ of the two edges at the vertex
$a_1$. Then $\|F_T(\hat x) - a_1\| \le h$ for every $\hat x \in \hat T$. The norm is the sup
norm on `Fin 2 → ℝ`. -/
theorem norm_triangleMap_sub_vertex_le {v : Fin 3 → Fin 2 → ℝ} {h : ℝ} (hh₁ : ‖v 1 - v 0‖ ≤ h)
    (hh₂ : ‖v 2 - v 0‖ ≤ h) {x : Fin 2 → ℝ} (hx : x ∈ refTriangle) :
    ‖triangleMap v x - v 0‖ ≤ h := by
  obtain ⟨h0, h1, h2⟩ := hx
  rw [triangleMap_sub_vertex]
  calc ‖x 0 • (v 1 - v 0) + x 1 • (v 2 - v 0)‖ ≤ ‖x 0 • (v 1 - v 0)‖ + ‖x 1 • (v 2 - v 0)‖ :=
        norm_add_le _ _
    _ = x 0 * ‖v 1 - v 0‖ + x 1 * ‖v 2 - v 0‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h0, Real.norm_of_nonneg h1]
    _ ≤ x 0 * h + x 1 * h :=
        add_le_add (mul_le_mul_of_nonneg_left hh₁ h0) (mul_le_mul_of_nonneg_left hh₂ h1)
    _ = (x 0 + x 1) * h := by ring
    _ ≤ 1 * h := mul_le_mul_of_nonneg_right h2 ((norm_nonneg _).trans hh₁)
    _ = h := one_mul h

/-- The affine map $F_T$ is continuous. -/
theorem continuous_triangleMap (v : Fin 3 → Fin 2 → ℝ) : Continuous (triangleMap v) :=
  (triangleLinear v).continuous_of_finiteDimensional.add continuous_const

/-- A triangle is compact. -/
theorem isCompact_triangle (v : Fin 3 → Fin 2 → ℝ) : IsCompact (triangle v) :=
  isCompact_refTriangle.image (continuous_triangleMap v)

/-- A triangle is measurable. -/
theorem measurableSet_triangle (v : Fin 3 → Fin 2 → ℝ) : MeasurableSet (triangle v) :=
  (isCompact_triangle v).isClosed.measurableSet

/-- The area of a triangle is nonnegative. -/
theorem area_nonneg (v : Fin 3 → Fin 2 → ℝ) : 0 ≤ area v :=
  ENNReal.toReal_nonneg

/-- Let the reference rule $(\hat w_j, \hat z_j)$ have degree of exactness $n$ for some $n$. Then
for every triangle $T$ the local weights $\alpha_T^{(j)} = 2|T| \hat w_j$ of (9.57) sum to
$|T|$.

The reason is that the rule integrates the constant $1$ exactly over $\hat T$, whose area is
$1/2$. -/
theorem sum_triangleWeight_eq_area {K : Type*} [Fintype K] {w : K → ℝ} {z : K → Fin 2 → ℝ}
    {n : ℕ} (hexact : definition_9_1 w z n) (v : Fin 3 → Fin 2 → ℝ) :
    ∑ j, 2 * area v * w j = area v := by
  have h1 := hexact 1 (by simp)
  simp only [map_one, mul_one] at h1
  have h00 : ∫ _x in refTriangle, (1 : ℝ) = 1 / 2 := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, volume_refTriangle,
      ENNReal.toReal_ofReal (by norm_num)]
  rw [h00] at h1
  rw [← Finset.mul_sum, h1]
  ring

/-- **Property 9.4** of [quarteroni2000numerical], on a single triangle. Let the reference rule
$(\hat w_j, \hat z_j)$ have degree of exactness $n$ (Definition 9.1), nonnegative weights and
nodes in $\hat T$. Let $T$ be a nondegenerate triangle with vertices $a_1, a_2, a_3$, and let
$\|a_2 - a_1\| \le h$ and $\|a_3 - a_1\| \le h$. Let $f$ be of class $C^{n+1}$ at every point of
$T$, and let $\|f^{(n+1)}(x)\| \le M_{n+1}$ for all $x \in T$. Then the local rule of (9.57)
satisfies
$$|E_T(f)| = \Bigl|\int_T f - \sum_j 2|T| \hat w_j f(F_T(\hat z_j))\Bigr| \le \frac{2}{(n+1)!}
  h^{n+1} |T| M_{n+1}.$$

The derivative $f^{(n+1)}(x)$ is `iteratedFDeriv ℝ (n + 1) f x`, and the norms are the sup norm
on `Fin 2 → ℝ` and the operator norm for it. Let $P$ be the Taylor polynomial of $f$ of degree
$n$ at $a_1$. Then $E_T(f) = E_T(f - P)$, because the rule is exact on polynomials of degree $n$
on $T$ (`QuarteroniSaccoSaleri.Chapter09.definition_9_1_transport`,
`exists_mvPolynomial_taylorSum_pi`). Taylor's theorem along the segments from $a_1$ gives
$|f - P| \le M_{n+1} h^{n+1}/(n+1)!$ on $T$ (`norm_sub_taylorSum_segment_le`,
`QuarteroniSaccoSaleri.Chapter09.triangleMap_segment_mem`). Finally
$|E_T(g)| \le 2|T| \sup_T |g|$ for every $g$, because the nonnegative weights sum to $|T|$
(`QuarteroniSaccoSaleri.Chapter09.sum_triangleWeight_eq_area`).

**Reading.** Single-triangle statement with explicit 2/(n+1)! factor, two anchored edge bounds and
derivative operator norm.
-/
theorem property_9_4_triangle {K : Type*} [Fintype K] {w : K → ℝ} {z : K → Fin 2 → ℝ} {n : ℕ}
    (hexact : definition_9_1 w z n) (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, z j ∈ refTriangle)
    {v : Fin 3 → Fin 2 → ℝ} (hv : Function.Injective (triangleLinear v)) {h : ℝ}
    (hh₁ : ‖v 1 - v 0‖ ≤ h) (hh₂ : ‖v 2 - v 0‖ ≤ h) {f : (Fin 2 → ℝ) → ℝ}
    (hf : ∀ x ∈ triangle v, ContDiffAt ℝ (n + 1) f x) {M : ℝ}
    (hM : ∀ x ∈ triangle v, ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ M) :
    |(∫ x in triangle v, f x) - ∑ j, (2 * area v * w j) * f (triangleMap v (z j))|
      ≤ 2 / (n + 1)! * h ^ (n + 1) * area v * M := by
  set P : (Fin 2 → ℝ) → ℝ := fun y =>
    ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f (v 0) (fun _ => y - v 0)
    with hP
  set B : ℝ := M * h ^ (n + 1) / (n + 1)! with hB
  -- (1) Taylor's theorem along the segments from the vertex
  have htaylor : ∀ y ∈ triangle v, |f y - P y| ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    have key := norm_sub_taylorSum_segment_le (f := f) (n := n) (a := v 0)
      (w := triangleMap v x - v 0) (M := M) (fun s hs => hf _ (triangleMap_segment_mem v hx hs))
      (fun s hs => hM _ (triangleMap_segment_mem v hx hs))
    rw [add_sub_cancel, Real.norm_eq_abs] at key
    refine key.trans ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨x, hx, rfl⟩)
    rw [hB]
    gcongr
    exact norm_triangleMap_sub_vertex_le hh₁ hh₂ hx
  -- (2) the rule is exact on the Taylor polynomial
  obtain ⟨q, hqdeg, hq⟩ := exists_mvPolynomial_taylorSum_pi (f := f) (v 0) n
  have hPq : P = fun y => MvPolynomial.eval y q := funext hq
  have hEP : (∫ x in triangle v, P x) = ∑ j, (2 * area v * w j) * P (triangleMap v (z j)) := by
    rw [hPq]
    exact (definition_9_1_transport hexact v hv q hqdeg).symm
  -- (3) integrability
  have hfc : ContinuousOn f (triangle v) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntegrableOn f (triangle v) := hfc.integrableOn_compact (isCompact_triangle v)
  have hPi : IntegrableOn P (triangle v) := by
    rw [hPq]
    exact (MvPolynomial.continuous_eval q).continuousOn.integrableOn_compact (isCompact_triangle v)
  -- (4) `E(f) = E(f - P)` and the two bounds
  have hsplit : (∫ x in triangle v, f x) - ∑ j, (2 * area v * w j) * f (triangleMap v (z j))
      = (∫ x in triangle v, (f x - P x))
        - ∑ j, (2 * area v * w j) * (f (triangleMap v (z j)) - P (triangleMap v (z j))) := by
    rw [integral_sub hfi hPi, hEP]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hint : |∫ x in triangle v, (f x - P x)| ≤ B * area v := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := triangle v)
      (f := fun x => f x - P x) (C := B) (isCompact_triangle v).measure_lt_top
      (fun x hx => by rw [Real.norm_eq_abs]; exact htaylor x hx)
    rwa [Real.norm_eq_abs, measureReal_def] at this
  have hnodes : |∑ j, (2 * area v * w j) * (f (triangleMap v (z j)) - P (triangleMap v (z j)))|
      ≤ area v * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |(2 * area v * w j) * (f (triangleMap v (z j)) - P (triangleMap v (z j)))|
        = ∑ j, (2 * area v * w j) * |f (triangleMap v (z j)) - P (triangleMap v (z j))| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (by have := area_nonneg v; have := hw j; positivity)]
      _ ≤ ∑ j, (2 * area v * w j) * B :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (htaylor _ ⟨z j, hz j, rfl⟩)
            (by have := area_nonneg v; have := hw j; positivity)
      _ = area v * B := by rw [← Finset.sum_mul, sum_triangleWeight_eq_area hexact v]
  rw [hsplit, sub_eq_add_neg]
  calc |(∫ x in triangle v, (f x - P x))
        + -∑ j, (2 * area v * w j) * (f (triangleMap v (z j)) - P (triangleMap v (z j)))|
      ≤ |∫ x in triangle v, (f x - P x)|
        + |∑ j, (2 * area v * w j) * (f (triangleMap v (z j)) - P (triangleMap v (z j)))| := by
        rw [← abs_neg (∑ j, _)]
        exact abs_add_le _ _
    _ ≤ B * area v + area v * B := add_le_add hint hnodes
    _ = 2 / (n + 1)! * h ^ (n + 1) * area v * M := by rw [hB]; ring

/-- **Property 9.4** of [quarteroni2000numerical]. Let the reference rule $(\hat w_j, \hat z_j)$
have degree of exactness $n \ge 0$ (Definition 9.1), nonnegative weights and nodes in $\hat T$.
Let $\{T\}$ be a finite family of nondegenerate triangles whose union is $\Omega$ and which
pairwise overlap only on null sets, and let $h$ bound the norms of the two edges at the first
vertex of every triangle. Let $f$ be of class $C^{n+1}$ at every point of $\Omega$, and let
$\|f^{(n+1)}(x)\| \le M_{n+1}$ for all $x \in \Omega$. Then the composite formula (9.57)
satisfies
$$|E_n^c(f)| = \Bigl|\int_\Omega f - I_n^c(f)\Bigr| \le K_n h^{n+1} |\Omega| M_{n+1}, \qquad
  K_n = \frac{2}{(n+1)!},$$
where $|\Omega|$ is the area of $\Omega$.

**Generalization.** The source states the property for a triangulation of $\Omega$. The
statement here needs only a finite family of triangles that covers $\Omega$ and overlaps on null
sets.

The book states the property without proof and refers to [isaacson1994analysis], pp. 361–362.
The proof sums the bound `QuarteroniSaccoSaleri.Chapter09.property_9_4_triangle` over the
triangles, with $|\Omega| = \sum_T |T|$. The derivative $f^{(n+1)}(x)$ is
`iteratedFDeriv ℝ (n + 1) f x`, with the operator norm for the sup norm on `Fin 2 → ℝ`, and the
edges are measured in the sup norm, so the maximum Euclidean edge length is an admissible $h$. -/
theorem property_9_4 {ι K : Type*} [Fintype ι] [Fintype K] {w : K → ℝ} {z : K → Fin 2 → ℝ}
    {n : ℕ} (hexact : definition_9_1 w z n) (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, z j ∈ refTriangle)
    {v : ι → Fin 3 → Fin 2 → ℝ} (hv : ∀ T, Function.Injective (triangleLinear (v T)))
    (hdisj : Pairwise (AEDisjoint volume on fun T => triangle (v T)))
    {Ω : Set (Fin 2 → ℝ)} (hΩ : Ω = ⋃ T, triangle (v T)) {h : ℝ}
    (hh : ∀ T, ‖v T 1 - v T 0‖ ≤ h ∧ ‖v T 2 - v T 0‖ ≤ h) {f : (Fin 2 → ℝ) → ℝ}
    (hf : ∀ x ∈ Ω, ContDiffAt ℝ (n + 1) f x) {M : ℝ}
    (hM : ∀ x ∈ Ω, ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ M) :
    |(∫ x in Ω, f x) - equation_9_57 v w z f|
      ≤ 2 / (n + 1)! * h ^ (n + 1) * (volume Ω).toReal * M := by
  subst hΩ
  have hmeas : ∀ T, NullMeasurableSet (triangle (v T)) volume := fun T =>
    (measurableSet_triangle _).nullMeasurableSet
  have hfc : ContinuousOn f (⋃ T, triangle (v T)) := fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntegrableOn f (⋃ T, triangle (v T)) :=
    hfc.integrableOn_compact (isCompact_iUnion fun T => isCompact_triangle _)
  have hvol : (volume (⋃ T, triangle (v T))).toReal = ∑ T, area (v T) := by
    rw [measure_iUnion₀ hdisj hmeas, tsum_fintype,
      ENNReal.toReal_sum fun T _ => (isCompact_triangle _).measure_lt_top.ne]
    rfl
  rw [integral_iUnion_ae hmeas hdisj hfi, tsum_fintype, hvol, equation_9_57,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ T, |(∫ x in triangle (v T), f x)
        - ∑ j, (2 * area (v T) * w j) * f (triangleMap (v T) (z j))|
      ≤ ∑ T, 2 / (n + 1)! * h ^ (n + 1) * area (v T) * M :=
        Finset.sum_le_sum fun T _ => property_9_4_triangle hexact hw hz (hv T) (hh T).1 (hh T).2
          (fun x hx => hf x (mem_iUnion.mpr ⟨T, hx⟩))
          (fun x hx => hM x (mem_iUnion.mpr ⟨T, hx⟩))
    _ = 2 / (n + 1)! * h ^ (n + 1) * (∑ T, area (v T)) * M := by
        rw [Finset.mul_sum, Finset.sum_mul]

/-! ### §9.9.3: the Monte Carlo method -/

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} {d : ℕ}

/-- **Section 9.9.3** of [quarteroni2000numerical], the integral as a mean value. Let
$\Omega \subseteq \mathbb{R}^d$ with $0 < |\Omega| < \infty$. Then for every $f$,
$$\int_\Omega f(x)\,dx = |\Omega| \int_{\mathbb{R}^d} |\Omega|^{-1} \chi_\Omega(x) f(x)\,dx =
  |\Omega|\, \mu(f),$$
where $\mu(f)$ is the mean of $f(X)$ for a random variable $X$ with the uniform density
$|\Omega|^{-1} \chi_\Omega$.

The uniform distribution is the conditional measure `volume[|Ω]`. The book writes $n$ for the
dimension $d$. The statement needs no measurability hypothesis on $\Omega$ or $f$. -/
theorem monteCarlo_mean {Ω : Set (Fin d → ℝ)} (h0 : volume Ω ≠ 0) (htop : volume Ω ≠ ⊤)
    (f : (Fin d → ℝ) → ℝ) :
    ∫ x in Ω, f x = (volume Ω).toReal * ∫ x, f x ∂(volume[|Ω]) :=
  MonteCarlo.setIntegral_eq_volume_mul_integral_cond h0 htop f

/-- **Equation (9.60)** of [quarteroni2000numerical] and the strong law of large numbers. Let
$\Omega \subseteq \mathbb{R}^d$ with $0 < |\Omega| < \infty$, and let $f$ be measurable. Let
$X_1, X_2, \dots$ be measurable random variables that are pairwise independent and each have the
uniform distribution on $\Omega$, and let $f(X_1)$ be integrable. Then with probability $1$ the
sample mean
$$I_N(f) = \frac{1}{N} \sum_{i=1}^{N} f(X_i)$$
converges to the mean value $\mu(f) = |\Omega|^{-1} \int_\Omega f$ as $N \to \infty$.

The sample mean is `MonteCarlo.sampleMean f X N`, and the samples are indexed from $0$. The
proof is the backbone's `MonteCarlo.tendsto_sampleMean_ae` (the strong law of Mathlib) together
with `QuarteroniSaccoSaleri.Chapter09.monteCarlo_mean`. -/
theorem monteCarlo_strongLaw {Ω : Set (Fin d → ℝ)} (h0 : volume Ω ≠ 0) (htop : volume Ω ≠ ⊤)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) {X : ℕ → Ω' → (Fin d → ℝ)}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, Measure.map (X i) μ = volume[|Ω])
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hint : Integrable (f ∘ X 0) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => MonteCarlo.sampleMean f X N ω) atTop
      (𝓝 ((volume Ω).toReal⁻¹ * ∫ x in Ω, f x)) := by
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i =>
    ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
  have hmean : μ[f ∘ X 0] = (volume Ω).toReal⁻¹ * ∫ x in Ω, f x := by
    rw [monteCarlo_mean h0 htop f, ← mul_assoc,
      inv_mul_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩), one_mul, ← hlaw 0,
      integral_map (hX 0).aemeasurable hf.aestronglyMeasurable]
    rfl
  rw [← hmean]
  exact MonteCarlo.tendsto_sampleMean_ae f hf X hint hindep hident

/-- **Equation (9.61)** of [quarteroni2000numerical]. On a probability space, let $f$ be measurable,
let $X_1, X_2, \dots$ be pairwise independent random variables with the same distribution, let
$f(X_1)$ have a finite second moment, and let $N \ge 1$. Then the standard deviation of the
sample mean is
$$\sigma(I_N(f)) = \frac{\sigma(f)}{\sqrt{N}}, \qquad \text{that is,} \qquad
  \operatorname{Var}(I_N(f)) = \frac{\operatorname{Var}(f(X_1))}{N},$$
where $\sigma(f)$ is the standard deviation of $f(X_1)$. Moreover Chebyshev's inequality gives,
for every $c > 0$,
$$P\{|I_N(f) - \mu(f)| \ge c\} \le \frac{\sigma(f)^2}{N c^2},$$
where $\mu(f)$ is the mean of $f(X_1)$.

So the statistical error decays as $O(N^{-1/2})$, independently of the dimension. The statement
needs only pairwise independence. The proof is the backbone's `MonteCarlo.variance_sampleMean`
and `MonteCarlo.meas_ge_le_sampleMean`.

**Reading.** Applies to any identically distributed independent samples with second moment, adds
variance and Chebyshev probability bound.
-/
theorem equation_9_61 [IsProbabilityMeasure μ] {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    {X : ℕ → Ω' → (Fin d → ℝ)} (hL2 : MemLp (f ∘ X 0) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {N : ℕ} (hN : 0 < N) :
    Real.sqrt (variance (MonteCarlo.sampleMean f X N) μ)
        = Real.sqrt (variance (f ∘ X 0) μ) / Real.sqrt N ∧
      variance (MonteCarlo.sampleMean f X N) μ = variance (f ∘ X 0) μ / N ∧
      ∀ c : ℝ, 0 < c → μ {ω | c ≤ |MonteCarlo.sampleMean f X N ω - μ[f ∘ X 0]|}
        ≤ ENNReal.ofReal (variance (f ∘ X 0) μ / (N * c ^ 2)) :=
  ⟨by rw [MonteCarlo.variance_sampleMean hf hL2 hindep hident hN, Real.sqrt_div' _ (by positivity)],
    MonteCarlo.variance_sampleMean hf hL2 hindep hident hN,
    fun _ hc => MonteCarlo.meas_ge_le_sampleMean hf hL2 hindep hident hN hc⟩

end QuarteroniSaccoSaleri.Chapter09
