/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Boundary.PolygonTrace
import NumlibSurface.AtkinsonHan.Chapter07.Section03

/-!
# Atkinson and Han, Section 7.6: Integration by parts formulas

This module formalizes Section 7.6 of [han2009theoretical]. The section proves the Gauss–Green
formula
$$\int_\Omega u_{x_i} v \, dx = \int_\Gamma u v \nu_i \, ds - \int_\Omega u v_{x_i} \, dx$$
on a domain $\Omega$ with boundary $\Gamma$ and outward unit normal $\nu$. The formula holds
classically for $u, v \in C^1(\bar\Omega)$. A density argument extends it to $u, v \in H^1(\Omega)$
(Proposition 7.6.1, the formula (7.6.1)), and further to $u \in W^{1,p}(\Omega)$ and
$v \in W^{1,p^*}(\Omega)$ with $1/p + 1/p^* = 1$ (the formula (7.6.3)). The source derives Green's
identities from these formulas. For Sobolev functions the boundary term is $\int_\Gamma (\gamma
u)(\gamma v) \nu_i \, d\sigma$, with the traces $\gamma u$ and $\gamma v$ of Theorem 7.3.10, because
$u$ and $v$ are defined only almost everywhere in $\Omega$.

The source states the section for a Lipschitz domain. The formalization has two readings of it: a
bounded $C^1$ domain $\Omega \subseteq \mathbb{R}^{d+1}$, and a plane domain triangulated without
slits. On a $C^1$ domain, `Numlib.Analysis.Sobolev.Boundary.ContDiffDomain` provides the surface
measure, the outward normal, the divergence theorem and the trace, and the Sobolev formula is proved
in `Numlib.Analysis.Sobolev.Boundary.Trace`. On a triangulated polygon,
`Numlib.Analysis.Sobolev.Boundary.Polygon` and `Numlib.Analysis.Sobolev.Boundary.PolygonTrace`
provide the arclength measure, the outward normal and the trace.

## Main results

* Section 7.6, `AtkinsonHan.Chapter07.proposition_7_6_1_classical`: the Gauss–Green formula for
  $u, v \in C^1(\bar\Omega)$ on a bounded $C^1$ domain.
* Proposition 7.6.1, `AtkinsonHan.Chapter07.proposition_7_6_1`: the formula (7.6.1) for
  $u, v \in H^1(\Omega)$ on a bounded $C^1$ domain.
* Equation (7.6.3), `AtkinsonHan.Chapter07.proposition_7_6_1_conj`: the formula for
  $u \in W^{1,p}(\Omega)$ and $v \in W^{1,p^*}(\Omega)$ on a bounded $C^1$ domain.
* Proposition 7.6.1, `AtkinsonHan.Chapter07.proposition_7_6_1_polygon`: the formula (7.6.1) for
  $u, v \in H^1(\Omega)$ on a polygon triangulated without slits.
* Equation (7.6.3), `AtkinsonHan.Chapter07.proposition_7_6_1_polygon_conj`: the formula (7.6.3) on a
  polygon triangulated without slits.

## Proof outline

On a $C^1$ domain, the classical formula is the divergence theorem for the field $(uv) e_i$. The
Sobolev formula follows by the density argument of the source: the classical formula holds for the
smooth approximations of Theorem 7.3.2, the boundary term passes to the limit by the continuity of
the trace (Theorem 7.3.10 (b)), and the interior terms pass to the limit by Hölder's inequality. A
polygon is not known to be an extension domain, so there the formula is the sum over the triangles
of the formula on each triangle. The terms of the interior edges cancel, because the two one-sided
traces agree across an edge that lies in $\Omega$.

## Conventions

* The ambient space of a $C^1$ domain is $\mathbb{R}^{d+1}$, as in Definition 7.2.1. A bounded $C^1$
  domain is given by the hypotheses `hΩ : IsContDiffDomain 1 Ω` and `hb : Bornology.IsBounded Ω`.
* $H^1(\Omega)$ and $W^{1,p}(\Omega)$ are the spaces of Definition 7.2.2 in the multi-index reading,
  `SobolevMultiIndex ℝ (AtkinsonHan.Chapter07.stdBasis (d + 1)) 1 p Ω volume`.
* The weak derivative $u_{x_i}$ is `weakDeriv u (MultiIndexLE.single i)`.
* The conjugate exponents $p, p^* \in (1, \infty)$ with $1/p + 1/p^* = 1$ are given by
  `ENNReal.HolderConjugate p q`, `p ≠ ⊤` and `q ≠ ⊤`; see `ENNReal.holderConjugate_iff`.

## Implementation notes

* On a $C^1$ domain, the surface measure $\sigma$ is a measure on the ambient space that is carried
  by $\Gamma = \partial\Omega$. It is `hΩ.boundaryMeasure hb`.
* On a $C^1$ domain, the outward unit normal $\nu$ is a function on the ambient space of norm one
  $\sigma$-almost everywhere. It is `hΩ.outwardNormal hb`.
* On a $C^1$ domain, the trace $\gamma_p : W^{1,p}(\Omega) \to L^p(\Gamma)$ is `hΩ.traceL hb p hp`.
* On a triangulated polygon, $\Omega \subseteq \mathbb{R}^2$ comes with a triangulation
  `𝒯 : Triangulation Ω` without slits, which is the hypothesis `𝒯.InteriorEdgesSubset`: the relative
  interior of every interior edge lies in $\Omega$. Across a slit the two one-sided traces differ,
  and the formula with a single trace is false.
* On a triangulated polygon, the measure $\sigma$ is the arclength measure of the boundary edges and
  $\nu$ is the outward normal; they are `𝒯.boundaryMeasure` and `𝒯.outwardNormal`.
* On a triangulated polygon, the trace is `𝒯.traceL p hp` of
  `AtkinsonHan.Chapter07.theorem_7_3_10_polygon`, glued from the triangles.

## Deviations from the source

* **The classical Gauss–Green formula, Proposition 7.6.1 and (7.6.3)** (reading). The source assumes
  a Lipschitz domain. The statements assume a bounded $C^1$ domain, or a plane domain triangulated
  without slits, which is the case that the finite element chapters use. See
  `AtkinsonHan.Chapter07.proposition_7_6_1_classical`, `AtkinsonHan.Chapter07.proposition_7_6_1` and
  `AtkinsonHan.Chapter07.proposition_7_6_1_polygon`.
-/

open Filter MeasureTheory Set TopologicalSpace SobolevMultiIndex

open scoped ContDiff ENNReal NNReal Topology

namespace AtkinsonHan.Chapter07

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Section 7.6** of [han2009theoretical], the classical Gauss–Green formula. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with boundary $\Gamma$, surface
measure $\sigma$ and outward unit normal $\nu$. Let $u, v$ be continuous on $\bar\Omega$ and of
class $C^1$ on $\Omega$, with derivatives that extend continuously to $\bar\Omega$. Then for
each coordinate index $i$,
$$\int_\Omega u_{x_i} v \, dx = \int_\Gamma u v \nu_i \, d\sigma - \int_\Omega u v_{x_i} \,
  dx.$$

**Reading.** The source assumes a Lipschitz domain. The statement assumes a bounded $C^1$
domain.

The source displays this formula before Proposition 7.6.1 and calls it Gauss's formula, or the
divergence theorem. The proof is `BoundaryData.integral_fderiv_mul_add_eq`, the divergence
theorem `IsContDiffDomain.integral_div_eq` for the field $(uv) e_i$. The regularity on the
closure is `ContDiffOnClosure`, and `fderiv ℝ u x (EuclideanSpace.single i 1)` is the derivative
$u_{x_i}$. -/
theorem proposition_7_6_1_classical
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {u v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hu' : ContDiffOnClosure ℝ 1 u (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hv : ContinuousOn v (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hv' : ContDiffOnClosure ℝ 1 v (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (i : Fin (d + 1)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        fderiv ℝ u x (EuclideanSpace.single i 1) * v x
      = (∫ x, u x * v x * hΩ.outwardNormal hb x i ∂(hΩ.boundaryMeasure hb))
        - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          u x * fderiv ℝ v x (EuclideanSpace.single i 1) :=
  eq_sub_of_add_eq ((hΩ.boundaryData hb).integral_fderiv_mul_add_eq hu hu' hv hv' i)

/-- **Proposition 7.6.1** of [han2009theoretical], the formula (7.6.1). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with boundary $\Gamma$, surface
measure $\sigma$, outward unit normal $\nu$ and trace $\gamma : H^1(\Omega) \to L^2(\Gamma)$ of
Theorem 7.3.10. Then for all $u, v \in H^1(\Omega)$ and each coordinate index $i$,
$$\int_\Omega u_{x_i} v \, dx = \int_\Gamma (\gamma u)(\gamma v) \nu_i \, d\sigma - \int_\Omega
  u v_{x_i} \, dx,$$
where $u_{x_i}$ and $v_{x_i}$ are weak derivatives.

**Reading.** The source assumes a Lipschitz domain. The statement assumes a bounded $C^1$
domain. The boundary values of $u$ and $v$ in the source are read as their traces.

$H^1(\Omega)$ is the space of Definition 7.2.2, `SobolevMultiIndex ℝ
(AtkinsonHan.Chapter07.stdBasis (d + 1)) 1 2 Ω volume`. The proof of the source is a density
argument: the classical formula holds for $u_n, v_n \in C^1(\bar\Omega)$ that converge to $u, v$
in $H^1(\Omega)$ (Theorem 7.3.2), the interior terms pass to the limit by the Cauchy–Schwarz
inequality, and the boundary term passes to the limit by the continuity of the trace (Theorem
7.3.10 (b)). The classical formula is `AtkinsonHan.Chapter07.proposition_7_6_1_classical`, and
the proof here is the field `green` of the trace family of the backbone,
`IsContDiffDomain.green` for $p = q = 2$, which comes from
`BoundaryData.green_of_hasSmoothDensity`. -/
theorem proposition_7_6_1 (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (u v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 2 Ω volume) (i : Fin (d + 1)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        (weakDeriv u (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x * fn v x
      = (∫ x, (hΩ.traceL hb 2 ENNReal.ofNat_ne_top u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x
          * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x
          * hΩ.outwardNormal hb x i ∂(hΩ.boundaryMeasure hb))
        - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), fn u x
          * (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x :=
  eq_sub_of_add_eq (hΩ.green hb 2 2 ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top u v i)

/-- **Equation (7.6.3)** of [han2009theoretical], the extension of Proposition 7.6.1 to conjugate
exponents. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain with boundary
$\Gamma$, surface measure $\sigma$ and outward unit normal $\nu$. Let $p, p^* \in (1, \infty)$
with $1/p + 1/p^* = 1$, and let $\gamma_p : W^{1,p}(\Omega) \to L^p(\Gamma)$ and $\gamma_{p^*} :
W^{1,p^*}(\Omega) \to L^{p^*}(\Gamma)$ be the traces of Theorem 7.3.10. Then for all
$u \in W^{1,p}(\Omega)$, $v \in W^{1,p^*}(\Omega)$ and each coordinate index $i$,
$$\int_\Omega u_{x_i} v \, dx = \int_\Gamma (\gamma_p u)(\gamma_{p^*} v) \nu_i \, d\sigma -
  \int_\Omega u v_{x_i} \, dx.$$

**Reading.** The source assumes a Lipschitz domain. The statement assumes a bounded $C^1$
domain.

The proof is the density argument of Proposition 7.6.1 with Hölder's inequality in place of the
Cauchy–Schwarz inequality: the field `green` of the trace family of the backbone,
`IsContDiffDomain.green`. The exponents are `p q : ℝ≥0∞` with `ENNReal.HolderConjugate p q`,
`Fact (1 ≤ p)`, `Fact (1 ≤ q)`, `p ≠ ⊤` and `q ≠ ⊤`; conjugacy then gives $1 < p, q < \infty$. -/
theorem proposition_7_6_1_conj {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (u : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume)
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 q Ω volume) (i : Fin (d + 1)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        (weakDeriv u (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x * fn v x
      = (∫ x, (hΩ.traceL hb p hp u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x
          * (hΩ.traceL hb q hq v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x
          * hΩ.outwardNormal hb x i ∂(hΩ.boundaryMeasure hb))
        - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), fn u x
          * (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x :=
  eq_sub_of_add_eq (hΩ.green hb p q hp hq u v i)

/-! ### Proposition 7.6.1 on a triangulated polygon -/

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Equation (7.6.3)** of [han2009theoretical], on a triangulated polygon. Let
$\Omega \subseteq \mathbb{R}^2$ be open with a triangulation $\mathcal{T}$ that has no slits,
let $\sigma$ be the arclength measure on $\Gamma = \partial\Omega$ and $\nu$ the outward unit
normal. Let $p, p^* \in (1, \infty)$ with $1/p + 1/p^* = 1$, and let
$\gamma_p : W^{1,p}(\Omega) \to L^p(\Gamma)$ and $\gamma_{p^*} : W^{1,p^*}(\Omega) \to
L^{p^*}(\Gamma)$ be the traces of `AtkinsonHan.Chapter07.theorem_7_3_10_polygon`. Then for all
$u \in W^{1,p}(\Omega)$, $v \in W^{1,p^*}(\Omega)$ and each coordinate index $i$,
$$\int_\Omega u_{x_i} v \, dx = \int_\Gamma (\gamma_p u)(\gamma_{p^*} v) \nu_i \, d\sigma -
  \int_\Omega u v_{x_i} \, dx.$$

**Reading.** The source assumes a Lipschitz domain. A polygon triangulated without slits is the
case of a Lipschitz domain that the finite element chapters use.

The hypothesis without slits is `𝒯.InteriorEdgesSubset`. The exponents are given as in
`AtkinsonHan.Chapter07.proposition_7_6_1_conj`. The formula is the field `green` of
`Triangulation.traceFamily`, `Triangulation.green`. It is proved by the sum of the formula over
the triangles, not by density on the polygon. -/
theorem proposition_7_6_1_polygon_conj {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)
    (hI : 𝒯.InteriorEdgesSubset) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (u : SobolevMultiIndex ℝ (stdBasis 2) 1 p Ω volume)
    (v : SobolevMultiIndex ℝ (stdBasis 2) 1 q Ω volume) (i : Fin 2) :
    ∫ x in (Ω : Set 𝔼₂), (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * fn v x
      = (∫ x, (𝒯.traceL p hp u : 𝔼₂ → ℝ) x * (𝒯.traceL q hq v : 𝔼₂ → ℝ) x
          * 𝒯.outwardNormal x i ∂𝒯.boundaryMeasure)
        - ∫ x in (Ω : Set 𝔼₂), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼₂ → ℝ) x :=
  eq_sub_of_add_eq (𝒯.green hI q hp hq u v i)

/-- **Proposition 7.6.1** of [han2009theoretical], the formula (7.6.1) on a triangulated polygon.
Let $\Omega \subseteq \mathbb{R}^2$ be open with a triangulation $\mathcal{T}$ that has no
slits, let $\sigma$ be the arclength measure on $\Gamma = \partial\Omega$, $\nu$ the outward
unit normal, and $\gamma : H^1(\Omega) \to L^2(\Gamma)$ the trace of
`AtkinsonHan.Chapter07.theorem_7_3_10_polygon`. Then for all $u, v \in H^1(\Omega)$ and each
coordinate index $i$,
$$\int_\Omega u_{x_i} v \, dx = \int_\Gamma (\gamma u)(\gamma v) \nu_i \, d\sigma - \int_\Omega
  u v_{x_i} \, dx.$$

**Reading.** The source assumes a Lipschitz domain. A polygon triangulated without slits is the
case of a Lipschitz domain that the finite element chapters use.

This is the case $p = p^* = 2$ of `AtkinsonHan.Chapter07.proposition_7_6_1_polygon_conj`. The
hypothesis without slits is `𝒯.InteriorEdgesSubset`. `AtkinsonHan.Chapter07.proposition_7_6_1`
is the formula on a $C^1$ domain. -/
theorem proposition_7_6_1_polygon {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)
    (hI : 𝒯.InteriorEdgesSubset)
    (u v : SobolevMultiIndex ℝ (stdBasis 2) 1 2 Ω volume) (i : Fin 2) :
    ∫ x in (Ω : Set 𝔼₂), (weakDeriv u (MultiIndexLE.single i) : 𝔼₂ → ℝ) x * fn v x
      = (∫ x, (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼₂ → ℝ) x
          * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼₂ → ℝ) x
          * 𝒯.outwardNormal x i ∂𝒯.boundaryMeasure)
        - ∫ x in (Ω : Set 𝔼₂), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼₂ → ℝ) x :=
  proposition_7_6_1_polygon_conj 𝒯 hI ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top u v i

end AtkinsonHan.Chapter07
