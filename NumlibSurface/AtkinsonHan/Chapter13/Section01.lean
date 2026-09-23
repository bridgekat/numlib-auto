import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.AddCircle.Real
import Numlib.Analysis.Complex.Harmonic
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Boundary.Polygon
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.Approximation.DividedDifference
import Numlib.IntegralEquations.Basic

/-!
# Atkinson–Han §13.1: the parametrized double layer kernel

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §13.1.

Almost all of §13.1 is planar potential theory — the divergence theorem on a piecewise smooth
multiply connected region, Green's identities, the representation formula, the jump relations — and
is out of scope; the chapter's plan group says which results and why.  What is *not* potential
theory is the object §13.2 actually computes with: after a regular `C²` parametrization
`r(t) = (ξ(t), η(t))` of the boundary, the double layer operator is an ordinary integral operator
whose kernel (13.1.33) is

`k(t, s) = [η'(s) (ξ(t) - ξ(s)) - ξ'(s) (η(t) - η(s))] / |r(t) - r(s)|²`,

a `0/0` quotient on the diagonal.  Numerator and denominator both vanish to second order there, and
(13.1.34) says the quotient extends continuously, with `k(t, t)` equal to **minus half the signed
curvature** of the counterclockwise parametrization that the book fixes.  That is the whole of the
analysis needed to make the double layer operator a *compact* operator, and it is what this file
provides.

## A sign in the book

The book's *prose* right after (13.1.34) — "the value of `k(t, t)` is one-half the curvature of `S`
at `r(t)`" — contradicts the book's own display (13.1.34), and it is the display that is right.
For the counterclockwise unit circle `r(t) = (cos t, sin t)`, whose signed curvature is `+1`,
(13.1.34) evaluates to `-1/2`; and (13.1.33) evaluates to `-1/2` at every `s ≠ t`, as it must, the
two displays being the same quotient with the common factor `(t - s)²` cancelled.  Both displays
also agree with `∂/∂n_Q log |P - Q|` computed directly from the *inner* normal
`n = (-η', ξ') / √(ξ'² + η'²)` that §13.1 fixes just before (13.1.32).  This file follows the two
displays, so here `k(t, t) = -κ(t)/2`.

The sign is not cosmetic: it is what makes the row integral `∫_0^L k(t, s) ds` equal `-π` rather
than `+π`, and hence what makes the boundary integral equation (13.1.32) read `(-π + K) u = g`,
which is the form `Chapter13/Section02` states and solves.

The kernel is therefore *defined* by the quotient of divided differences that is already continuous,
`Numlib/Approximation/DividedDifference`, rather than by the displayed formula with a case
distinction at `s = t`; `equation_13_1_33` then recovers the book's formula off the diagonal and
`equation_13_1_34` the diagonal value.  Only the derivatives `ξ', η', ξ'', η''` enter the
definition.

## Main results

* `doubleLayerKernel`, with `equation_13_1_33` and `equation_13_1_34`.
* `doubleLayerKernel_eq_neg_im_div`, that off the diagonal the kernel is
  `-Im (r'(s) / (r(s) - r(t)))`, *minus* the rate of turning of the chord from `r(t)` to `r(s)` —
  the identity that makes the row integral of Exercise 13.2.5 a turning number.
* `doubleLayerKernelCM` — the kernel as a `C(Icc a b × Icc a b, ℝ)` on a parameter interval on
  which the curve is regular and simple, and `isCompactOperator_doubleLayer`, that the resulting
  integral operator is compact.
* `doubleLayerKernelCP` — the same for a regular simple *closed* curve of period `L`, as a
  `C(AddCircle L × AddCircle L, ℝ)`, with `isCompactOperator_doubleLayerCP`.  This is the form
  §13.2 uses, `C_p(L) = C(AddCircle L, ℝ)`.

  The descent is *not* a lift of a biperiodic function: `doubleLayerKernel` is not separately
  `L`-periodic, because `k(t + L, t) = 0` by `equation_13_1_33` — the real parameters `t` and
  `t + L` are distinct and the chord between them vanishes — whereas `k(t, t)` is minus half the
  signed curvature.  What is invariant is the *diagonal* translation `(t, s) ↦ (t + L, s + L)`
  (`doubleLayerKernel_add_period`), so the kernel on the circle takes the representative of the
  *difference* `s - t` in `[-L/2, L/2)`.  Continuity then rests on the seam identity
  `doubleLayerKernel_sub_half_period`, `k(t, t - L/2) = k(t, t + L/2)`, and on the parameter
  rectangle `[0, L] × [-L/2, L/2]` being a compact space mapping onto the torus, hence a quotient
  map.

* `kelvin` and `kelvin_harmonic` — §13.1.2, that the Kelvin transform `û = u ∘ T` of a harmonic
  function is harmonic, `T` being inversion in the unit circle.  This is the one item of the module
  that is not on the path to §13.2; identifying the plane with `ℂ` it is
  `InnerProductSpace.HarmonicAt.comp_conj` and `.comp_analyticAt` of
  `Numlib/Analysis/Complex/Harmonic`, because `T z = conj (z⁻¹)`.

## Green's theorem and the weak Neumann problem (boundary round, 2026-09-21)

The surface measure `IsContDiffDomain.boundaryMeasure`, the outward normal
`IsContDiffDomain.outwardNormal`, the divergence theorem and the trace of
`Numlib/Analysis/Sobolev/Boundary/` close the two numbered results of the section as far as
Green's identities carry them:

* `theorem_13_1_2` — the divergence theorem (13.1.4) on a bounded `C¹` plane domain, with the
  chapter's *inner* normal `n = −ν`; `theorem_13_1_2_polygon` on a triangulated polygon
  (`Triangulation.boundaryData`).  The chapter's piecewise smooth multiply connected region is
  not covered; see below.
* `theorem_13_1_1_neumann_weak` — the Neumann clause of Theorem 13.1.1 in weak form, on a bounded
  connected `C¹` domain: `∫_Ω ∇u·∇v = ∫_Γ f γv dσ` for all `v ∈ H¹(Ω)` is solvable if and only
  if `∫_Γ f dσ = 0`, uniquely up to a constant — Lax–Milgram on the mean-zero subspace, where the
  Dirichlet form is coercive by the Poincaré–Wirtinger inequality
  (`exists_norm_le_gradNorm_of_integral_eq_zero`, Deny–Lions), and the constants are the kernel
  of the Dirichlet form on a connected domain (`exists_fn_ae_eq_const_of_gradNorm_eq_zero`).

## Not formalized here

* The identification of the double layer operator with the boundary integral
  `∫_S ρ(Q) ∂/∂n_Q log |P - Q| dS_Q`: the surface measure and the normal now exist, but the
  identification needs the jump relations of the layer potentials.

* **Theorem 13.1.1, the classical clauses.**  For `f` continuous on a boundary `S` admitting a
  twice continuously differentiable parametrization, the interior Dirichlet problem has a unique
  solution, and the interior Neumann problem has a solution, unique up to an additive constant,
  exactly when `∫_S f dS = 0`.  This is the classical existence theory for the planar Laplace
  equation, which the book quotes from its own Chapter 8 rather than proving here.

  The *weak Neumann* clause is proved, as `theorem_13_1_1_neumann_weak` above.  What remains is
  the two classical clauses.  The **Dirichlet problem with merely continuous data** `f ∈ C(S)`:
  the variational route wants an `H¹` extension of `f`, that is `f ∈ H^{1/2}(S)`, and the range
  of the trace on a `C¹` domain is not characterized in this library; the potential route wants
  the layer potentials and their jump relations, which are the rest of §13.1 and are skipped.
  The **classical Neumann solution**, with `∂u/∂n = f` pointwise rather than in the weak sense:
  that needs boundary regularity of the weak solution — the `H²` Neumann estimate of
  `Numlib/Analysis/PDE/Elliptic/Regularity` and, beyond it, a `C²` version of it.  Uniqueness
  for the Dirichlet problem, by contrast, is within reach: it is the maximum principle, Mathlib's
  `HarmonicContOnCl`.

* **Theorem 13.1.2 in the chapter's own generality**: the divergence theorem on a multiply
  connected planar region whose boundary is a finite union of piecewise `C²` (or merely `C¹`)
  Jordan curves with corners.  The `C¹` case and the polygonal case are proved
  (`theorem_13_1_2`, `theorem_13_1_2_polygon`).  A region bounded by curves with corners that are
  neither straight nor `C¹` — a curved polygon — is a Lipschitz domain, and the Lipschitz theory
  is out of scope.  An arclength measure on a parametrized `C¹` curve, packaged as a
  `BoundaryData` (the plane case of a chart-based definition through `EuclideanSpace.gramDet`),
  would cover the *smooth* multiply connected case at about `600` lines; the curved-corner case
  needs in addition the piecewise gluing of `Boundary/Polygon.lean` for curved edges.  Nothing in
  the formalized part of the chapter depends on it.

* Everything the Kelvin transform is used *for*: the exterior Dirichlet and Neumann problems
  (13.1.14)–(13.1.23) rest on Theorem 13.1.1 above, and on the removable singularity statement
  for a bounded harmonic function on a punctured neighbourhood of the origin.
-/

open Set

namespace AtkinsonHan.Chapter13

open DividedDifference

/-- **(13.1.33)–(13.1.34), the parametrized double layer kernel** of a plane curve
`r(t) = (ξ(t), η(t))`, defined so as to be continuous on the diagonal:

`k(t, s) = (η'(s) ξ[s, s, t] - ξ'(s) η[s, s, t]) / (ξ[s, t]² + η[s, t]²)`,

which is the second display of (13.1.33) verbatim, with `ξ[s, t]` and `ξ[s, s, t]` the first and
second divided differences in their Hermite–Genocchi form.  Off the diagonal it is the first display
of (13.1.33) (`equation_13_1_33`), because the factor `(t - s)²` by which numerator and denominator
of that formula both vanish has been cancelled; on the diagonal it is minus half the signed
curvature (`equation_13_1_34`).

Only the first and second derivatives of the parametrization enter. -/
noncomputable def doubleLayerKernel (ξ' η' ξ'' η'' : ℝ → ℝ) (t s : ℝ) : ℝ :=
  (η' s * secondOrder ξ'' s t - ξ' s * secondOrder η'' s t) /
    (firstOrder ξ' s t ^ 2 + firstOrder η' s t ^ 2)

variable {ξ η ξ' η' ξ'' η'' : ℝ → ℝ}

/-- **(13.1.33)**: off the diagonal the kernel is the double layer kernel of the book,

`k(t, s) = [η'(s) (ξ(t) - ξ(s)) - ξ'(s) (η(t) - η(s))] / (|ξ(t) - ξ(s)|² + |η(t) - η(s)|²)`.

Both sides are the same quotient with the common factor `(t - s)²` cancelled, so no regularity of
the curve is needed here: only `s ≠ t`. -/
theorem equation_13_1_33 (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x)
    (hη : ∀ x, HasDerivAt η (η' x) x) (hη' : ∀ x, HasDerivAt η' (η'' x) x)
    (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'') (hcη' : Continuous η')
    (hcη'' : Continuous η'') {s t : ℝ} (hst : s ≠ t) :
    doubleLayerKernel ξ' η' ξ'' η'' t s =
      (η' s * (ξ t - ξ s) - ξ' s * (η t - η s)) / ((ξ t - ξ s) ^ 2 + (η t - η s) ^ 2) := by
  have hd : t - s ≠ 0 := sub_ne_zero.2 (Ne.symm hst)
  have hA : ξ t - ξ s = (t - s) * firstOrder ξ' s t := by
    have h := sub_eq_mul_firstOrder hξ hcξ' s t
    linear_combination -h
  have hB : η t - η s = (t - s) * firstOrder η' s t := by
    have h := sub_eq_mul_firstOrder hη hcη' s t
    linear_combination -h
  have hP : ξ' s = firstOrder ξ' s t + (s - t) * secondOrder ξ'' s t := by
    have := sub_firstOrder_eq hξ hξ' hcξ' hcξ'' s t
    linarith
  have hQ : η' s = firstOrder η' s t + (s - t) * secondOrder η'' s t := by
    have := sub_firstOrder_eq hη hη' hcη' hcη'' s t
    linarith
  rw [hA, hB, doubleLayerKernel]
  have hnum : η' s * ((t - s) * firstOrder ξ' s t) - ξ' s * ((t - s) * firstOrder η' s t)
      = (t - s) ^ 2 * (η' s * secondOrder ξ'' s t - ξ' s * secondOrder η'' s t) := by
    rw [hP, hQ]
    ring
  have hden : ((t - s) * firstOrder ξ' s t) ^ 2 + ((t - s) * firstOrder η' s t) ^ 2
      = (t - s) ^ 2 * (firstOrder ξ' s t ^ 2 + firstOrder η' s t ^ 2) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hd)]

/-- **The double layer kernel is minus the rate of turning of the chord.**  Write the curve as the
complex-valued `r(s) = ξ(s) + i η(s)`.  Off the diagonal,

`k(t, s) = -Im (r'(s) / (r(s) - r(t)))`,

and `Im (r'(s) / (r(s) - r(t)))` is `d/ds arg (r(s) - r(t))`: the kernel is minus the rate at which
the direction of the chord from the fixed boundary point `r(t)` to the moving point `r(s)` turns.
As in `equation_13_1_33`, no regularity of the curve is needed and the identity holds even where the
chord vanishes, both sides being `0` there.

This identity is what makes (13.2.20) and Exercise 13.2.5 *topology* rather than analysis: the
chord direction turns by `+π` in total along a counterclockwise regular simple closed curve — a
boundary-point form of Hopf's Umlaufsatz — so `∫_0^L k(t, s) ds = -π`, which is the constant of the
integral equation (13.1.32), and `|∫_0^L k(t, s) ds| = ∫_0^L |k(t, s)| ds` exactly when the region
is convex, so that the chord direction turns monotonically.  Mathlib has neither a continuous
argument along a plane curve nor a turning number, and that, rather than any missing analysis, is
what Exercise 13.2.5 waits on. -/
theorem doubleLayerKernel_eq_neg_im_div (hξ : ∀ x, HasDerivAt ξ (ξ' x) x)
    (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x) (hη : ∀ x, HasDerivAt η (η' x) x)
    (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'')
    (hcη' : Continuous η') (hcη'' : Continuous η'') {s t : ℝ} (hst : s ≠ t) :
    doubleLayerKernel ξ' η' ξ'' η'' t s
      = -(((ξ' s : ℂ) + (η' s : ℂ) * Complex.I) /
          (((ξ s : ℂ) + (η s : ℂ) * Complex.I) - ((ξ t : ℂ) + (η t : ℂ) * Complex.I))).im := by
  rw [equation_13_1_33 hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hst, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.normSq_apply, zero_add, add_zero,
    neg_zero, div_sub_div_same]
  rw [← neg_div]
  congr 1 <;> ring

/-- **(13.1.34)**: on the diagonal the parametrized double layer kernel is *minus half the signed
curvature*,

`k(t, t) = (η'(t) ξ''(t) - ξ'(t) η''(t)) / (2 (ξ'(t)² + η'(t)²))`.

For an arclength parametrization the denominator is `2`, and the value is `-κ(t) / 2`, with `κ` the
signed curvature of the counterclockwise parametrization: on the unit circle `κ = 1` and
`k(t, t) = -1/2`.  (The book's prose after (13.1.34) says "one-half the curvature", dropping the
sign; the display, which is what is stated here, is the one that is consistent with (13.1.33) and
with the inner normal of §13.1.  See the module doc.)

This continuity on the diagonal is what makes the kernel of a `C²` curve continuous, and hence the
double layer operator compact. -/
theorem equation_13_1_34 (ξ' η' ξ'' η'' : ℝ → ℝ) (t : ℝ) :
    doubleLayerKernel ξ' η' ξ'' η'' t t =
      (η' t * ξ'' t - ξ' t * η'' t) / (2 * (ξ' t ^ 2 + η' t ^ 2)) := by
  rw [doubleLayerKernel, firstOrder_self, firstOrder_self, secondOrder_self, secondOrder_self,
    show η' t * (ξ'' t / 2) - ξ' t * (η'' t / 2) = (η' t * ξ'' t - ξ' t * η'' t) / 2 from by ring,
    div_div]

/-- **The kernel of the unit circle is `-1/2` on the diagonal**, `r(t) = (cos t, sin t)` being the
counterclockwise parametrization of signed curvature `+1`.  Off the diagonal (13.1.33) gives the
same constant `-1/2` wherever the chord does not vanish, so the row integral over a period is `-π`
and (13.1.32) is `(-π + K) u = g`, as the book writes it.

This is the numerical check that fixes the sign of `doubleLayerKernel`: the book's *prose* after
(13.1.34), "one-half the curvature", would give `+1/2` here and a row integral of `+π`, which is not
the constant of the book's own integral equation.  See the module doc. -/
theorem doubleLayerKernel_circle_self (t : ℝ) :
    doubleLayerKernel (fun x => -Real.sin x) Real.cos (fun x => -Real.cos x)
      (fun x => -Real.sin x) t t = -(1 / 2) := by
  rw [equation_13_1_34]
  show (Real.cos t * -Real.cos t - -Real.sin t * -Real.sin t) /
    (2 * ((-Real.sin t) ^ 2 + Real.cos t ^ 2)) = -(1 / 2)
  rw [show Real.cos t * -Real.cos t - -Real.sin t * -Real.sin t
        = -(Real.sin t ^ 2 + Real.cos t ^ 2) from by ring,
    show (2 : ℝ) * ((-Real.sin t) ^ 2 + Real.cos t ^ 2)
        = 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) from by ring,
    Real.sin_sq_add_cos_sq]
  norm_num

/-- **The parametrized double layer kernel is continuous**, the diagonal included, wherever the
curve is regular and simple.

The hypothesis `hD` says that `|r(s) - r(t)|² / (s - t)²` is positive: on the diagonal it is
regularity, `ξ'(t)² + η'(t)² > 0`, and off it, by `equation_13_1_33`'s computation, it is
`r(s) ≠ r(t)`.  For a regular simple closed curve of period `L` it holds exactly for
`|s - t| < L`. -/
theorem continuous_doubleLayerKernel {X : Type*} [TopologicalSpace X] {p : X → ℝ × ℝ}
    (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'') (hcη' : Continuous η')
    (hcη'' : Continuous η'') (hp : Continuous p)
    (hD : ∀ x : X, firstOrder ξ' (p x).2 (p x).1 ^ 2 + firstOrder η' (p x).2 (p x).1 ^ 2 ≠ 0) :
    Continuous fun x => doubleLayerKernel ξ' η' ξ'' η'' (p x).1 (p x).2 := by
  have hswap : Continuous fun x => ((p x).2, (p x).1) := by fun_prop
  have h1 : Continuous fun x => firstOrder ξ' (p x).2 (p x).1 :=
    (continuous_firstOrder hcξ').comp hswap
  have h2 : Continuous fun x => firstOrder η' (p x).2 (p x).1 :=
    (continuous_firstOrder hcη').comp hswap
  have h3 : Continuous fun x => secondOrder ξ'' (p x).2 (p x).1 :=
    (continuous_secondOrder hcξ'').comp hswap
  have h4 : Continuous fun x => secondOrder η'' (p x).2 (p x).1 :=
    (continuous_secondOrder hcη'').comp hswap
  have hs : Continuous fun x => (p x).2 := continuous_snd.comp hp
  exact Continuous.div (((hcη'.comp hs).mul h3).sub ((hcξ'.comp hs).mul h4))
    ((h1.pow 2).add (h2.pow 2)) hD

/-- The parametrized double layer kernel as a continuous kernel on a parameter square, ready for
`IntegralOperator.fredholm`.  The hypothesis is that the curve is regular and simple on `[a, b]`. -/
noncomputable def doubleLayerKernelCM {a b : ℝ} (ξ' η' ξ'' η'' : ℝ → ℝ) (hcξ' : Continuous ξ')
    (hcξ'' : Continuous ξ'') (hcη' : Continuous η') (hcη'' : Continuous η'')
    (hD : ∀ p : Icc a b × Icc a b,
      firstOrder ξ' (p.2 : ℝ) (p.1 : ℝ) ^ 2 + firstOrder η' (p.2 : ℝ) (p.1 : ℝ) ^ 2 ≠ 0) :
    C(Icc a b × Icc a b, ℝ) :=
  ⟨fun p => doubleLayerKernel ξ' η' ξ'' η'' (p.1 : ℝ) (p.2 : ℝ),
    continuous_doubleLayerKernel (p := fun p : Icc a b × Icc a b => ((p.1 : ℝ), (p.2 : ℝ)))
      hcξ' hcξ'' hcη' hcη'' (by fun_prop) hD⟩

/-- **The double layer operator is compact.**  This is the last sentence of §13.1.3 — "the integral
operator `K` is a compact operator from `C_p(L)` to `C_p(L)`" — for the parametrized kernel on a
parameter interval on which the curve is regular and simple.

Given the continuity of the kernel, which is the content of `equation_13_1_34`, this is
`IntegralOperator.isCompactOperator_fredholm` and nothing else: the Arzelà–Ascoli argument was the
shared prerequisite of Chapter 12 and is proved there. -/
theorem isCompactOperator_doubleLayer {a b : ℝ} (hab : a ≤ b) (ξ' η' ξ'' η'' : ℝ → ℝ)
    (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'') (hcη' : Continuous η')
    (hcη'' : Continuous η'')
    (hD : ∀ p : Icc a b × Icc a b,
      firstOrder ξ' (p.2 : ℝ) (p.1 : ℝ) ^ 2 + firstOrder η' (p.2 : ℝ) (p.1 : ℝ) ^ 2 ≠ 0) :
    IsCompactOperator
      (IntegralOperator.fredholm hab
        (doubleLayerKernelCM ξ' η' ξ'' η'' hcξ' hcξ'' hcη' hcη'' hD)) :=
  IntegralOperator.isCompactOperator_fredholm hab _

/-! ### The descent to a closed curve -/

section Closed

variable {L : ℝ}

/-- The first divided difference is invariant under the *diagonal* translation by a period of the
derivative. -/
theorem firstOrder_add_period {f' : ℝ → ℝ} (hp : Function.Periodic f' L) (s t : ℝ) :
    firstOrder f' (s + L) (t + L) = firstOrder f' s t := by
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show s + L - (t + L) = s - t from by ring,
    show (s - t) * θ + (t + L) = (s - t) * θ + t + L from by ring, hp]

/-- The second divided difference is invariant under the *diagonal* translation by a period of the
second derivative. -/
theorem secondOrder_add_period {f'' : ℝ → ℝ} (hp : Function.Periodic f'' L) (s t : ℝ) :
    secondOrder f'' (s + L) (t + L) = secondOrder f'' s t := by
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show t + L - (s + L) = t - s from by ring,
    show (t - s) * θ + (s + L) = (t - s) * θ + s + L from by ring, hp]

/-- **The parametrized double layer kernel is invariant under the diagonal translation**
`(t, s) ↦ (t + L, s + L)`, and under that one only.  It is *not* separately `L`-periodic in either
argument: `k(t + L, t) = 0` while `k(t, t)` is minus half the signed curvature, because the divided
differences divide by `s - t`, and `s - t` and `s - t - L` are different divisors of the same
vanishing chord.
This is why the kernel on the circle is built by choosing the representative of the *difference*
`s - t`, and not by lifting a biperiodic function. -/
theorem doubleLayerKernel_add_period (hpξ' : Function.Periodic ξ' L)
    (hpη' : Function.Periodic η' L) (hpξ'' : Function.Periodic ξ'' L)
    (hpη'' : Function.Periodic η'' L) (t s : ℝ) :
    doubleLayerKernel ξ' η' ξ'' η'' (t + L) (s + L) = doubleLayerKernel ξ' η' ξ'' η'' t s := by
  rw [doubleLayerKernel, doubleLayerKernel, hpξ', hpη', secondOrder_add_period hpη'',
    secondOrder_add_period hpξ'', firstOrder_add_period hpξ', firstOrder_add_period hpη']

/-- A period of a differentiable function is a period of its derivative. -/
theorem periodic_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hp : Function.Periodic f L) : Function.Periodic f' L := by
  intro x
  have hshift : (fun y : ℝ => f (y + L)) = f := funext hp
  have h2 : HasDerivAt (fun y : ℝ => f (y + L)) (f' (x + L)) x :=
    HasDerivAt.comp_add_const x L (hf (x + L))
  rw [hshift] at h2
  exact h2.unique (hf x)

/-- **The seam identity**: the two parameters at distance `L/2` on either side of `t` give the same
value of the kernel, because they are the same point of the closed curve.  Both are off the
diagonal, so this is `equation_13_1_33` together with the periodicity of the parametrization. -/
theorem doubleLayerKernel_sub_half_period (hL : 0 < L) (hξ : ∀ x, HasDerivAt ξ (ξ' x) x)
    (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x) (hη : ∀ x, HasDerivAt η (η' x) x)
    (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'')
    (hcη' : Continuous η') (hcη'' : Continuous η'') (hpξ : Function.Periodic ξ L)
    (hpη : Function.Periodic η L) (t : ℝ) :
    doubleLayerKernel ξ' η' ξ'' η'' t (t - L / 2)
      = doubleLayerKernel ξ' η' ξ'' η'' t (t + L / 2) := by
  have hpξ' : Function.Periodic ξ' L := periodic_of_hasDerivAt hξ hpξ
  have hpη' : Function.Periodic η' L := periodic_of_hasDerivAt hη hpη
  have hne1 : t - L / 2 ≠ t := by intro h; linarith
  have hne2 : t + L / 2 ≠ t := by intro h; linarith
  have hsum : t + L / 2 = (t - L / 2) + L := by ring
  rw [equation_13_1_33 hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hne1,
    equation_13_1_33 hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hne2, hsum, hpξ, hpη, hpξ', hpη']

/-- **The parametrized double layer kernel of a closed curve, as a function on the torus.**  For a
point `(T, S)` of `AddCircle L × AddCircle L` it takes the representative `t` of `T` in `[0, L)` and
the representative `d` of `S - T` in `[-L/2, L/2)`, and evaluates `doubleLayerKernel` at
`(t, t + d)`.

Choosing the representative of the *difference* is what makes this well defined: the kernel is
invariant under the diagonal translation (`doubleLayerKernel_add_period`) and under nothing else. -/
noncomputable def doubleLayerKernelCPFun (L : ℝ) [Fact (0 < L)] (ξ' η' ξ'' η'' : ℝ → ℝ)
    (p : AddCircle L × AddCircle L) : ℝ :=
  doubleLayerKernel ξ' η' ξ'' η'' (AddCircle.equivIco L 0 p.1)
    ((AddCircle.equivIco L 0 p.1 : ℝ) + (AddCircle.equivIco L (-(L / 2)) (p.2 - p.1) : ℝ))

variable [hL : Fact (0 < L)]

/-- On the representatives themselves the circle kernel is the kernel of the line. -/
theorem doubleLayerKernelCPFun_coe_of_mem {t u : ℝ} (ht : t ∈ Ico (0 : ℝ) L)
    (hu : u ∈ Ico (-(L / 2)) (L / 2)) :
    doubleLayerKernelCPFun L ξ' η' ξ'' η'' ((t : AddCircle L), ((t + u : ℝ) : AddCircle L))
      = doubleLayerKernel ξ' η' ξ'' η'' t (t + u) := by
  have hd : (((t + u : ℝ) : AddCircle L) - (t : AddCircle L)) = ((u : ℝ) : AddCircle L) := by
    rw [← AddCircle.coe_sub]
    congr 1
    ring
  have ht' : (AddCircle.equivIco L 0 (t : AddCircle L) : ℝ) = t :=
    AddCircle.equivIco_coe_of_mem (by simpa using ht)
  have hu' : (AddCircle.equivIco L (-(L / 2)) (((u : ℝ) : AddCircle L)) : ℝ) = u :=
    AddCircle.equivIco_coe_of_mem (by rw [show -(L / 2) + L = L / 2 from by ring]; exact hu)
  rw [doubleLayerKernelCPFun, hd, ht', hu']

/-- **The parametrized double layer kernel of a regular simple closed curve, on the torus.**  This
is the form §13.2 uses: `C_p(L) = C(AddCircle L, ℝ)` and the kernel is a continuous function of the
pair of arclength parameters, so `IntegralOperator.kernelCLM volume` of it is the compact operator
`K` of (13.2.4).

The hypothesis `hD` is that the curve is regular and simple: `|r(t + u) - r(t)|²/u²` does not
vanish for `|u| ≤ L/2`, which on the diagonal is `ξ'(t)² + η'(t)² > 0` and off it is injectivity of
the parametrization on a half period. -/
noncomputable def doubleLayerKernelCP (L : ℝ) [Fact (0 < L)] {ξ η ξ' η' ξ'' η'' : ℝ → ℝ}
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x)
    (hη : ∀ x, HasDerivAt η (η' x) x) (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ')
    (hcξ'' : Continuous ξ'') (hcη' : Continuous η') (hcη'' : Continuous η'')
    (hpξ : Function.Periodic ξ L) (hpη : Function.Periodic η L)
    (hD : ∀ t u : ℝ, |u| ≤ L / 2 →
      firstOrder ξ' (t + u) t ^ 2
        + firstOrder η' (t + u) t ^ 2 ≠ 0) :
    C(AddCircle L × AddCircle L, ℝ) := by
  refine ⟨doubleLayerKernelCPFun L ξ' η' ξ'' η'', ?_⟩
  have hLpos : 0 < L := Fact.out
  have hpξ' : Function.Periodic ξ' L := periodic_of_hasDerivAt hξ hpξ
  have hpη' : Function.Periodic η' L := periodic_of_hasDerivAt hη hpη
  have hpξ'' : Function.Periodic ξ'' L := periodic_of_hasDerivAt hξ' hpξ'
  have hpη'' : Function.Periodic η'' L := periodic_of_hasDerivAt hη' hpη'
  set Θ : Icc (0 : ℝ) L × Icc (-(L / 2)) (L / 2) → AddCircle L × AddCircle L :=
    fun q => (((q.1 : ℝ) : AddCircle L), (((q.1 : ℝ) + (q.2 : ℝ) : ℝ) : AddCircle L)) with hΘ
  have hcoe : Continuous fun x : ℝ => (x : AddCircle L) := AddCircle.continuous_mk' L
  have hΘc : Continuous Θ := by
    rw [hΘ]
    exact (hcoe.comp (continuous_subtype_val.comp continuous_fst)).prodMk
      (hcoe.comp ((continuous_subtype_val.comp continuous_fst).add
        (continuous_subtype_val.comp continuous_snd)))
  have hΘs : Function.Surjective Θ := by
    rintro ⟨T, S⟩
    have ht : ((AddCircle.equivIco L 0 T : ℝ)) ∈ Ico (0 : ℝ) (0 + L) :=
      (AddCircle.equivIco L 0 T).2
    have hu : ((AddCircle.equivIco L (-(L / 2)) (S - T) : ℝ)) ∈ Ico (-(L / 2)) (-(L / 2) + L) :=
      (AddCircle.equivIco L (-(L / 2)) (S - T)).2
    refine ⟨(⟨(AddCircle.equivIco L 0 T : ℝ), ⟨ht.1, by linarith [ht.2]⟩⟩,
      ⟨(AddCircle.equivIco L (-(L / 2)) (S - T) : ℝ), ⟨hu.1, by linarith [hu.2]⟩⟩), ?_⟩
    have e1 : (((AddCircle.equivIco L 0 T : ℝ)) : AddCircle L) = T := AddCircle.coe_equivIco
    have e2 : ((((AddCircle.equivIco L 0 T : ℝ)
        + (AddCircle.equivIco L (-(L / 2)) (S - T) : ℝ) : ℝ)) : AddCircle L) = S := by
      rw [AddCircle.coe_add, AddCircle.coe_equivIco, AddCircle.coe_equivIco]
      abel
    exact Prod.ext e1 e2
  have hq : Topology.IsQuotientMap Θ := Topology.IsQuotientMap.of_surjective_continuous hΘs hΘc
  rw [hq.continuous_iff]
  -- the composite is the kernel of the line, read on the compact parameter rectangle
  have hIco : (-(L / 2)) ∈ Ico (-(L / 2)) (L / 2) := ⟨le_rfl, by linarith⟩
  have hkey : ∀ q : Icc (0 : ℝ) L × Icc (-(L / 2)) (L / 2),
      doubleLayerKernelCPFun L ξ' η' ξ'' η'' (Θ q)
        = doubleLayerKernel ξ' η' ξ'' η'' (q.1 : ℝ) ((q.1 : ℝ) + (q.2 : ℝ)) := by
    rintro ⟨⟨t, ht⟩, ⟨u, hu⟩⟩
    simp only [hΘ]
    -- reduce the difference to `[-L/2, L/2)`
    have hred : ∀ s : ℝ, s ∈ Ico (0 : ℝ) L →
        doubleLayerKernelCPFun L ξ' η' ξ'' η'' ((s : AddCircle L), ((s + u : ℝ) : AddCircle L))
          = doubleLayerKernel ξ' η' ξ'' η'' s (s + u) := by
      intro s hs
      rcases eq_or_lt_of_le hu.2 with hu2 | hu2
      · have hcoeq : ((s + u : ℝ) : AddCircle L) = ((s + -(L / 2) : ℝ) : AddCircle L) := by
          rw [show s + u = (s + -(L / 2)) + L from by rw [hu2]; ring, AddCircle.coe_add_period]
        rw [hcoeq, doubleLayerKernelCPFun_coe_of_mem hs hIco, hu2,
          show s + -(L / 2) = s - L / 2 from by ring,
          doubleLayerKernel_sub_half_period hLpos hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hpξ hpη s]
      · exact doubleLayerKernelCPFun_coe_of_mem hs ⟨hu.1, hu2⟩
    rcases eq_or_lt_of_le ht.2 with ht2 | ht2
    · have h0 : ((t : ℝ) : AddCircle L) = ((0 : ℝ) : AddCircle L) := by
        rw [ht2]
        simp [AddCircle.coe_period]
      have h1 : ((t + u : ℝ) : AddCircle L) = ((0 + u : ℝ) : AddCircle L) := by
        rw [ht2, show L + u = (0 + u) + L from by ring, AddCircle.coe_add_period]
      have hshift : doubleLayerKernel ξ' η' ξ'' η'' L (L + u)
          = doubleLayerKernel ξ' η' ξ'' η'' 0 (0 + u) := by
        have hs := doubleLayerKernel_add_period hpξ' hpη' hpξ'' hpη'' (0 : ℝ) (0 + u)
        rw [show (0 : ℝ) + L = L from by ring,
          show (0 : ℝ) + u + L = L + u from by ring] at hs
        exact hs
      rw [h0, h1, hred 0 ⟨le_rfl, hLpos⟩, ht2, hshift]
    · exact hred t ⟨ht.1, ht2⟩
  simp only [Function.comp_def, hkey]
  exact continuous_doubleLayerKernel hcξ' hcξ'' hcη' hcη''
    (p := fun q : Icc (0 : ℝ) L × Icc (-(L / 2)) (L / 2) => ((q.1 : ℝ), (q.1 : ℝ) + (q.2 : ℝ)))
    (by fun_prop) fun q => by
      simpa using hD (q.1 : ℝ) (q.2 : ℝ) (abs_le.2 ⟨q.2.2.1, q.2.2.2⟩)

/-- **The double layer operator of a closed curve is compact on `C_p(L)`.**  This is the last
sentence of §13.1.3 in the form §13.2 uses it: the kernel `doubleLayerKernelCP` is continuous on
`AddCircle L × AddCircle L`, so the integral operator it defines on `C(AddCircle L, ℝ)` is compact
by `IntegralOperator.isCompactOperator_kernelCLM`. -/
theorem isCompactOperator_doubleLayerCP (L : ℝ) [Fact (0 < L)] {ξ η ξ' η' ξ'' η'' : ℝ → ℝ}
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x)
    (hη : ∀ x, HasDerivAt η (η' x) x) (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ')
    (hcξ'' : Continuous ξ'') (hcη' : Continuous η') (hcη'' : Continuous η'')
    (hpξ : Function.Periodic ξ L) (hpη : Function.Periodic η L)
    (hD : ∀ t u : ℝ, |u| ≤ L / 2 →
      firstOrder ξ' (t + u) t ^ 2 + firstOrder η' (t + u) t ^ 2 ≠ 0) :
    IsCompactOperator (IntegralOperator.kernelCLM MeasureTheory.volume
      (doubleLayerKernelCP L hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hpξ hpη hD)) :=
  IntegralOperator.isCompactOperator_kernelCLM _ _

end Closed

/-! ### §13.1.2, the Kelvin transform -/

section Kelvin

open InnerProductSpace

/-- **(13.1.10), (13.1.12): the Kelvin transform** of a function on a planar region.  Inversion in
the unit circle is `T (x, y) = (x, y) / r²` with `r = |(x, y)|`, an involution of
`ℝ² \ {0}`, and the Kelvin transform of `u` is `û = u ∘ T`; the book writes `û (T P) = u (P)`,
which is the same thing because `T ∘ T` is the identity.  Identifying the plane with `ℂ`,
`T z = z / ‖z‖²`.

In dimension two the transform carries no `‖x‖^(2 - d)` weight, so `kelvin` is a plain
precomposition. -/
noncomputable def kelvin (u : ℂ → ℝ) (x : ℂ) : ℝ := u (x / (‖x‖ ^ 2 : ℝ))

/-- Inversion in the unit circle is `z ↦ 1 / conj z`.  The identity holds at `0` too, both sides
being `0` there. -/
theorem div_norm_sq_eq_inv_conj (z : ℂ) :
    z / ((‖z‖ ^ 2 : ℝ) : ℂ) = ((starRingEnd ℂ) z)⁻¹ := by
  rw [Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **(13.1.13): the Kelvin transform preserves harmonicity.**  If `u` is harmonic at the inverse
point `T x = x / ‖x‖²` then `û = u ∘ T` is harmonic at `x`; this is the book's computation
`Δ û (ξ, η) = r⁴ Δ u (x, y)`, which is what turns the exterior Dirichlet and Neumann problems on
`D_e` into interior problems on `T (D_e)`.

Identifying the plane with `ℂ`, `T z = conj (z⁻¹)` is anticonformal, and the statement is that
harmonicity survives precomposition with an inversion and with a reflection:
`InnerProductSpace.HarmonicAt.comp_analyticAt` and `InnerProductSpace.HarmonicAt.comp_conj` of
`Numlib/Analysis/Complex/Harmonic`. -/
theorem kelvin_harmonic {u : ℂ → ℝ} {x : ℂ} (hx : x ≠ 0)
    (hu : HarmonicAt u (x / ((‖x‖ ^ 2 : ℝ) : ℂ))) : HarmonicAt (kelvin u) x := by
  have hinv : AnalyticAt ℂ (fun z : ℂ => z⁻¹) x := (analyticAt_id (𝕜 := ℂ) (z := x)).inv hx
  have hconj : HarmonicAt (fun w : ℂ => u ((starRingEnd ℂ) w)) x⁻¹ := by
    refine InnerProductSpace.HarmonicAt.comp_conj ?_
    rwa [map_inv₀, ← div_norm_sq_eq_inv_conj]
  have hcomp := InnerProductSpace.HarmonicAt.comp_analyticAt
    (u := fun w : ℂ => u ((starRingEnd ℂ) w)) (g := fun z : ℂ => z⁻¹) hconj hinv
  have hfun : kelvin u = fun z : ℂ => u ((starRingEnd ℂ) z⁻¹) := by
    funext z
    rw [kelvin, div_norm_sq_eq_inv_conj, map_inv₀]
  rw [hfun]
  exact hcomp

end Kelvin

/-! ### Theorem 13.1.2: the divergence theorem with the chapter's inner normal -/

section Divergence

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

/-- **Theorem 13.1.2 (the divergence theorem)** on a bounded `C¹` plane domain `Ω ⊆ ℝ²`
(`hΩ : IsContDiffDomain 1 Ω`, `hb`; the chapter's piecewise smooth multiply connected region is
not covered — see the module doc), with the chapter's *inner* unit normal `n = −ν` — `ν` being the
outward normal `IsContDiffDomain.outwardNormal` of `Numlib/Analysis/Sobolev/Boundary/` — and the
arclength measure `dΓ = σ` (`IsContDiffDomain.boundaryMeasure`), for `F : ℝ² → ℝ²` with both
components in `C¹(Ω̄)` (`ContinuousOn F (closure Ω)`, `ContDiffOnClosure ℝ 1 F Ω`):

  `∫_Ω ∇·F dΩ = −∫_Γ F·n dΓ`  (13.1.4).

The field `BoundaryData.integral_div_eq` of the boundary data `hΩ.boundaryData hb`, read with
the sign convention of the chapter (`inner_neg_right`). Green's identities (13.1.5)–(13.1.6)
follow with `F = u ∇w` (`BoundaryData.integral_laplacian_mul_add_eq`), as the chapter derives
them. -/
theorem theorem_13_1_2 {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2))))
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF₀ : ContinuousOn F (closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin 2))), EuclideanSpace.div F x
      = -∫ x, ⟪F x, -(hΩ.boundaryData hb).ν x⟫_ℝ ∂(hΩ.boundaryData hb).σ := by
  simp only [inner_neg_right, integral_neg, neg_neg]
  exact (hΩ.boundaryData hb).integral_div_eq F hF₀ hF₁

/-- **Theorem 13.1.2 on a triangulated polygon** `Ω ⊆ ℝ²` (`𝒯 : Triangulation Ω`): with the
inner normal `n = −ν` and the arclength measure `dΓ = σ` of the polygon
(`Triangulation.boundaryData`, `Numlib/Analysis/Sobolev/Boundary/Polygon.lean`), for `F` with
both components in `C¹(Ω̄)`, `∫_Ω ∇·F dΩ = −∫_Γ F·n dΓ`. The polygonal case of the chapter's
"boundaries need not be smooth". -/
theorem theorem_13_1_2_polygon {Ω : Opens (EuclideanSpace ℝ (Fin 2))} (𝒯 : Triangulation Ω)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF₀ : ContinuousOn F (closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin 2))), EuclideanSpace.div F x
      = -∫ x, ⟪F x, -𝒯.boundaryData.ν x⟫_ℝ ∂𝒯.boundaryData.σ := by
  simp only [inner_neg_right, integral_neg, neg_neg]
  exact 𝒯.boundaryData.integral_div_eq F hF₀ hF₁

end Divergence

/-! ### Theorem 13.1.1: the weak Neumann problem -/

section Neumann

open MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace NNReal

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- `ℝ^{d+1}`, locally. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The constant function `1` as an element of `H¹(Ω)` on a bounded open set, with vanishing
weak derivatives. -/
theorem exists_one (hb : Bornology.IsBounded (Ω : Set 𝔼)) :
    ∃ one : SobolevEuclidean (d + 1) 1 2 Ω,
      SobolevMultiIndex.fn one =ᵐ[volume.restrict (Ω : Set 𝔼)] (fun _ ↦ (1 : ℝ)) ∧
      ∀ i, (SobolevMultiIndex.weakDeriv one (MultiIndexLE.single i) : 𝔼 → ℝ)
        =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ 0 := by
  obtain ⟨one, hone⟩ : ∃ one : SobolevEuclidean (d + 1) 1 2 Ω,
      SobolevMultiIndex.fn one =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ (1 : ℝ) :=
    ((contDiffOn_const (c := (1 : ℝ))).contDiffOnClosure Ω.isOpen).memSobolevMultiIndex_of_isBounded
      Ω hb 2 |>.exists_sobolevMultiIndex
  refine ⟨one, hone, fun i ↦ ?_⟩
  have h := Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω
    (contDiffOn_const (c := (1 : ℝ))) hone i
  filter_upwards [h] with x hx
  simp only [hx, fderiv_fun_const, Pi.zero_apply, zero_apply]

/-- **The Poincaré–Wirtinger inequality on a bounded connected `C¹` domain**: there is `C > 0`
with `‖v‖_{H¹} ≤ C ‖∇v‖_{L²}` for every `v ∈ H¹(Ω)` of mean zero. The Deny–Lions inequality
`SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected` (Theorem 7.3.12 with
the one seminorm `|∫_Ω v|`) on the extension domain `Ω`
(`IsSobolevExtensionDomain.of_isContDiffDomain`): a constant of mean zero on a set of positive
measure is zero. -/
theorem exists_norm_le_gradNorm_of_integral_eq_zero (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hc : IsConnected (Ω : Set 𝔼)) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
      ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn v x = 0 →
        ‖v‖ ≤ C * SobolevMultiIndex.gradNorm v := by
  have hΩo := Ω.isOpen
  have hvol : volume (Ω : Set 𝔼) ≠ ⊤ := hb.measure_lt_top.ne
  have hvolpos : 0 < (volume (Ω : Set 𝔼)).toReal :=
    ENNReal.toReal_pos (hΩo.measure_pos volume hc.nonempty).ne' hvol
  obtain ⟨one, hone, -⟩ := exists_one hb
  -- the mean functional
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ,
      ∀ v, ℓ₀ v = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn v x :=
    ⟨Elliptic.load Ω (SobolevMultiIndex.weakDeriv one 0), fun v ↦ by
      rw [Elliptic.load_apply]
      refine integral_congr_ae ?_
      filter_upwards [hone] with x hx
      change SobolevMultiIndex.fn one x * _ = _
      rw [hx, one_mul]⟩
  have hext : IsSobolevExtensionDomain (d + 1) 2 Ω :=
    IsSobolevExtensionDomain.of_isContDiffDomain hΩ
      (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).isBounded
  -- (H2): a constant of mean zero is zero
  have h2 : ∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
      (∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0,
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) → ℓ₀ v = 0 → v = 0 := by
    rintro v ⟨q, hq, hvq⟩ hℓv
    rw [MvPolynomial.mem_restrictTotalDegree, Nat.le_zero,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
    have hvc : SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ q.coeff 0 := by
      filter_upwards [hvq] with x hx
      rw [hx]
      conv_lhs => rw [hq]
      rw [MvPolynomial.eval_C]
    rw [hℓ₀, integral_congr_ae hvc, setIntegral_const, smul_eq_mul] at hℓv
    have hc0 : q.coeff 0 = 0 :=
      (mul_eq_zero.1 hℓv).resolve_left (by rw [measureReal_def]; exact hvolpos.ne')
    refine SobolevMultiIndex.ext_of_fn_ae_eq (hvc.trans ?_)
    rw [hc0]
    exact SobolevMultiIndex.fn_zero.symm
  have : Fact ((1 : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨C, hC, hle⟩ := SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected
    (k := 0) (p := 2) hext hvol hc.isPreconnected ℓ₀ fun v hv h0 ↦ h2 v hv h0
  refine ⟨C, hC, fun v hv ↦ ?_⟩
  have h := hle v
  have e : SobolevMultiIndex.topSeminorm ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (0 + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω volume v = SobolevMultiIndex.gradNorm v :=
    SobolevMultiIndex.topSeminorm_one_eq_gradNorm v
  have e2 : ℓ₀ v = 0 := by rw [hℓ₀]; exact hv
  rw [e] at h
  have h' : ‖v‖ ≤ C * (SobolevMultiIndex.gradNorm v + |ℓ₀ v|) := h
  rw [e2, abs_zero, add_zero] at h'
  exact h'

/-- **An `H¹` function with vanishing gradient on a connected open set is a constant** almost
everywhere: Deny–Lions at order one
(`SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero`, the
polynomials of degree `0`). -/
theorem exists_fn_ae_eq_const_of_gradNorm_eq_zero (hc : IsPreconnected (Ω : Set 𝔼))
    {w : SobolevEuclidean (d + 1) 1 2 Ω} (hw : SobolevMultiIndex.gradNorm w = 0) :
    ∃ c : ℝ, SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ c := by
  have : Fact ((1 : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  have htop : SobolevMultiIndex.topSeminorm ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (0 + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω volume w = 0 := by
    have e : SobolevMultiIndex.topSeminorm ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (0 + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω volume w = SobolevMultiIndex.gradNorm w :=
      SobolevMultiIndex.topSeminorm_one_eq_gradNorm w
    rw [e]
    exact hw
  obtain ⟨q, hq, hwq⟩ :=
    SobolevEuclidean.exists_mem_restrictTotalDegree_ae_eq_of_topSeminorm_eq_zero (k := 0) (p := 2)
      hc htop
  rw [MvPolynomial.mem_restrictTotalDegree, Nat.le_zero,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
  have hwq' : SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun x ↦ MvPolynomial.eval (fun i ↦ x i) q := hwq
  refine ⟨q.coeff 0, ?_⟩
  filter_upwards [hwq'] with x hx
  rw [hx]
  conv_lhs => rw [hq]
  rw [MvPolynomial.eval_C]

/-- **Lax–Milgram on the mean-zero subspace**: if `‖v‖ ≤ C ‖∇v‖` on the kernel of a bounded
functional `ℓ₀`, the Dirichlet form is coercive there and every bounded functional `F` is
represented on the kernel: `∃ u₀, ∀ v, ℓ₀ v = 0 → ∫_Ω ∇u₀·∇v = F(v)`
(`IsGalerkinSolution.existsUnique_of_restrict`). -/
theorem exists_forall_dirichletForm_eq_of_ker {ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ}
    {C : ℝ} (hC : 0 < C)
    (hle : ∀ v : SobolevEuclidean (d + 1) 1 2 Ω, ℓ₀ v = 0 → ‖v‖ ≤ C * SobolevMultiIndex.gradNorm v)
    (F : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ) :
    ∃ u₀ : SobolevEuclidean (d + 1) 1 2 Ω, ∀ v, ℓ₀ v = 0 → Elliptic.dirichletForm Ω u₀ v = F v := by
  have hcoer : ((Elliptic.dirichletForm Ω).restrict
      (LinearMap.ker (ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →ₗ[ℝ] ℝ))).IsCoerciveWith
      (C⁻¹ ^ 2) := by
    rintro ⟨v, hv⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
    have h1 := hle v hv
    have h2 : C⁻¹ * ‖v‖ ≤ SobolevMultiIndex.gradNorm v := by
      rw [inv_mul_le_iff₀ hC]
      exact h1
    simp only [SesqForm.restrict_apply, RCLike.re_to_real,
      Elliptic.dirichletForm_self_eq_gradNorm_sq]
    calc C⁻¹ ^ 2 * ‖v‖ ^ 2 = (C⁻¹ * ‖v‖) ^ 2 := by ring
      _ ≤ SobolevMultiIndex.gradNorm v ^ 2 := by gcongr
  have : CompleteSpace (LinearMap.ker (ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →ₗ[ℝ] ℝ)) :=
    ℓ₀.isClosed_ker.completeSpace_coe
  obtain ⟨u₀, ⟨-, hu₀⟩, -⟩ := IsGalerkinSolution.existsUnique_of_restrict (ℓ := F)
    (by positivity) hcoer
  exact ⟨u₀, fun v hv ↦ hu₀ v (by rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact hv)⟩

/-- **Lax–Milgram for the weak Neumann problem** on a bounded connected `C¹` domain: for a
bounded functional `F` on `H¹(Ω)` vanishing on the constant function `1`, there is `u₀ ∈ H¹(Ω)`
with `∫_Ω ∇u₀·∇v = F(v)` for all `v ∈ H¹(Ω)`. Lax–Milgram on the closed subspace of mean-zero
functions, where the Dirichlet form is coercive by the Poincaré–Wirtinger inequality
(`exists_norm_le_gradNorm_of_integral_eq_zero`, `exists_forall_dirichletForm_eq_of_ker`), and
the decomposition `v = v₀ + c·1` with `c = (∫_Ω v)/|Ω|`. -/
theorem exists_forall_dirichletForm_eq (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hc : IsConnected (Ω : Set 𝔼))
    {one : SobolevEuclidean (d + 1) 1 2 Ω}
    (hone : SobolevMultiIndex.fn one =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ (1 : ℝ))
    (hd1 : ∀ u : SobolevEuclidean (d + 1) 1 2 Ω, Elliptic.dirichletForm Ω u one = 0)
    (F : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ) (hF1 : F one = 0) :
    ∃ u₀ : SobolevEuclidean (d + 1) 1 2 Ω, ∀ v, Elliptic.dirichletForm Ω u₀ v = F v := by
  have hΩo := Ω.isOpen
  have hvol : volume (Ω : Set 𝔼) ≠ ⊤ := hb.measure_lt_top.ne
  have hvolpos : 0 < (volume (Ω : Set 𝔼)).toReal :=
    ENNReal.toReal_pos (hΩo.measure_pos volume hc.nonempty).ne' hvol
  -- the mean functional
  obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ₀ : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ,
      ∀ v, ℓ₀ v = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn v x :=
    ⟨Elliptic.load Ω (SobolevMultiIndex.weakDeriv one 0), fun v ↦ by
      rw [Elliptic.load_apply]
      refine integral_congr_ae ?_
      filter_upwards [hone] with x hx
      change SobolevMultiIndex.fn one x * _ = _
      rw [hx, one_mul]⟩
  have hℓ₀one : ℓ₀ one = (volume (Ω : Set 𝔼)).toReal := by
    rw [hℓ₀, integral_congr_ae hone, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  obtain ⟨C, hC, hle⟩ := exists_norm_le_gradNorm_of_integral_eq_zero hΩ hb hc
  obtain ⟨u₀, hu₀⟩ := exists_forall_dirichletForm_eq_of_ker hC
    (fun v hv ↦ hle v (by rw [← hℓ₀]; exact hv)) F
  refine ⟨u₀, fun v ↦ ?_⟩
  -- `v = v₀ + c 1` with `v₀` of mean zero
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ℓ₀ v / ℓ₀ one := ⟨_, rfl⟩
  have hℓ₀one' : ℓ₀ one ≠ 0 := by rw [hℓ₀one]; exact hvolpos.ne'
  have hv₀ : ℓ₀ (v - c • one) = 0 := by
    simp only [ℓ₀.map_sub v (c • one), ℓ₀.map_smul c one, smul_eq_mul]
    rw [hcdef, div_mul_cancel₀ _ hℓ₀one', sub_self]
  have e1 : Elliptic.dirichletForm Ω u₀ (v - c • one)
      = Elliptic.dirichletForm Ω u₀ v - c * Elliptic.dirichletForm Ω u₀ one := by
    simp only [(Elliptic.dirichletForm Ω u₀).map_sub v (c • one),
      (Elliptic.dirichletForm Ω u₀).map_smul c one, smul_eq_mul]
  have e2 : F (v - c • one) = F v - c * F one := by
    simp only [F.map_sub v (c • one), F.map_smul c one, smul_eq_mul]
  have e3 := hu₀ _ hv₀
  rw [e1, e2, hd1, hF1] at e3
  linarith

/-- **Theorem 13.1.1, the Neumann clause in weak form**, on a bounded connected `C¹` domain
`Ω ⊆ ℝ^{d+1}` (`hΩ : IsContDiffDomain 1 Ω`, `hb`, `hc : IsConnected Ω`; the chapter's region
with a `C²` boundary curve is the plane case), with the arclength measure
`σ = hΩ.boundaryMeasure hb` and the trace `γ = hΩ.traceL hb 2 : H¹(Ω) →L L²(σ)` of
`Numlib/Analysis/Sobolev/Boundary/`,
for `f ∈ L²(σ)`: the weak Neumann problem (13.1.2), `Δu = 0` in `Ω`, `∂u/∂n = f` on `Γ` —
find `u ∈ H¹(Ω)` with

  `∫_Ω ∇u·∇v dx = ∫_Γ f γv dσ`  for all `v ∈ H¹(Ω)`

— has a solution if and only if `∫_Γ f dσ = 0` (13.1.3), and the solution is unique up to the
addition of an arbitrary constant. This is the part of Theorem 13.1.1 that Green's identities
carry; the book quotes it from its Chapter 8. Necessity: test with `v = 1` (`∇1 = 0`, `γ1 = 1`).
Existence: Lax–Milgram on the mean-zero subspace, where the Dirichlet form is coercive by the
Poincaré–Wirtinger inequality (`exists_forall_dirichletForm_eq`), and `v ↦ ∫_Γ f γv dσ` is
bounded and vanishes on the constants when `∫_Γ f dσ = 0`. Uniqueness: two solutions differ by
`w` with `∫_Ω |∇w|² = 0`, a constant on the connected `Ω`
(`exists_fn_ae_eq_const_of_gradNorm_eq_zero`). The classical clauses of Theorem 13.1.1 — the
Dirichlet problem with continuous data and the pointwise Neumann condition — are not formalized;
the module doc says what they would need. -/
theorem theorem_13_1_1_neumann_weak (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hc : IsConnected (Ω : Set 𝔼))
    (f : Lp ℝ 2 (hΩ.boundaryMeasure hb)) :
    ((∃ u : SobolevEuclidean (d + 1) 1 2 Ω, ∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
        = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂(hΩ.boundaryMeasure hb))
      ↔ ∫ x, f x ∂(hΩ.boundaryMeasure hb) = 0) ∧
    ∀ u u' : SobolevEuclidean (d + 1) 1 2 Ω,
      (∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
        = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
            ∂(hΩ.boundaryMeasure hb)) →
      (∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, SobolevMultiIndex.weakDeriv u' (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
        = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
            ∂(hΩ.boundaryMeasure hb)) →
      ∃ c : ℝ, SobolevMultiIndex.fn u' =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun x ↦ SobolevMultiIndex.fn u x + c := by
  obtain ⟨one, hone, hdone⟩ := exists_one hb
  have hγone : (hΩ.traceL hb 2 ENNReal.ofNat_ne_top one : 𝔼 → ℝ) =ᵐ[hΩ.boundaryMeasure hb]
      fun _ ↦ (1 : ℝ) :=
    hΩ.traceL_ae_eq_of_continuousOn hb 2 ENNReal.ofNat_ne_top one hone continuousOn_const
  -- the Dirichlet form vanishes against `1`
  have hd1 : ∀ u : SobolevEuclidean (d + 1) 1 2 Ω, Elliptic.dirichletForm Ω u one = 0 := by
    intro u
    rw [Elliptic.dirichletForm_apply]
    rw [← integral_zero 𝔼 ℝ (μ := volume.restrict (Ω : Set 𝔼))]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hdone] with x hx
    simp only [hx, mul_zero, Finset.sum_const_zero]
  -- the boundary functional `v ↦ ∫ f γv dσ`
  obtain ⟨Fσ, hFσ⟩ : ∃ Fσ : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ,
      ∀ v, Fσ v = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
        ∂(hΩ.boundaryMeasure hb) :=
    ⟨(innerSL ℝ f).comp (hΩ.traceL hb 2 ENNReal.ofNat_ne_top), fun v ↦ by
      rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_eq_integral_mul]⟩
  have hFσone : Fσ one = ∫ x, f x ∂(hΩ.boundaryMeasure hb) := by
    rw [hFσ]
    refine integral_congr_ae ?_
    filter_upwards [hγone] with x hx
    rw [hx, mul_one]
  -- the problem in the backbone's vocabulary
  have hsol : ∀ u : SobolevEuclidean (d + 1) 1 2 Ω,
      (∀ v : SobolevEuclidean (d + 1) 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), ∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
        = ∫ x, f x * (hΩ.traceL hb 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
            ∂(hΩ.boundaryMeasure hb)) ↔
      ∀ v, Elliptic.dirichletForm Ω u v = Fσ v := fun u ↦ by
    simp only [Elliptic.dirichletForm_apply, hFσ]
  simp only [hsol]
  refine ⟨⟨fun ⟨u, hu⟩ ↦ ?_, fun hf ↦ ?_⟩, fun u u' hu hu' ↦ ?_⟩
  · -- necessity: test with `v = 1`
    rw [← hFσone, ← hu one, hd1]
  · -- existence
    exact exists_forall_dirichletForm_eq hΩ hb hc hone hd1 Fσ (hFσone.trans hf)
  · -- uniqueness up to a constant
    obtain ⟨w, hwdef⟩ : ∃ w : SobolevEuclidean (d + 1) 1 2 Ω, w = u' - u := ⟨_, rfl⟩
    have hw : ∀ v, Elliptic.dirichletForm Ω w v = 0 := fun v ↦ by
      rw [hwdef, map_sub, sub_apply, hu v, hu' v, sub_self]
    have hgrad : SobolevMultiIndex.gradNorm w = 0 := by
      have h := hw w
      rw [Elliptic.dirichletForm_self_eq_gradNorm_sq] at h
      exact pow_eq_zero_iff two_ne_zero |>.1 h
    obtain ⟨c, hwc⟩ := exists_fn_ae_eq_const_of_gradNorm_eq_zero hc.isPreconnected hgrad
    refine ⟨c, ?_⟩
    have e : u' = u + w := by rw [hwdef, add_sub_cancel]
    rw [e]
    filter_upwards [SobolevMultiIndex.fn_add u w, hwc] with x hx hx'
    rw [hx, Pi.add_apply, hx']

end Neumann

end AtkinsonHan.Chapter13
