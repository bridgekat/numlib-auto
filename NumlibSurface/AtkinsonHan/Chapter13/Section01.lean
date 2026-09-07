import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.AddCircle.Real
import Numlib.Analysis.Complex.Harmonic
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

`k(t, s) = [η'(s) (ξ(s) - ξ(t)) - ξ'(s) (η(s) - η(t))] / |r(s) - r(t)|²`,

a `0/0` quotient on the diagonal.  Numerator and denominator both vanish to second order there, and
(13.1.34) says the quotient extends continuously with `k(t, t)` equal to **half the curvature**.
That is the whole of the analysis needed to make the double layer operator a *compact* operator, and
it is what this file provides.

The kernel is therefore *defined* by the quotient of divided differences that is already continuous,
`Numlib/Approximation/DividedDifference`, rather than by the displayed formula with a case
distinction at `s = t`; `equation_13_1_33` then recovers the book's formula off the diagonal and
`equation_13_1_34` the diagonal value.  Only the derivatives `ξ', η', ξ'', η''` enter the
definition.

## Main results

* `doubleLayerKernel`, with `equation_13_1_33` and `equation_13_1_34`.
* `doubleLayerKernel_eq_im_div`, that off the diagonal the kernel is `Im (r'(s) / (r(s) - r(t)))`,
  the rate of turning of the chord from `r(t)` to `r(s)` — the identity that makes the row integral
  of Exercise 13.2.5 a turning number.
* `doubleLayerKernelCM` — the kernel as a `C(Icc a b × Icc a b, ℝ)` on a parameter interval on
  which the curve is regular and simple, and `isCompactOperator_doubleLayer`, that the resulting
  integral operator is compact.
* `doubleLayerKernelCP` — the same for a regular simple *closed* curve of period `L`, as a
  `C(AddCircle L × AddCircle L, ℝ)`, with `isCompactOperator_doubleLayerCP`.  This is the form
  §13.2 uses, `C_p(L) = C(AddCircle L, ℝ)`.

  The descent is *not* a lift of a biperiodic function: `doubleLayerKernel` is not separately
  `L`-periodic, because `k(t + L, t) = 0` by `equation_13_1_33` — the real parameters `t` and
  `t + L` are distinct and the chord between them vanishes — whereas `k(t, t)` is half the
  curvature.  What is invariant is the *diagonal* translation `(t, s) ↦ (t + L, s + L)`
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

## Not formalized here

* The identification of this operator with the boundary integral
  `∫_S ρ(Q) ∂/∂n_Q log |P - Q| dS_Q`, which needs a surface measure and a normal field on `S`.
* Everything the Kelvin transform is used *for*: the exterior Dirichlet and Neumann problems
  (13.1.14)–(13.1.23) rest on Theorem 13.1.1, quoted by the book from Chapter 8, and on the
  removable singularity statement for a bounded harmonic function on a punctured neighbourhood of
  the origin.
-/

open Set

namespace AtkinsonHan.Chapter13

open DividedDifference

/-- **(13.1.33)–(13.1.34), the parametrized double layer kernel** of a plane curve
`r(t) = (ξ(t), η(t))`, defined so as to be continuous on the diagonal:

`k(t, s) = (ξ'(s) η[s, s, t] - η'(s) ξ[s, s, t]) / (ξ[s, t]² + η[s, t]²)`,

with `ξ[s, t]` and `ξ[s, s, t]` the first and second divided differences in their Hermite–Genocchi
form.  Off the diagonal this is the book's (13.1.33) (`equation_13_1_33`), because the factor
`(s - t)²` by which numerator and denominator of that formula both vanish has been cancelled; on the
diagonal it is half the curvature (`equation_13_1_34`).

Only the first and second derivatives of the parametrization enter. -/
noncomputable def doubleLayerKernel (ξ' η' ξ'' η'' : ℝ → ℝ) (t s : ℝ) : ℝ :=
  (ξ' s * secondOrder η'' s t - η' s * secondOrder ξ'' s t) /
    (firstOrder ξ' s t ^ 2 + firstOrder η' s t ^ 2)

variable {ξ η ξ' η' ξ'' η'' : ℝ → ℝ}

/-- **(13.1.33)**: off the diagonal the kernel is the double layer kernel of the book,

`k(t, s) = [η'(s) (ξ(s) - ξ(t)) - ξ'(s) (η(s) - η(t))] / (|ξ(s) - ξ(t)|² + |η(s) - η(t)|²)`.

Both sides are the same quotient with the common factor `(s - t)²` cancelled, so no regularity of
the curve is needed here: only `s ≠ t`. -/
theorem equation_13_1_33 (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x)
    (hη : ∀ x, HasDerivAt η (η' x) x) (hη' : ∀ x, HasDerivAt η' (η'' x) x)
    (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'') (hcη' : Continuous η')
    (hcη'' : Continuous η'') {s t : ℝ} (hst : s ≠ t) :
    doubleLayerKernel ξ' η' ξ'' η'' t s =
      (η' s * (ξ s - ξ t) - ξ' s * (η s - η t)) / ((ξ s - ξ t) ^ 2 + (η s - η t) ^ 2) := by
  have hd : s - t ≠ 0 := sub_ne_zero.2 hst
  have hA : ξ s - ξ t = (s - t) * firstOrder ξ' s t := sub_eq_mul_firstOrder hξ hcξ' s t
  have hB : η s - η t = (s - t) * firstOrder η' s t := sub_eq_mul_firstOrder hη hcη' s t
  have hP : ξ' s = firstOrder ξ' s t + (s - t) * secondOrder ξ'' s t := by
    have := sub_firstOrder_eq hξ hξ' hcξ' hcξ'' s t
    linarith
  have hQ : η' s = firstOrder η' s t + (s - t) * secondOrder η'' s t := by
    have := sub_firstOrder_eq hη hη' hcη' hcη'' s t
    linarith
  rw [hA, hB, doubleLayerKernel]
  have hnum : η' s * ((s - t) * firstOrder ξ' s t) - ξ' s * ((s - t) * firstOrder η' s t)
      = (s - t) ^ 2 * (ξ' s * secondOrder η'' s t - η' s * secondOrder ξ'' s t) := by
    rw [hP, hQ]
    ring
  have hden : ((s - t) * firstOrder ξ' s t) ^ 2 + ((s - t) * firstOrder η' s t) ^ 2
      = (s - t) ^ 2 * (firstOrder ξ' s t ^ 2 + firstOrder η' s t ^ 2) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hd)]

/-- **The double layer kernel is the rate of turning of the chord.**  Write the curve as the
complex-valued `r(s) = ξ(s) + i η(s)`.  Off the diagonal,

`k(t, s) = Im (r'(s) / (r(s) - r(t)))`,

and the right-hand side is `d/ds arg (r(s) - r(t))`: the kernel measures how fast the direction of
the chord from the fixed boundary point `r(t)` to the moving point `r(s)` turns.  As in
`equation_13_1_33`, no regularity of the curve is needed and the identity holds even where the
chord vanishes, both sides being `0` there.

This identity is what makes (13.2.20) and Exercise 13.2.5 *topology* rather than analysis:
`∫_0^L k(t, s) ds` is the total turning of the chord direction, which is `-π` for a regular simple
closed curve — a boundary-point form of Hopf's Umlaufsatz — and equals `∫_0^L |k(t, s)| ds` exactly
when the region is convex, so that the chord direction turns monotonically.  Mathlib has neither a
continuous argument along a plane curve nor a turning number, and that, rather than any missing
analysis, is what Exercise 13.2.5 waits on. -/
theorem doubleLayerKernel_eq_im_div (hξ : ∀ x, HasDerivAt ξ (ξ' x) x)
    (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x) (hη : ∀ x, HasDerivAt η (η' x) x)
    (hη' : ∀ x, HasDerivAt η' (η'' x) x) (hcξ' : Continuous ξ') (hcξ'' : Continuous ξ'')
    (hcη' : Continuous η') (hcη'' : Continuous η'') {s t : ℝ} (hst : s ≠ t) :
    doubleLayerKernel ξ' η' ξ'' η'' t s
      = (((ξ' s : ℂ) + (η' s : ℂ) * Complex.I) /
          (((ξ s : ℂ) + (η s : ℂ) * Complex.I) - ((ξ t : ℂ) + (η t : ℂ) * Complex.I))).im := by
  rw [equation_13_1_33 hξ hξ' hη hη' hcξ' hcξ'' hcη' hcη'' hst, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, Complex.normSq_apply, zero_add, add_zero,
    neg_zero, div_sub_div_same]
  congr 1
  ring

/-- **(13.1.34)**: on the diagonal the parametrized double layer kernel is *half the curvature*,

`k(t, t) = (ξ'(t) η''(t) - η'(t) ξ''(t)) / (2 (ξ'(t)² + η'(t)²))`.

For an arclength parametrization the denominator is `2`, and the value is `κ(t) / 2`.  This is what
makes the kernel of a `C²` curve continuous, and hence the double layer operator compact. -/
theorem equation_13_1_34 (ξ' η' ξ'' η'' : ℝ → ℝ) (t : ℝ) :
    doubleLayerKernel ξ' η' ξ'' η'' t t =
      (ξ' t * η'' t - η' t * ξ'' t) / (2 * (ξ' t ^ 2 + η' t ^ 2)) := by
  rw [doubleLayerKernel, firstOrder_self, firstOrder_self, secondOrder_self, secondOrder_self,
    show ξ' t * (η'' t / 2) - η' t * (ξ'' t / 2) = (ξ' t * η'' t - η' t * ξ'' t) / 2 from by ring,
    div_div]

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
  exact Continuous.div (((hcξ'.comp hs).mul h4).sub ((hcη'.comp hs).mul h3))
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
argument: `k(t + L, t) = 0` while `k(t, t)` is half the curvature, because the divided differences
divide by `s - t` and `s - t` and `s - t - L` are different divisors of the same vanishing chord.
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

end AtkinsonHan.Chapter13
