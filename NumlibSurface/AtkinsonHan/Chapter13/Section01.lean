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
* `doubleLayerKernelCM` — the kernel as a `C(Icc a b × Icc a b, ℝ)` on a parameter interval on
  which the curve is regular and simple, and `isCompactOperator_doubleLayer`, that the resulting
  integral operator is compact.

## Not formalized here

* The identification of this operator with the boundary integral
  `∫_S ρ(Q) ∂/∂n_Q log |P - Q| dS_Q`, which needs a surface measure and a normal field on `S`.
* The descent of the kernel to `C_p(L) = C(AddCircle L, ℝ)` for a *closed* curve of period `L`,
  which is the form §13.2 uses.  Note that `doubleLayerKernel` is *not* separately `L`-periodic:
  `k(t + L, t) = 0` by `equation_13_1_33`, since `t` and `t + L` are distinct real parameters and
  the chord between them vanishes, whereas `k(t, t)` is half the curvature.  What is invariant is
  the *diagonal* translation `(t, s) ↦ (t + L, s + L)`, so the kernel on the circle is obtained by
  choosing the representative of `s - t` in `[-L/2, L/2)`; the plan node `doubleLayerKernelCP`
  writes out the three steps.  Until that is done, the compactness statement below is for a
  parameter interval on which the curve is simple, which for a closed curve means one shorter than
  the period.
* §13.1.2, the Kelvin transform: reachable from Mathlib's `HarmonicOnNhd` and the identification of
  harmonic functions with real parts of holomorphic ones in the plane, but isolated — nothing else
  in the corpus consumes it.  See the plan.
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

end AtkinsonHan.Chapter13
