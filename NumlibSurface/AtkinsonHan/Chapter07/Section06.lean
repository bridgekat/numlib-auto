import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import NumlibSurface.AtkinsonHan.Chapter07.Section03

/-!
# Atkinson–Han §7.6: integration by parts formulas

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.6.

The section is the Gauss–Green formula `∫_Ω u_{x_i} v = ∫_Γ u v ν_i ds − ∫_Ω u v_{x_i}` on a
domain `Ω` with boundary `Γ` and outward unit normal `ν`: the classical formula for
`u, v ∈ C¹(Ω̄)` (`proposition_7_6_1_classical`), its extension by a density argument to
`u, v ∈ H¹(Ω)` (**Proposition 7.6.1**, `proposition_7_6_1`) and further to conjugate pairs
`u ∈ W^{1,p}(Ω)`, `v ∈ W^{1,p^*}(Ω)`, `1/p + 1/p^* = 1` ((7.6.3), `proposition_7_6_1_conj`), from
which the book derives its Green's identities.

The book states the section for a Lipschitz domain, whose boundary carries a surface measure and
an outward normal defined almost everywhere. Lipschitz domains are out of scope, as everywhere in
this chapter; the formalization has the bounded `C¹` domains of Definition 7.2.1
(`hΩ : IsContDiffDomain 1 Ω`, `hb : Bornology.IsBounded Ω`), on which
`Numlib/Analysis/Sobolev/Boundary/` provides the surface measure `σ = hΩ.boundaryMeasure hb` on
`Γ = ∂Ω` (a measure on the ambient space carried by `Γ`), the outward unit normal
`ν = hΩ.outwardNormal hb` (a function on the ambient space, of norm one `σ`-almost everywhere),
the divergence theorem for `C¹(Ω̄)` fields (`IsContDiffDomain.integral_div_eq`) and the trace
`γ_p = hΩ.traceL hb p hp : W^{1,p}(Ω) →L L^p(Γ)` of Theorem 7.3.10. The classical formula is the
divergence theorem for the field `(u v) e_i` (`BoundaryData.integral_fderiv_mul_add_eq`), and the
Sobolev formula is the field `green` of the trace family `IsContDiffDomain.traceFamily`, proved in
`Numlib/Analysis/Sobolev/Boundary/Trace.lean` by the book's density argument: the classical formula
for the smooth approximants of Theorem 7.3.2, the continuity of the trace (Theorem 7.3.10 (b)) for
the boundary term, and Hölder's inequality for the interior terms. The boundary term is written
with the traces, `∫_Γ (γ u)(γ v) ν_i dσ`, since `u` and `v` are defined only almost everywhere
in `Ω`. The polygon case, on a triangulated plane domain without slits, is the open
`proposition_7_6_1_polygon`.
-/

open Filter MeasureTheory Set TopologicalSpace SobolevMultiIndex

open scoped ContDiff ENNReal NNReal Topology

namespace AtkinsonHan.Chapter07

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The classical Gauss–Green formula** displayed before Proposition 7.6.1, on a bounded `C¹`
domain `Ω ⊆ ℝ^{d+1}` with boundary `Γ`, surface measure `σ` and outward unit normal `ν`:
`∫_Ω u_{x_i} v dx = ∫_Γ u v ν_i ds − ∫_Ω u v_{x_i} dx` for all `u, v ∈ C¹(Ω̄)` — functions
continuous on `closure Ω` and `C¹` on `Ω` with derivative extending continuously to `closure Ω`
(`ContDiffOnClosure`). The book calls it Gauss's formula or the divergence theorem; it is the
backbone's `BoundaryData.integral_fderiv_mul_add_eq`, the divergence theorem
`IsContDiffDomain.integral_div_eq` applied to the field `(u v) e_i`. The book's Lipschitz domain
is out of scope and restated as `C¹` (see the module documentation). -/
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

/-- **Proposition 7.6.1**, the formula (7.6.1), on a bounded `C¹` domain `Ω ⊆ ℝ^{d+1}` with
boundary `Γ`, surface measure `σ`, outward unit normal `ν` and trace `γ : H¹(Ω) → L²(Γ)`
(Theorem 7.3.10): `∫_Ω u_{x_i} v dx = ∫_Γ u v ν_i ds − ∫_Ω u v_{x_i} dx` for all `u, v ∈ H¹(Ω)`,
where `u_{x_i} = ∂_i u` is the weak derivative and the boundary term is
`∫_Γ (γ u)(γ v) ν_i dσ`, the boundary values of `u` and `v` being their traces. `H¹(Ω)` is the
space of Definition 7.2.2 in the book's own indexing,
`SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 2 Ω volume`.

The book's proof is the density argument: the classical formula (`proposition_7_6_1_classical`)
for sequences `u_n, v_n ∈ C¹(Ω̄)` converging to `u, v` in `H¹(Ω)` (Theorem 7.3.2), the interior
terms passing to the limit by the Cauchy–Schwarz inequality and the boundary term by the
continuity of the trace (Theorem 7.3.10 (b)). This is the field `green` of the backbone's trace
family (`IsContDiffDomain.green` at `p = q = 2`, `BoundaryData.green_of_hasSmoothDensity` in
`Numlib/Analysis/Sobolev/Boundary/Trace.lean`). The book's Lipschitz domain is out of scope and
restated as `C¹`. -/
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

/-- **The formula (7.6.3)**, the extension of Proposition 7.6.1 to conjugate exponents: on a
bounded `C¹` domain with boundary `Γ`, surface measure `σ`, outward normal `ν` and traces
`γ_p : W^{1,p}(Ω) → L^p(Γ)`, `γ_{p^*} : W^{1,p^*}(Ω) → L^{p^*}(Γ)` (Theorem 7.3.10),
`∫_Ω u_{x_i} v dx = ∫_Γ (γ_p u)(γ_{p^*} v) ν_i dσ − ∫_Ω u v_{x_i} dx` for all `u ∈ W^{1,p}(Ω)`
and `v ∈ W^{1,p^*}(Ω)`, where `p, p^* ∈ (1, ∞)` are conjugate, `1/p + 1/p^* = 1` — the class
`ENNReal.HolderConjugate p q` (`ENNReal.holderConjugate_iff`), with `p, q ≠ ∞` and `1 ≤ p, q`
(which conjugacy makes `1 < p, q < ∞`). The same density argument as Proposition 7.6.1 with
Hölder's inequality in place of Cauchy–Schwarz: the field `green` of the backbone's trace family
at `(p, p^*)` (`IsContDiffDomain.green`). The book's Lipschitz domain is out of scope and
restated as `C¹`. -/
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

end AtkinsonHan.Chapter07
