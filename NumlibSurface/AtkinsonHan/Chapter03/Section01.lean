import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Approximation.Muntz

/-!
# Atkinson–Han §3.1: the Weierstrass approximation theorems

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.1.

## Main results

* `theorem_3_1_1` — Weierstrass: the polynomials are dense in `C[a, b]`.
* `theorem_3_1_2` — Stone–Weierstrass: a subalgebra of `C(D, ℝ)` for compact `D` that separates
  points is dense.
* `corollary_3_1_3` — the polynomials in `d` variables are dense in `C(D, ℝ)` for compact
  `D ⊆ ℝ^d`.
* `corollary_3_1_4` — the trigonometric polynomials are dense in `C_p(2π)`.
* `theorem_3_1_5` — Müntz–Szász: for `0 < λ₁ < λ₂ < ⋯ → ∞`, the span of `t ↦ t ^ λⱼ` is dense in
  `L²(0, 1)` if and only if `∑ 1 / λⱼ = ∞`.

The first two are Mathlib's. Corollary 3.1.3 is Theorem 3.1.2 applied to the image of
`MvPolynomial (Fin d) ℝ` in `C(D, ℝ)`, which contains the constants and separates points because
the coordinate functions do; `ℝ^d` is read as `Fin d → ℝ`, and by Theorem 1.2.14 the choice of
norm on it does not matter, only the topology. Corollary 3.1.4 is the backbone's
`exists_mem_span_trigFun_norm_sub_lt` of `Numlib/Analysis/Fourier/TrigonometricBasis`:
`span_fourier_closure_eq_top` — the density of the *complex* exponentials in `C(AddCircle T, ℂ)` —
carried to the real system `trigFun` by taking real parts. It is what makes the trigonometric
system complete in Theorem 1.3.13 and what Theorem 4.1.2 needs.

`C_p(2π)`, the continuous `2π`-periodic functions with the uniform norm, is `C(AddCircle (2π), ℝ)`,
as everywhere in this surface.

## Müntz's theorem

Theorem 3.1.5 is the backbone's `Muntz.dense_span_powerL2_iff` of `Numlib/Approximation/Muntz`,
proved there through Gram determinants: the Gram matrix of finitely many powers in `L²(0, 1)` is a
Cauchy matrix, Gram's formula turns the distance from `tᵃ` to their span into a product
`(2a + 1)⁻¹ ∏ᵢ ((a - λᵢ) / (a + λᵢ + 1))²`, and that product tends to `0` exactly when
`∑ 1/λᵢ` diverges.
-/

open Complex Filter MeasureTheory Set Submodule

open scoped Polynomial Real Topology

namespace AtkinsonHan.Chapter03

/-- **Theorem 3.1.1** (Weierstrass). The polynomials are dense in `C[a, b]` with the uniform norm:
every continuous `f` on `[a, b]` is within `ε` of a polynomial. -/
theorem theorem_3_1_1 (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ‖p.toContinuousMapOn (Set.Icc a b) - f‖ < ε :=
  exists_polynomial_near_continuousMap a b f ε hε

/-- **Theorem 3.1.2** (Stone–Weierstrass). A subalgebra of `C(D, ℝ)` for a compact `D` that
separates the points of `D` is dense. The book states it for a linear subspace closed under
products and containing the constants, which is exactly a subalgebra. -/
theorem theorem_3_1_2 {D : Type*} [TopologicalSpace D] [CompactSpace D] (A : Subalgebra ℝ C(D, ℝ))
    (hA : A.SeparatesPoints) : A.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA

/-- **Corollary 3.1.3.** The polynomials in `d` variables are dense in `C(D, ℝ)` for a compact
`D ⊆ ℝ^d`: every continuous `f` on `D` is uniformly within `ε` of a multivariate polynomial. -/
theorem corollary_3_1_3 {d : ℕ} {D : Set (Fin d → ℝ)} (hD : IsCompact D) (f : C(D, ℝ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin d) ℝ, ∀ x : D, |MvPolynomial.eval (x : Fin d → ℝ) p - f x| < ε := by
  have : CompactSpace D := isCompact_iff_compactSpace.mp hD
  -- the `d` coordinate functions, as elements of `C(D, ℝ)`
  set φ : Fin d → C(D, ℝ) :=
    fun i => ⟨fun x => (x : Fin d → ℝ) i, (continuous_apply i).comp continuous_subtype_val⟩
  set A : Subalgebra ℝ C(D, ℝ) := (MvPolynomial.aeval φ).range
  have hmem : ∀ i, φ i ∈ A := fun i => ⟨MvPolynomial.X i, by simp⟩
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, (x : Fin d → ℝ) i ≠ (y : Fin d → ℝ) i := by
      by_contra h
      exact hxy (Subtype.ext (funext fun i => not_not.mp (not_exists.mp h i)))
    exact ⟨⇑(φ i), ⟨φ i, hmem i, rfl⟩, hi⟩
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hsep f ε hε
  obtain ⟨p, hp⟩ := g.2
  refine ⟨p, fun x => ?_⟩
  have hx := (ContinuousMap.norm_lt_iff _ hε).mp hg x
  have hval : MvPolynomial.eval (x : Fin d → ℝ) p = (MvPolynomial.aeval φ) p x :=
    (MvPolynomial.comp_aeval_apply φ (ContinuousMap.evalAlgHom ℝ ℝ x) p).symm
  have hgp : (MvPolynomial.aeval φ) p = (g : C(D, ℝ)) := hp
  rw [hval, hgp]
  simpa [Real.norm_eq_abs] using hx

section Trigonometric

variable {T : ℝ}

/-- **Corollary 3.1.4.** The trigonometric polynomials are dense in `C_p(2π)`, the continuous
`2π`-periodic functions with the uniform norm: every such `f` is uniformly within `ε` of a real
linear combination of `1`, `cos (j x)` and `sin (j x)`.

Stated on `C(AddCircle T, ℝ)` for any period `T > 0`; the book's `C_p(2π)` is `T = 2π`. The system
`trigFun T` is the one of Theorem 1.3.13, so its real span is exactly the trigonometric
polynomials; the density is the backbone's `exists_mem_span_trigFun_norm_sub_lt`. -/
theorem corollary_3_1_4 [Fact (0 < T)] (f : C(AddCircle T, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ span ℝ (Set.range (trigFun T)), ‖p - f‖ < ε :=
  exists_mem_span_trigFun_norm_sub_lt f hε

end Trigonometric

section Muntz

/-! ### Theorem 3.1.5: the Müntz–Szász theorem

`L²(0, 1)` is `Lp ℝ 2 μ₁` for the Lebesgue measure `μ₁` restricted to the open unit interval;
`Muntz.powerL2 l` is the power `t ↦ t ^ l` as an element of it.
-/

/-- The measure of `L²(0, 1)`: Lebesgue measure restricted to the open unit interval. -/
local notation "μ₁" => MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- **Theorem 3.1.5** (Müntz). Let `0 < λ₁ < λ₂ < ⋯` with `λⱼ → ∞`. The span of the powers
`t ↦ t ^ λⱼ` is dense in `L²(0, 1)` if and only if `∑ 1 / λⱼ = ∞`.

The sequence is indexed from `0` here, so the book's `λ₁` is `lam 0`, and the divergence of
`∑ 1 / λⱼ` is stated as the failure of `Summable`, the terms being positive. -/
theorem theorem_3_1_5 (lam : ℕ → ℝ) (hpos : 0 < lam 0) (hmono : StrictMono lam)
    (htop : Tendsto lam atTop atTop) :
    Dense ((Submodule.span ℝ (Set.range fun j ↦ Muntz.powerL2 (lam j)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁))
      ↔ ¬ Summable fun j ↦ (lam j)⁻¹ :=
  Muntz.dense_span_powerL2_iff lam hpos hmono htop

end Muntz

end AtkinsonHan.Chapter03
