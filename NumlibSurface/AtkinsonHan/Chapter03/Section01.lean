import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Numlib.Analysis.Fourier.TrigonometricBasis

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

The first two are Mathlib's. Corollary 3.1.3 is Theorem 3.1.2 applied to the image of
`MvPolynomial (Fin d) ℝ` in `C(D, ℝ)`, which contains the constants and separates points because
the coordinate functions do; `ℝ^d` is read as `Fin d → ℝ`, and by Theorem 1.2.14 the choice of
norm on it does not matter, only the topology. Corollary 3.1.4 is
`span_fourier_closure_eq_top` — the density of the *complex* exponentials in `C(AddCircle T, ℂ)` —
carried to the real system `trigFun` of `Numlib/Analysis/Fourier/TrigonometricBasis` by taking real
parts: the real and imaginary parts of a complex trigonometric polynomial are real trigonometric
polynomials, and taking real parts does not increase the uniform norm. It is what makes the
trigonometric system complete in Theorem 1.3.13 and what Theorem 4.1.2 needs.

`C_p(2π)`, the continuous `2π`-periodic functions with the uniform norm, is `C(AddCircle (2π), ℝ)`,
as everywhere in this surface.

## Not formalized here

Theorem 3.1.5, Müntz's theorem: the Müntz–Szász theorem is not in Mathlib, its proof is a
development of its own, and no other result in the corpus uses it. The Gram matrix of the system
`t ↦ t ^ λⱼ` in `L²(0, 1)` is the Cauchy matrix `(λᵢ + λⱼ + 1)⁻¹`, whose determinant the classical
proof computes; that determinant is `Matrix.det_cauchy` of `Numlib/LinearAlgebra/Matrix/Cauchy`,
and `plans/NumlibSurface/AtkinsonHan/Chapter03/Section01.toml` records what else the route needs.
-/

open Complex MeasureTheory Set Submodule

open scoped Polynomial Real

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

/-- Taking real parts, as a real-linear map on continuous complex-valued functions. -/
private noncomputable def reMap (X : Type*) [TopologicalSpace X] : C(X, ℂ) →ₗ[ℝ] C(X, ℝ) :=
  (Complex.reCLM.compLeftContinuous ℝ X).toLinearMap

/-- Taking imaginary parts, as a real-linear map on continuous complex-valued functions. -/
private noncomputable def imMap (X : Type*) [TopologicalSpace X] : C(X, ℂ) →ₗ[ℝ] C(X, ℝ) :=
  (Complex.imCLM.compLeftContinuous ℝ X).toLinearMap

@[simp]
private theorem reMap_apply {X : Type*} [TopologicalSpace X] (P : C(X, ℂ)) (x : X) :
    reMap X P x = (P x).re :=
  rfl

@[simp]
private theorem imMap_apply {X : Type*} [TopologicalSpace X] (P : C(X, ℂ)) (x : X) :
    imMap X P x = (P x).im :=
  rfl

/-- The real trigonometric polynomials: the real span of the system `trigFun` of
`Numlib/Analysis/Fourier/TrigonometricBasis`, that is, of `1`, `cos (2 π n x / T)` and
`sin (2 π n x / T)`. -/
private def trigPoly (T : ℝ) : Submodule ℝ C(AddCircle T, ℝ) :=
  span ℝ (Set.range (trigFun T))

private theorem sqrt_two_ne_zero : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)

/-- The real and imaginary parts of a complex exponential are real trigonometric polynomials. -/
private theorem reMap_imMap_fourier_mem (n : ℤ) :
    reMap (AddCircle T) (fourier n) ∈ trigPoly T ∧
      imMap (AddCircle T) (fourier n) ∈ trigPoly T := by
  have hgen : ∀ m : ℤ, trigFun T m ∈ trigPoly T := fun m => subset_span ⟨m, rfl⟩
  have hre : ∀ m : ℤ, 0 < m →
      reMap (AddCircle T) (fourier m) = (√2 : ℝ)⁻¹ • trigFun T m := by
    intro m hm
    ext x
    rw [reMap_apply, ContinuousMap.smul_apply, trigFun_apply, trigWeight_of_pos hm, re_ofReal_mul,
      smul_eq_mul, inv_mul_cancel_left₀ sqrt_two_ne_zero]
  have him : ∀ m : ℤ, 0 < m →
      imMap (AddCircle T) (fourier m) = (√2 : ℝ)⁻¹ • trigFun T (-m) := by
    intro m hm
    ext x
    rw [imMap_apply, ContinuousMap.smul_apply, trigFun_apply, trigWeight_of_neg (by omega),
      mul_assoc, re_ofReal_mul, fourier_neg, smul_eq_mul, Complex.I_mul_re, Complex.conj_im,
      neg_neg, inv_mul_cancel_left₀ sqrt_two_ne_zero]
  have hconj : ∀ m : ℤ, reMap (AddCircle T) (fourier (-m)) = reMap (AddCircle T) (fourier m) ∧
      imMap (AddCircle T) (fourier (-m)) = -imMap (AddCircle T) (fourier m) := by
    refine fun m => ⟨?_, ?_⟩
    · ext x
      rw [reMap_apply, reMap_apply, fourier_neg, Complex.conj_re]
    · ext x
      rw [ContinuousMap.neg_apply, imMap_apply, imMap_apply, fourier_neg, Complex.conj_im]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨hr, hi⟩ := hconj (-n)
    rw [neg_neg] at hr hi
    refine ⟨?_, ?_⟩
    · rw [hr, hre (-n) (by omega)]
      exact smul_mem _ _ (hgen _)
    · rw [hi, him (-n) (by omega)]
      exact neg_mem (smul_mem _ _ (hgen _))
  · refine ⟨?_, ?_⟩
    · have : reMap (AddCircle T) (fourier (0 : ℤ)) = trigFun T 0 := by
        ext x; simp
      rw [this]; exact hgen 0
    · have : imMap (AddCircle T) (fourier (0 : ℤ)) = 0 := by
        ext x; simp
      rw [this]; exact zero_mem _
  · exact ⟨by rw [hre n hn]; exact smul_mem _ _ (hgen _),
      by rw [him n hn]; exact smul_mem _ _ (hgen _)⟩

/-- The real and imaginary parts of a complex trigonometric polynomial are real trigonometric
polynomials. The two halves have to be proved together, because a complex scalar multiple mixes
them. -/
private theorem reMap_imMap_mem_of_mem_span {P : C(AddCircle T, ℂ)}
    (hP : P ∈ span ℂ (Set.range (fourier (T := T)))) :
    reMap (AddCircle T) P ∈ trigPoly T ∧ imMap (AddCircle T) P ∈ trigPoly T := by
  induction hP using Submodule.span_induction with
  | mem P hP => obtain ⟨n, rfl⟩ := hP; exact reMap_imMap_fourier_mem n
  | zero => simp only [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
  | add P Q _ _ ihP ihQ =>
      rw [map_add, map_add]
      exact ⟨add_mem ihP.1 ihQ.1, add_mem ihP.2 ihQ.2⟩
  | smul c P _ ih =>
      have hre : reMap (AddCircle T) (c • P)
          = c.re • reMap (AddCircle T) P - c.im • imMap (AddCircle T) P := by
        ext x; simp [Complex.mul_re]
      have him : imMap (AddCircle T) (c • P)
          = c.re • imMap (AddCircle T) P + c.im • reMap (AddCircle T) P := by
        ext x; simp [Complex.mul_im]
      rw [hre, him]
      exact ⟨sub_mem (smul_mem _ _ ih.1) (smul_mem _ _ ih.2),
        add_mem (smul_mem _ _ ih.2) (smul_mem _ _ ih.1)⟩

/-- **Corollary 3.1.4.** The trigonometric polynomials are dense in `C_p(2π)`, the continuous
`2π`-periodic functions with the uniform norm: every such `f` is uniformly within `ε` of a real
linear combination of `1`, `cos (j x)` and `sin (j x)`.

Stated on `C(AddCircle T, ℝ)` for any period `T > 0`; the book's `C_p(2π)` is `T = 2π`. The system
`trigFun T` is the one of Theorem 1.3.13, so its real span is exactly the trigonometric
polynomials. -/
theorem corollary_3_1_4 [Fact (0 < T)] (f : C(AddCircle T, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ span ℝ (Set.range (trigFun T)), ‖p - f‖ < ε := by
  -- the complexification of `f`
  set F : C(AddCircle T, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    with hF
  have hFtop : F ∈ (span ℂ (Set.range (fourier (T := T)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hFtop
  obtain ⟨P, hPmem, hPdist⟩ := hFtop ε hε
  refine ⟨reMap (AddCircle T) P, (reMap_imMap_mem_of_mem_span hPmem).1, ?_⟩
  have hle : ‖reMap (AddCircle T) P - f‖ ≤ ‖P - F‖ := by
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    have h1 : (reMap (AddCircle T) P - f) x = (P x - F x).re := by
      simp [hF, Complex.sub_re]
    rw [h1, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (ContinuousMap.norm_coe_le_norm (P - F) x)
  rw [dist_eq_norm, norm_sub_rev] at hPdist
  exact lt_of_le_of_lt hle hPdist

end Trigonometric

end AtkinsonHan.Chapter03
