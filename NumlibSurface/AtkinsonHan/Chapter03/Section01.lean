import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.InnerProductSpace.GramDeterminant
import Numlib.Approximation.BestApprox
import Numlib.LinearAlgebra.Matrix.Cauchy

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
norm on it does not matter, only the topology. Corollary 3.1.4 is
`span_fourier_closure_eq_top` — the density of the *complex* exponentials in `C(AddCircle T, ℂ)` —
carried to the real system `trigFun` of `Numlib/Analysis/Fourier/TrigonometricBasis` by taking real
parts: the real and imaginary parts of a complex trigonometric polynomial are real trigonometric
polynomials, and taking real parts does not increase the uniform norm. It is what makes the
trigonometric system complete in Theorem 1.3.13 and what Theorem 4.1.2 needs.

`C_p(2π)`, the continuous `2π`-periodic functions with the uniform norm, is `C(AddCircle (2π), ℝ)`,
as everywhere in this surface.

## Müntz's theorem

Theorem 3.1.5 is proved here from scratch: Mathlib has neither the Müntz–Szász theorem nor a Hardy
space theory. The route is the classical one through Gram determinants, and it is built out of two
backbone results.

`powerL2 l` is `t ↦ t ^ l` as an element of `L²(0, 1)`, and `inner_powerL2` computes
`⟪tᵃ, t^b⟫ = 1/(a + b + 1)`, so the Gram matrix of a finite system of powers is the Cauchy matrix of
`Numlib/LinearAlgebra/Matrix/Cauchy`, whose determinant is `Matrix.det_cauchy`. Gram's formula for
the distance to a span, `Submodule.norm_sub_starProjection_sq_eq_det_gram_div_real` of
`Numlib/Analysis/InnerProductSpace/GramDeterminant`, then turns the quotient of two such
determinants into the squared best-approximation error, and the quotient telescopes
(`dist_sq_powerL2`) to

`dₙ(a)² = (2a + 1)⁻¹ ∏_{i < n} ((a - λᵢ) / (a + λᵢ + 1))²`.

The rest is real analysis of that product. Since `1 - (λᵢ - a)/(λᵢ + a + 1) = (2a+1)/(λᵢ + a + 1)`
is comparable to `1/λᵢ`, the product tends to `0` exactly when `∑ 1/λᵢ` diverges: `1 - x ≤ exp (-x)`
for the vanishing, the Weierstrass product inequality `1 - ∑ bᵢ ≤ ∏ (1 - bᵢ)` for the lower bound.
For the *if* direction the vanishing is applied at every natural number `a = m` and closed against
`dense_span_monomials`, the density of the polynomials in `L²(0, 1)`, which is Theorem 3.1.1
together with the density of the bounded continuous functions in `L²`. For the *only if* direction
the lower bound is applied at one `a` outside the sequence, namely a point between `λ₁` and `λ₂`.
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

section Muntz

/-! ### Theorem 3.1.5: the Müntz–Szász theorem

`L²(0, 1)` is `Lp ℝ 2 μ₁` for the Lebesgue measure `μ₁` restricted to the open unit interval.
-/

/-- The measure of `L²(0, 1)`: Lebesgue measure restricted to the open unit interval. -/
local notation "μ₁" => MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- The power function `t ↦ t ^ l` is measurable on `(0, 1)`. -/
private theorem aestronglyMeasurable_rpow (l : ℝ) :
    AEStronglyMeasurable (fun t : ℝ ↦ t ^ l) μ₁ :=
  (ContinuousOn.rpow_const continuousOn_id fun _ hx ↦
    Or.inl (ne_of_gt hx.1)).aestronglyMeasurable measurableSet_Ioo

/-- `∫₀¹ tᵃ t^b dt = 1 / (a + b + 1)` whenever `a + b > -1`. -/
private theorem integral_rpow_mul_rpow {a b : ℝ} (h : -1 < a + b) :
    ∫ t in Ioo (0:ℝ) 1, t ^ a * t ^ b = 1 / (a + b + 1) := by
  have hc : ∀ t ∈ Ioo (0:ℝ) 1, t ^ a * t ^ b = t ^ (a + b) :=
    fun t ht ↦ (Real.rpow_add ht.1 a b).symm
  rw [setIntegral_congr_fun measurableSet_Ioo hc, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl h), Real.one_rpow,
    Real.zero_rpow (by linarith), sub_zero]

/-- The power function `t ↦ t ^ l` is square integrable on `(0, 1)` when `l > -1/2`. -/
theorem memLp_rpow {l : ℝ} (hl : -(1 / 2 : ℝ) < l) : MemLp (fun t : ℝ ↦ t ^ l) 2 μ₁ := by
  rw [memLp_two_iff_integrable_sq (aestronglyMeasurable_rpow l)]
  have hc : ∀ t ∈ Ioo (0:ℝ) 1, (t ^ l) ^ 2 = t ^ (2 * l) := by
    intro t ht
    rw [← Real.rpow_natCast (t ^ l) 2, ← Real.rpow_mul ht.1.le]
    norm_num
    ring_nf
  rw [← IntegrableOn, integrableOn_congr_fun hc measurableSet_Ioo]
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)

/-- The power function `t ↦ t ^ l` as an element of `L²(0, 1)`. For `l ≤ -1/2` it is not square
integrable and the definition returns `0`; every use below has `l > 0`. -/
noncomputable def powerL2 (l : ℝ) : Lp ℝ 2 μ₁ :=
  if h : -(1 / 2 : ℝ) < l then (memLp_rpow h).toLp _ else 0

/-- `powerL2 l` is represented by `t ↦ t ^ l`. -/
theorem coeFn_powerL2 {l : ℝ} (hl : -(1 / 2 : ℝ) < l) : powerL2 l =ᵐ[μ₁] fun t ↦ t ^ l := by
  have h : powerL2 l = (memLp_rpow hl).toLp _ := dite_eq_iff.2 (Or.inl ⟨hl, rfl⟩)
  rw [h]
  exact MemLp.coeFn_toLp _

/-- The inner product of two powers in `L²(0, 1)`: `⟪tᵃ, t^b⟫ = 1 / (a + b + 1)`. -/
theorem inner_powerL2 {a b : ℝ} (ha : -(1 / 2 : ℝ) < a) (hb : -(1 / 2 : ℝ) < b) :
    inner ℝ (powerL2 a) (powerL2 b) = 1 / (a + b + 1) := by
  rw [L2.inner_def, ← integral_rpow_mul_rpow (a := a) (b := b) (by linarith)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_powerL2 ha, coeFn_powerL2 hb] with t h1 h2
  rw [h1, h2, RCLike.inner_apply]
  simp [mul_comm]

/-- The Gram matrix of the powers `t ^ mᵢ` in `L²(0, 1)` is the Cauchy matrix of `mᵢ + 1/2` with
itself. -/
private theorem gram_powerL2 {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, -(1 / 2 : ℝ) < m i) :
    Matrix.gram ℝ (fun i ↦ powerL2 (m i))
      = Matrix.cauchy (fun i ↦ m i + 1 / 2) (fun i ↦ m i + 1 / 2) := by
  ext i j
  rw [Matrix.gram_apply, inner_powerL2 (hm i) (hm j), Matrix.cauchy_apply, one_div]
  congr 1
  ring

/-- The Cauchy determinant, read on the Gram matrix of the powers. -/
private theorem det_gram_powerL2 {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, -(1 / 2 : ℝ) < m i) :
    (Matrix.gram ℝ fun i ↦ powerL2 (m i)).det
      = (∏ i, ∏ j ∈ Finset.Ioi i, ((m j - m i) * (m j - m i)))
        / ∏ i, ∏ j, (m i + m j + 1) := by
  rw [gram_powerL2 m hm,
    Matrix.det_cauchy _ _ fun i j ↦ ne_of_gt (by have := hm i; have := hm j; linarith)]
  congr 1
  · exact Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl fun j _ ↦ by ring
  · exact Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl fun j _ ↦ by ring

/-- Distinct powers are linearly independent in `L²(0, 1)`, because their Gram matrix is a Cauchy
matrix with distinct nodes. -/
theorem linearIndependent_powerL2 {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, -(1 / 2 : ℝ) < m i)
    (hinj : Function.Injective m) : LinearIndependent ℝ (fun i ↦ powerL2 (m i)) := by
  refine Matrix.det_gram_ne_zero_iff_linearIndependent.1 ?_
  rw [gram_powerL2 m hm]
  exact Matrix.det_cauchy_ne_zero (fun i j ↦ ne_of_gt (by have := hm i; have := hm j; linarith))
    (fun i j h ↦ hinj (by simpa using h)) (fun i j h ↦ hinj (by simpa using h))

/-- Splitting a product over the strictly upper triangle of `Fin (n + 1)` along `Fin.cons`. -/
private theorem prod_Ioi_cons {M : Type*} [CommMonoid M] {n : ℕ} (g : ℝ → ℝ → M) (a : ℝ)
    (l : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
        g ((Fin.cons a l : Fin (n + 1) → ℝ) i) ((Fin.cons a l : Fin (n + 1) → ℝ) j))
      = (∏ j, g a (l j)) * ∏ i, ∏ j ∈ Finset.Ioi i, g (l i) (l j) := by
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_Ioi_zero]; simp
  · exact Finset.prod_congr rfl fun i _ ↦ by rw [Fin.prod_Ioi_succ]; simp

/-- Splitting a double product over `Fin (n + 1)` along `Fin.cons`. -/
private theorem prod_prod_cons {M : Type*} [CommMonoid M] {n : ℕ} (g : ℝ → ℝ → M) (a : ℝ)
    (l : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
        g ((Fin.cons a l : Fin (n + 1) → ℝ) i) ((Fin.cons a l : Fin (n + 1) → ℝ) j))
      = (g a a * ∏ j, g a (l j)) * ∏ i, (g (l i) a * ∏ j, g (l i) (l j)) := by
  simp [Fin.prod_univ_succ]

/-- The cancellation that turns the quotient of the two Cauchy determinants into the Müntz
product. -/
private theorem ratio_algebra {A N P Q D a : ℝ} (hN : N ≠ 0) (hD : D ≠ 0) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (ha : 2 * a + 1 ≠ 0) :
    ((A * N) / (((a + a + 1) * P) * (Q * D))) / (N / D) = (2 * a + 1)⁻¹ * (A / (P * Q)) := by
  rw [show a + a + 1 = 2 * a + 1 by ring]
  field_simp

/-- The squared distance in `L²(0, 1)` from `t ^ a` to the span of the powers `t ^ lᵢ`:

`d² = (2a + 1)⁻¹ ∏ᵢ ((a - lᵢ) / (a + lᵢ + 1))²`.

This is Gram's determinant formula, `Submodule.norm_sub_starProjection_sq_eq_det_gram_div_real`,
evaluated on the Cauchy determinant `Matrix.det_cauchy`. -/
theorem dist_sq_powerL2 {n : ℕ} (l : Fin n → ℝ) (a : ℝ) (hl : ∀ i, -(1 / 2 : ℝ) < l i)
    (ha : -(1 / 2 : ℝ) < a) (hinj : Function.Injective l) :
    ‖powerL2 a
        - (Submodule.span ℝ (Set.range fun i ↦ powerL2 (l i))).starProjection (powerL2 a)‖ ^ 2
      = (2 * a + 1)⁻¹ * ∏ i, ((a - l i) / (a + l i + 1)) ^ 2 := by
  have hm : ∀ i, -(1 / 2 : ℝ) < (Fin.cons a l : Fin (n + 1) → ℝ) i := by
    intro i
    induction i using Fin.cases with
    | zero => simpa using ha
    | succ i => simpa using hl i
  have hcons : (Fin.cons (powerL2 a) fun i ↦ powerL2 (l i))
      = fun i ↦ powerL2 ((Fin.cons a l : Fin (n + 1) → ℝ) i) := by
    funext i; induction i using Fin.cases <;> simp
  have hN0 : (∏ i, ∏ j ∈ Finset.Ioi i, ((l j - l i) * (l j - l i))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ ↦ Finset.prod_ne_zero_iff.2 fun j hj ↦ ?_
    have h : l j ≠ l i := fun h ↦ absurd (hinj h) (Finset.mem_Ioi.1 hj).ne'
    exact mul_ne_zero (sub_ne_zero.2 h) (sub_ne_zero.2 h)
  have hD0 : (∏ i, ∏ j : Fin n, (l i + l j + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ Finset.prod_ne_zero_iff.2 fun j _ ↦
      ne_of_gt (by have := hl i; have := hl j; linarith)
  have hS : ∀ i, (a + l i + 1) ≠ 0 := fun i ↦ ne_of_gt (by have := hl i; linarith)
  have ha2 : (2 * a + 1) ≠ 0 := ne_of_gt (by linarith)
  rw [Submodule.norm_sub_starProjection_sq_eq_det_gram_div_real
    (linearIndependent_powerL2 l hl hinj), Matrix.det_gram_sumElim_eq_det_gram_cons, hcons,
    det_gram_powerL2 _ hm, det_gram_powerL2 l hl,
    prod_Ioi_cons (fun x y ↦ (y - x) * (y - x)) a l,
    prod_prod_cons (fun x y ↦ x + y + 1) a l]
  have hsplit : (∏ i, ((l i + a + 1) * ∏ j : Fin n, (l i + l j + 1)))
      = (∏ i, (l i + a + 1)) * ∏ i, ∏ j : Fin n, (l i + l j + 1) := Finset.prod_mul_distrib
  rw [hsplit]
  have hR : (∏ i, ((a - l i) / (a + l i + 1)) ^ 2)
      = (∏ i, ((l i - a) * (l i - a))) / ((∏ j, (a + l j + 1)) * ∏ i, (l i + a + 1)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [div_pow]; congr 1 <;> ring
  rw [hR]
  have hP : (∏ j : Fin n, (a + l j + 1)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hS i
  have hQ : (∏ i : Fin n, (l i + a + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ ne_of_gt (by have := hl i; linarith)
  exact ratio_algebra hN0 hD0 hP hQ ha2

/-! #### The Müntz products -/

/-- The Weierstrass product inequality, `1 - ∑ bᵢ ≤ ∏ (1 - bᵢ)` for `bᵢ ∈ [0, 1]`. -/
private theorem one_sub_sum_le_prod_one_sub (b : ℕ → ℝ) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1)
    (n : ℕ) : 1 - ∑ i ∈ Finset.range n, b i ≤ ∏ i ∈ Finset.range n, (1 - b i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range n, b i := Finset.sum_nonneg fun i _ ↦ hb0 i
    nlinarith [ih, hb0 n, hb1 n]

/-- If `∑ bᵢ` diverges and `bᵢ ≤ 1` then `∏ (1 - bᵢ) → 0`, by `1 - x ≤ exp (-x)`. -/
private theorem tendsto_prod_one_sub {b : ℕ → ℝ} (hb1 : ∀ i, b i ≤ 1)
    (hdiv : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, b i) atTop atTop) :
    Tendsto (fun n ↦ ∏ i ∈ Finset.range n, (1 - b i)) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ Finset.prod_nonneg fun i _ ↦ by linarith [hb1 i])
    (g := fun n ↦ Real.exp (-∑ i ∈ Finset.range n, b i)) (fun n ↦ ?_) ?_
  · calc ∏ i ∈ Finset.range n, (1 - b i) ≤ ∏ i ∈ Finset.range n, Real.exp (-b i) :=
          Finset.prod_le_prod (fun i _ ↦ by linarith [hb1 i])
            (fun i _ ↦ by linarith [Real.add_one_le_exp (-b i)])
      _ = Real.exp (-∑ i ∈ Finset.range n, b i) := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib]
  · exact Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.2 hdiv)

section Products

variable {a : ℝ} {l : ℕ → ℝ} {i : ℕ}

/-- The `i`-th factor of the Müntz product, `((a - lᵢ) / (a + lᵢ + 1)) ^ 2`, is at most `1`. -/
private theorem muntzFactor_le_one (ha : 0 ≤ a) (hl : 0 < l i) :
    ((a - l i) / (a + l i + 1)) ^ 2 ≤ 1 := by
  rw [div_pow, div_le_one (by positivity)]
  nlinarith [abs_nonneg (a - l i)]

/-- Where `lᵢ` exceeds `a`, the `i`-th factor is `(1 - bᵢ) ^ 2` with `bᵢ = (2a+1)/(lᵢ + a + 1)`,
the quantity that is comparable to `1 / lᵢ`. -/
private theorem muntzFactor_eq (ha : 0 ≤ a) (hl : 0 < l i) :
    ((a - l i) / (a + l i + 1)) ^ 2 = (1 - (2 * a + 1) / (l i + a + 1)) ^ 2 := by
  have h : l i + a + 1 ≠ 0 := by positivity
  rw [show (1 : ℝ) - (2 * a + 1) / (l i + a + 1) = (l i - a) / (l i + a + 1) by field_simp; ring,
    div_pow, div_pow]
  congr 1 <;> ring

/-- If `∑ 1 / lⱼ` diverges then the Müntz products tend to `0`. -/
private theorem tendsto_muntzProd (ha : 0 ≤ a) (hl : ∀ j, 0 < l j)
    (htop : Tendsto l atTop atTop) (hns : ¬ Summable fun j ↦ (l j)⁻¹) :
    Tendsto (fun n ↦ ∏ i ∈ Finset.range n, ((a - l i) / (a + l i + 1)) ^ 2) atTop (𝓝 0) := by
  obtain ⟨I, hI⟩ := (tendsto_atTop.1 htop (a + 1)).exists_forall_of_atTop
  set b : ℕ → ℝ := fun k ↦ (2 * a + 1) / (l (k + I) + a + 1) with hbdef
  have hlI : ∀ k, a + 1 ≤ l (k + I) := fun k ↦ hI (k + I) (Nat.le_add_left _ _)
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ by
    have := hl (k + I); positivity
  have hb1 : ∀ k, b k ≤ 1 := fun k ↦ by
    rw [hbdef, div_le_one (by have := hl (k + I); positivity)]
    linarith [hlI k]
  have hdiv : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, b k) atTop atTop := by
    refine (not_summable_iff_tendsto_nat_atTop_of_nonneg hb0).1 fun hsum ↦ hns ?_
    refine (summable_nat_add_iff I).1 (Summable.of_nonneg_of_le (fun k ↦ by
      have := hl (k + I); positivity) (fun k ↦ ?_) (hsum.mul_left (2 / (2 * a + 1))))
    have h1 : (0:ℝ) < l (k + I) := hl (k + I)
    have h4 : (0:ℝ) < l (k + I) + a + 1 := by linarith
    have key : (2 / (2 * a + 1)) * b k = 2 / (l (k + I) + a + 1) := by
      rw [hbdef]; field_simp
    rw [key, inv_eq_one_div, ← sub_nonneg,
      show 2 / (l (k + I) + a + 1) - 1 / l (k + I)
        = (l (k + I) - a - 1) / (l (k + I) * (l (k + I) + a + 1)) by field_simp; ring]
    exact div_nonneg (by linarith [hlI k]) (by positivity)
  have hprod : Tendsto (fun n ↦ ∏ k ∈ Finset.range n, (1 - b k)) atTop (𝓝 0) :=
    tendsto_prod_one_sub hb1 hdiv
  have hshift : ∀ n, (∏ i ∈ Finset.range (n + I), ((a - l i) / (a + l i + 1)) ^ 2)
      = (∏ i ∈ Finset.range I, ((a - l i) / (a + l i + 1)) ^ 2)
        * (∏ k ∈ Finset.range n, (1 - b k)) ^ 2 := by
    intro n
    rw [add_comm n I, Finset.prod_range_add, ← Finset.prod_pow]
    refine congrArg _ (Finset.prod_congr rfl fun k _ ↦ ?_)
    rw [show I + k = k + I from Nat.add_comm I k]
    exact muntzFactor_eq ha (hl (k + I))
  rw [← tendsto_add_atTop_iff_nat I]
  refine Filter.Tendsto.congr (fun n ↦ (hshift n).symm) ?_
  simpa using (hprod.pow 2).const_mul
    (∏ i ∈ Finset.range I, ((a - l i) / (a + l i + 1)) ^ 2)

/-- The Müntz products decrease. -/
private theorem muntzProd_antitone (ha : 0 ≤ a) (hl : ∀ j, 0 < l j) :
    Antitone fun n ↦ ∏ i ∈ Finset.range n, ((a - l i) / (a + l i + 1)) ^ 2 := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [Finset.prod_range_succ]
  nlinarith [Finset.prod_nonneg (fun i (_ : i ∈ Finset.range n) ↦
      sq_nonneg ((a - l i) / (a + l i + 1))),
    muntzFactor_le_one (i := n) ha (hl n), sq_nonneg ((a - l n) / (a + l n + 1))]

/-- If `∑ 1 / lⱼ` converges and `a` avoids the `lⱼ`, the Müntz products stay away from `0`. -/
private theorem muntzProd_bddBelow (ha : 0 ≤ a) (hl : ∀ j, 0 < l j)
    (htop : Tendsto l atTop atTop) (hne : ∀ j, l j ≠ a) (hsum : Summable fun j ↦ (l j)⁻¹) :
    ∃ ε > 0, ∀ n, ε ≤ ∏ i ∈ Finset.range n, ((a - l i) / (a + l i + 1)) ^ 2 := by
  set b : ℕ → ℝ := fun j ↦ (2 * a + 1) / (l j + a + 1) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j ↦ by have := hl j; positivity
  have hbsum : Summable b := by
    refine Summable.of_nonneg_of_le hb0 (fun j ↦ ?_) (hsum.mul_left (2 * a + 1))
    have h1 : (0:ℝ) < l j := hl j
    rw [hbdef, inv_eq_one_div, mul_one_div]
    exact div_le_div_of_nonneg_left (by linarith) h1 (by linarith)
  obtain ⟨I, hI⟩ := (tendsto_atTop.1 htop (a + 1)).exists_forall_of_atTop
  obtain ⟨J, hJI, hJ⟩ : ∃ J, I ≤ J ∧ ∑' k, b (k + J) ≤ 1 / 2 := by
    have h := (tendsto_sum_nat_add b).eventually
      (eventually_le_nhds (show (0:ℝ) < 1 / 2 by norm_num))
    obtain ⟨J, hJ⟩ := (h.and (eventually_ge_atTop I)).exists
    exact ⟨J, hJ.2, hJ.1⟩
  have hQJpos : 0 < ∏ i ∈ Finset.range J, ((a - l i) / (a + l i + 1)) ^ 2 := by
    refine Finset.prod_pos fun i _ ↦ ?_
    have h1 : (a - l i) / (a + l i + 1) ≠ 0 :=
      div_ne_zero (sub_ne_zero.2 fun h ↦ hne i h.symm) (by have := hl i; positivity)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1))
  refine ⟨(∏ i ∈ Finset.range J, ((a - l i) / (a + l i + 1)) ^ 2) / 4, by linarith, fun n ↦ ?_⟩
  rcases le_total n J with hn | hn
  · linarith [muntzProd_antitone ha hl hn]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hkey : (∏ i ∈ Finset.range (J + m), ((a - l i) / (a + l i + 1)) ^ 2)
        = (∏ i ∈ Finset.range J, ((a - l i) / (a + l i + 1)) ^ 2)
          * (∏ k ∈ Finset.range m, (1 - b (k + J))) ^ 2 := by
      rw [Finset.prod_range_add, ← Finset.prod_pow]
      refine congrArg _ (Finset.prod_congr rfl fun k _ ↦ ?_)
      rw [show J + k = k + J from Nat.add_comm J k]
      exact muntzFactor_eq ha (hl (k + J))
    have hlow : (1:ℝ) / 2 ≤ ∏ k ∈ Finset.range m, (1 - b (k + J)) := by
      have h1 : ∑ k ∈ Finset.range m, b (k + J) ≤ 1 / 2 :=
        le_trans (((summable_nat_add_iff J).2 hbsum).sum_le_tsum (Finset.range m)
          (fun k _ ↦ hb0 _)) hJ
      have h2 := one_sub_sum_le_prod_one_sub (fun k ↦ b (k + J)) (fun k ↦ hb0 _)
        (fun k ↦ by
          rw [hbdef, div_le_one (by have := hl (k + J); positivity)]
          linarith [hI (k + J) (le_trans hJI (Nat.le_add_left _ _))]) m
      linarith
    rw [hkey]
    have hB : (1:ℝ) / 4 ≤ (∏ k ∈ Finset.range m, (1 - b (k + J))) ^ 2 := by nlinarith [hlow]
    nlinarith [hQJpos, hB]

end Products

/-! #### The polynomials are dense in `L²(0, 1)` -/

/-- The representative of a finite combination of monomials. -/
private theorem coeFn_polySum (s : Finset ℕ) (c : ℕ → ℝ) :
    ⇑(∑ m ∈ s, c m • powerL2 (m : ℝ)) =ᵐ[μ₁] fun t ↦ ∑ m ∈ s, c m * t ^ (m : ℝ) := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℝ 2 μ₁
  | insert m s hm ih =>
      rw [Finset.sum_insert hm]
      filter_upwards [Lp.coeFn_add (c m • powerL2 (m : ℝ)) (∑ k ∈ s, c k • powerL2 (k : ℝ)),
        Lp.coeFn_smul (c m) (powerL2 (m : ℝ)),
        coeFn_powerL2 (l := (m : ℝ)) (by have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith),
        ih] with t h1 h2 h3 h4
      rw [h1, Finset.sum_insert hm]
      simp only [Pi.add_apply, h2, h4, Pi.smul_apply, h3, smul_eq_mul]

/-- A polynomial as an element of `L²(0, 1)`, presented as a combination of the monomials. -/
private noncomputable def polyL2 (p : ℝ[X]) : Lp ℝ 2 μ₁ :=
  ∑ m ∈ Finset.range (p.natDegree + 1), p.coeff m • powerL2 (m : ℝ)

/-- `polyL2 p` lies in the span of the monomials. -/
private theorem polyL2_mem (p : ℝ[X]) :
    polyL2 p ∈ Submodule.span ℝ (Set.range fun m : ℕ ↦ powerL2 (m : ℝ)) :=
  Submodule.sum_mem _ fun m _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-- `polyL2 p` is represented by `t ↦ p t`. -/
private theorem coeFn_polyL2 (p : ℝ[X]) : ⇑(polyL2 p) =ᵐ[μ₁] fun t ↦ p.eval t := by
  filter_upwards [coeFn_polySum (Finset.range (p.natDegree + 1)) p.coeff,
    ae_restrict_mem measurableSet_Ioo] with t h ht
  simp only [polyL2]
  rw [h, Polynomial.eval_eq_sum_range]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [Real.rpow_natCast]

/-- The unit interval has measure one. -/
private theorem measureUnivNNReal_unit : measureUnivNNReal μ₁ = 1 := by
  simp [measureUnivNNReal]

/-- The monomials span a dense subspace of `L²(0, 1)`: bounded continuous functions are dense in
`L²`, and Theorem 3.1.1 approximates them uniformly on `[0, 1]` by polynomials. -/
theorem dense_span_monomials :
    Dense ((Submodule.span ℝ (Set.range fun m : ℕ ↦ powerL2 (m : ℝ)) :
      Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) := by
  have : (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1)).WeaklyRegular :=
    MeasureTheory.Measure.WeaklyRegular.restrict_of_measure_ne_top
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have : IsFiniteMeasure μ₁ := ⟨by simp⟩
  intro f
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨g, hg, gmem⟩ := (Lp.memLp f).exists_boundedContinuous_eLpNorm_sub_le
    (p := 2) (by norm_num) (ε := ENNReal.ofReal (ε / 3)) (by simp; linarith)
  have hae : ⇑(f - gmem.toLp ⇑g) =ᵐ[μ₁] ⇑f - ⇑g := by
    filter_upwards [Lp.coeFn_sub f (gmem.toLp ⇑g), gmem.coeFn_toLp] with t h1 h2
    rw [h1, Pi.sub_apply, Pi.sub_apply, h2]
  have hfg : ‖f - gmem.toLp ⇑g‖ ≤ ε / 3 := by
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    calc (eLpNorm (⇑f - ⇑g) 2 μ₁).toReal ≤ (ENNReal.ofReal (ε / 3)).toReal :=
          ENNReal.toReal_mono (by simp) hg
      _ = ε / 3 := ENNReal.toReal_ofReal (by linarith)
  set G : C(Set.Icc (0:ℝ) 1, ℝ) := ⟨fun x ↦ g x, g.continuous.comp continuous_subtype_val⟩ with hG
  obtain ⟨q, hq⟩ := theorem_3_1_1 0 1 G (show (0:ℝ) < ε / 3 by linarith)
  have hgq : ‖gmem.toLp ⇑g - polyL2 q‖ ≤ ε / 3 := by
    have hb : ∀ᵐ t ∂μ₁, ‖(gmem.toLp ⇑g - polyL2 q) t‖ ≤ ε / 3 := by
      filter_upwards [Lp.coeFn_sub (gmem.toLp ⇑g) (polyL2 q), gmem.coeFn_toLp, coeFn_polyL2 q,
        ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3 ht
      have hmem : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
      have hbd := (ContinuousMap.norm_coe_le_norm (q.toContinuousMapOn (Set.Icc (0:ℝ) 1) - G)
        ⟨t, hmem⟩).trans hq.le
      rw [h1, Pi.sub_apply, h2, h3]
      simpa [hG, Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
        abs_sub_comm] using hbd
    simpa [measureUnivNNReal_unit] using
      Lp.norm_le_of_ae_bound (p := 2) (μ := μ₁) (by linarith : (0:ℝ) ≤ ε / 3) hb
  refine ⟨polyL2 q, polyL2_mem q, ?_⟩
  calc dist f (polyL2 q) ≤ ‖f - gmem.toLp ⇑g‖ + ‖gmem.toLp ⇑g - polyL2 q‖ := by
        rw [dist_eq_norm]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

/-! #### The theorem -/

section Main

variable {lam : ℕ → ℝ}

/-- The spans of the initial segments increase. -/
private theorem muntzFin_le {n n' : ℕ} (hn : n ≤ n') :
    Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))
      ≤ Submodule.span ℝ (Set.range fun i : Fin n' ↦ powerL2 (lam i)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.2 hn⟩, rfl⟩

/-- Each initial segment spans inside the full span. -/
private theorem muntzFin_le_span (n : ℕ) :
    Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))
      ≤ Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨i, rfl⟩

/-- Every element of the full span already lies in the span of an initial segment. -/
private theorem exists_mem_muntzFin {x : Lp ℝ 2 μ₁}
    (hx : x ∈ Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j))) :
    ∃ n, x ∈ Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i)) := by
  have hsub : Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j))
      ≤ ⨆ n, Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (j + 1)
      (Submodule.subset_span ⟨⟨j, Nat.lt_succ_self j⟩, rfl⟩)
  have hdir : Directed (· ≤ ·)
      fun n ↦ Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i)) :=
    fun n n' ↦ ⟨max n n', muntzFin_le (le_max_left n n'), muntzFin_le (le_max_right n n')⟩
  exact (Submodule.mem_iSup_of_directed _ hdir).1 (hsub hx)

/-- The distance from `t ^ a` to the span of the first `n` powers, as a Müntz product. -/
private theorem norm_sub_starProjection_muntz (hlam : ∀ j, 0 < lam j) (hmono : StrictMono lam)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection
        (powerL2 a)‖ ^ 2
      = (2 * a + 1)⁻¹ * ∏ i ∈ Finset.range n, ((a - lam i) / (a + lam i + 1)) ^ 2 := by
  rw [dist_sq_powerL2 (fun i : Fin n ↦ lam i) a (fun i ↦ by linarith [hlam i]) (by linarith)
    (fun i j h ↦ Fin.val_injective (hmono.injective h))]
  exact congrArg _ (Fin.prod_univ_eq_prod_range (fun i ↦ ((a - lam i) / (a + lam i + 1)) ^ 2) n)

/-- If `∑ 1 / λⱼ` diverges, every power `t ^ a` with `a ≥ 0` lies in the closure of the span. -/
private theorem mem_closure_muntzSpan (hlam : ∀ j, 0 < lam j) (hmono : StrictMono lam)
    (htop : Tendsto lam atTop atTop) (hns : ¬ Summable fun j ↦ (lam j)⁻¹) {a : ℝ} (ha : 0 ≤ a) :
    powerL2 a ∈ closure ((Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j)) :
      Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) := by
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  have hsq : Tendsto (fun n ↦ ‖powerL2 a - (Submodule.span ℝ
      (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection (powerL2 a)‖ ^ 2)
      atTop (𝓝 0) := by
    simp_rw [norm_sub_starProjection_muntz hlam hmono ha]
    simpa using (tendsto_muntzProd ha hlam htop hns).const_mul (2 * a + 1)⁻¹
  obtain ⟨n, hn⟩ := (hsq.eventually (gt_mem_nhds (show (0:ℝ) < ε ^ 2 by positivity))).exists
  refine ⟨(Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection
    (powerL2 a), muntzFin_le_span n (Submodule.starProjection_apply_mem _ _), ?_⟩
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hn

/-- If `∑ 1 / λⱼ` converges, the span is not dense: it misses `t ^ a` for `a` strictly between
`λ₀` and `λ₁`. -/
private theorem not_dense_muntzSpan (hlam : ∀ j, 0 < lam j) (hmono : StrictMono lam)
    (htop : Tendsto lam atTop atTop) (hs : Summable fun j ↦ (lam j)⁻¹) :
    ¬ Dense ((Submodule.span ℝ (Set.range fun j : ℕ ↦ powerL2 (lam j)) :
      Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) := by
  have h01 : lam 0 < lam 1 := hmono (by norm_num)
  set a := (lam 0 + lam 1) / 2 with hadef
  have ha0 : 0 < a := by have := hlam 0; simp only [hadef]; linarith
  have hane : ∀ j, lam j ≠ a := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [hadef]; intro h; linarith
    · have h1 : lam 1 ≤ lam j := hmono.monotone hj
      simp only [hadef]; intro h; linarith
  obtain ⟨ε, hε, hbd⟩ := muntzProd_bddBelow ha0.le hlam htop hane hs
  intro hdense
  obtain ⟨y, hy, hlt⟩ := Metric.mem_closure_iff.1 (hdense (powerL2 a))
    (Real.sqrt ((2 * a + 1)⁻¹ * ε)) (Real.sqrt_pos.2 (by positivity))
  obtain ⟨n, hn⟩ := exists_mem_muntzFin hy
  have hmin := (isBestApprox_starProjection
    (Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))) (powerL2 a)).2 y hn
  have hge : (2 * a + 1)⁻¹ * ε
      ≤ ‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection
        (powerL2 a)‖ ^ 2 := by
    rw [norm_sub_starProjection_muntz hlam hmono ha0.le]
    exact mul_le_mul_of_nonneg_left (hbd n) (by positivity)
  have hsqrt : Real.sqrt ((2 * a + 1)⁻¹ * ε)
      ≤ ‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦ powerL2 (lam i))).starProjection
        (powerL2 a)‖ := by
    rw [show ‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦
        powerL2 (lam i))).starProjection (powerL2 a)‖
        = Real.sqrt (‖powerL2 a - (Submodule.span ℝ (Set.range fun i : Fin n ↦
          powerL2 (lam i))).starProjection (powerL2 a)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hge
  rw [dist_eq_norm] at hlt
  linarith

/-- **Theorem 3.1.5** (Müntz). Let `0 < λ₁ < λ₂ < ⋯` with `λⱼ → ∞`. The span of the powers
`t ↦ t ^ λⱼ` is dense in `L²(0, 1)` if and only if `∑ 1 / λⱼ = ∞`.

The sequence is indexed from `0` here, so the book's `λ₁` is `lam 0`, and the divergence of
`∑ 1 / λⱼ` is stated as the failure of `Summable`, the terms being positive. -/
theorem theorem_3_1_5 (lam : ℕ → ℝ) (hpos : 0 < lam 0) (hmono : StrictMono lam)
    (htop : Tendsto lam atTop atTop) :
    Dense ((Submodule.span ℝ (Set.range fun j ↦ powerL2 (lam j)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁))
      ↔ ¬ Summable fun j ↦ (lam j)⁻¹ := by
  have hlam : ∀ j, 0 < lam j := fun j ↦ lt_of_lt_of_le hpos (hmono.monotone (Nat.zero_le j))
  refine ⟨fun hdense hs ↦ not_dense_muntzSpan hlam hmono htop hs hdense, fun hns ↦ ?_⟩
  have hmem : ∀ m : ℕ, powerL2 (m : ℝ) ∈
      closure ((Submodule.span ℝ (Set.range fun j ↦ powerL2 (lam j)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) :=
    fun m ↦ mem_closure_muntzSpan hlam hmono htop hns (Nat.cast_nonneg m)
  have hsub : ((Submodule.span ℝ (Set.range fun m : ℕ ↦ powerL2 (m : ℝ)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁))
      ⊆ closure ((Submodule.span ℝ (Set.range fun j ↦ powerL2 (lam j)) :
        Submodule ℝ (Lp ℝ 2 μ₁)) : Set (Lp ℝ 2 μ₁)) := by
    rw [← Submodule.topologicalClosure_coe, SetLike.coe_subset_coe, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.topologicalClosure_coe] at *
    exact hmem m
  refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
  rw [← dense_span_monomials.closure_eq]
  exact closure_minimal hsub isClosed_closure

end Main

end Muntz

end AtkinsonHan.Chapter03
