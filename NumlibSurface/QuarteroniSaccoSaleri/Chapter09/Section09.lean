import Numlib.Approximation.TriangleQuadrature
import Numlib.Probability.MonteCarlo

/-!
# Quarteroni–Sacco–Saleri §9.9: multidimensional numerical integration

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.9.

Three methods for `∫_Ω f` in several variables. The *reduction formula* (9.56) writes the
integral over a domain normal to the `x` axis as an iterated integral, to which one-dimensional
composite rules apply (§9.9.1; the midpoint and trapezoidal reduction formulae, Programs 78–79, are
algorithms with no stated property and are not nodes). The *composite interpolatory rules on a
triangulation* (§9.9.2): (9.57) with the local weights `α_T^{(j)} = 2|T| ∫_{T̂} l̂_j`, the
composite midpoint (9.58) and trapezoidal (9.59) formulae, Definition 9.1 (degree of exactness on
the reference triangle `T̂`), Property 9.4 (not formalized), and the two symmetric formulae `I₃`,
`I₇`. The *Monte Carlo method* (§9.9.3): the integral as `|Ω|` times a mean value, the sample
mean (9.60), the strong law of large numbers and the variance identity (9.61).

The backbone is `Numlib/Approximation/TriangleQuadrature` — `Quadrature.refTriangle`, the
Dirichlet integrals, the four rules as `Approximation.IsExactOn (volume.restrict refTriangle)`,
which is Definition 9.1 verbatim, and the affine transport `Quadrature.isExactOn_affineImage` —
and `Numlib/Probability/MonteCarlo`; the reduction formula is Fubini's theorem
(`MeasureTheory.integral_prod`).

## Main definitions

* `normalDomain a b φ₁ φ₂` — the domain `{(x, y) : a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}` of §9.9.1.
* `triangleLinear v`, `triangleMap v`, `triangle v`, `area v` — for vertices `v : Fin 3 → ℝ²`,
  the affine map `F_T x̂ = a₁ + x̂₀ (a₂ - a₁) + x̂₁ (a₃ - a₁)` from `T̂` (chapter 8's (8.34),
  written on `Fin 2 → ℝ`), the triangle `T = F_T(T̂)` and its area `|T|`.
* `equation_9_57`, `equation_9_58`, `equation_9_59` — the composite rule on a finite family of
  triangles with local weights `2|T| ŵ_j` and nodes `F_T(ẑ_j)`, and its instances with the
  centroid rule (weights `|T|`) and the vertex rule (weights `|T|/3`).
* `definition_9_1` — degree of exactness `n` on `T̂`.

## Main results

* `equation_9_56` — the reduction formula.
* `triangleWeight_eq`, `area_eq` — `∫_T g = 2|T| ∫_{T̂} g ∘ F_T`, `|T| = |det B_T|/2`, and the
  local weights `|T|` (`k = 0`) and `|T|/3` (`k = 1`).
* `equation_9_58_eq`, `equation_9_59_eq` — (9.58) and (9.59) are (9.57) with the centroid and
  vertex reference rules.
* `definition_9_1_iff`, `definition_9_1_transport` — Definition 9.1 in the book's words, and its
  consequence on every triangle `T`: the transported rule is exact to the same degree on `T`.
* `equation_9_58_degreeOfExactness`, `symmetricFormulae` — the composite midpoint and trapezoidal
  formulae have degree of exactness exactly `1`, the symmetric formulae `I₃`, `I₇` degrees `2`
  and `3`.
* `monteCarlo_mean`, `monteCarlo_strongLaw`, `equation_9_61` — the Monte Carlo statements.

## Not formalized

Property 9.4 (`|E_k^c(f)| ≤ K_n h^{n+1} |Ω| M_{n+1}`) is a two-dimensional Bramble–Hilbert
estimate, out of reach on this pin; its node is open in the plan.

## Conventions

Points of the plane are `Fin 2 → ℝ` here (the backbone's exactness predicate lives on `ι → ℝ`;
chapter 8's `equation_8_34` writes the same affine map on `ℝ × ℝ`), except in the reduction
formula (9.56), whose iterated integral reads naturally on `ℝ × ℝ`. `ℙ_n(T̂)` of (8.35) is the
polynomials `p : MvPolynomial (Fin 2) ℝ` with `p.totalDegree ≤ n`. A family of triangles is
indexed by a finite type `ι`; no triangulation structure is assumed, as none is needed for the
statements formalized.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory Function Quadrature
open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter09

/-! ### §9.9.1: the reduction formula -/

/-- **A domain normal to the `x` axis** (§9.9.1, Figure 9.5):
`Ω = {(x, y) : a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}`. -/
def normalDomain (a b : ℝ) (φ₁ φ₂ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc a b ∧ φ₁ p.1 ≤ p.2 ∧ p.2 ≤ φ₂ p.1}

/-- A normal domain with continuous boundary curves is closed, hence measurable. -/
theorem isClosed_normalDomain {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ} (h₁ : ContinuousOn φ₁ (Icc a b))
    (h₂ : ContinuousOn φ₂ (Icc a b)) : IsClosed (normalDomain a b φ₁ φ₂) := by
  have hs : IsClosed (Icc a b ×ˢ (univ : Set ℝ)) := isClosed_Icc.prod isClosed_univ
  have hc₁ : ContinuousOn (fun p : ℝ × ℝ => (φ₁ p.1, p.2)) (Icc a b ×ˢ univ) :=
    (h₁.comp continuousOn_fst fun p hp => hp.1).prodMk continuousOn_snd
  have hc₂ : ContinuousOn (fun p : ℝ × ℝ => (p.2, φ₂ p.1)) (Icc a b ×ˢ univ) :=
    continuousOn_snd.prodMk (h₂.comp continuousOn_fst fun p hp => hp.1)
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

/-- The slice of a normal domain at abscissa `x`: the segment `[φ₁(x), φ₂(x)]` for `x ∈ [a, b]`
and empty otherwise. -/
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

/-- **(9.56), the reduction formula for double integrals.** For `φ₁ ≤ φ₂` continuous on
`[a, b]`, the domain `Ω = {(x, y) : a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}` normal to the `x` axis, and
`f` integrable on `Ω`,
`I(f) = ∫_Ω f(x, y) dx dy = ∫_a^b (∫_{φ₁(x)}^{φ₂(x)} f(x, y) dy) dx = ∫_a^b F_f(x) dx`.
Fubini's theorem (`MeasureTheory.integral_prod`) for the indicator of `Ω`. -/
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

/-- **The linear part `B_T = [a₂ - a₁ | a₃ - a₁]`** of the affine map (8.34) from the reference
triangle onto the triangle with vertices `v 0, v 1, v 2`:
`x̂ ↦ x̂₀ (v 1 - v 0) + x̂₁ (v 2 - v 0)`. -/
noncomputable def triangleLinear (v : Fin 3 → Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (LinearMap.proj 0).smulRight (v 1 - v 0) + (LinearMap.proj 1).smulRight (v 2 - v 0)

/-- **The affine map `F_T x̂ = a₁ + x̂₀ (a₂ - a₁) + x̂₁ (a₃ - a₁)`** (8.34) from the reference
triangle onto the triangle `T` with vertices `a₁ = v 0`, `a₂ = v 1`, `a₃ = v 2`. -/
noncomputable def triangleMap (v : Fin 3 → Fin 2 → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  triangleLinear v x + v 0

/-- **The triangle** `T = F_T(T̂)` with vertices `v 0, v 1, v 2`. -/
def triangle (v : Fin 3 → Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  triangleMap v '' refTriangle

/-- **The area `|T|`** of the triangle with vertices `v 0, v 1, v 2`. -/
noncomputable def area (v : Fin 3 → Fin 2 → ℝ) : ℝ :=
  (volume (triangle v)).toReal

/-- `F_T x̂ = a₁ + x̂₀ (a₂ - a₁) + x̂₁ (a₃ - a₁)`, written out. -/
theorem triangleMap_apply (v : Fin 3 → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    triangleMap v x = v 0 + x 0 • (v 1 - v 0) + x 1 • (v 2 - v 0) := by
  simp only [triangleMap, triangleLinear, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]
  abel

/-- `F_T` sends the reference vertices `(0, 0), (1, 0), (0, 1)` to `a₁, a₂, a₃`, and the reference
centroid `(1/3, 1/3)` to the centroid `a_T = (a₁ + a₂ + a₃)/3`. -/
theorem triangleMap_vertex (v : Fin 3 → Fin 2 → ℝ) :
    triangleMap v ![0, 0] = v 0 ∧ triangleMap v ![1, 0] = v 1 ∧ triangleMap v ![0, 1] = v 2 ∧
      triangleMap v ![1 / 3, 1 / 3] = (v 0 + v 1 + v 2) / 3 := by
  simp only [triangleMap_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i; simp
  · funext i; simp
  · funext i; simp
  · funext i; simp; ring

/-- **The area of a triangle** is `|det B_T|/2` (`Quadrature.volume_affineImage_refTriangle`),
so the Jacobian `|det B_T|` of `F_T` is `2|T|`. -/
theorem area_eq (v : Fin 3 → Fin 2 → ℝ) : area v = |LinearMap.det (triangleLinear v)| / 2 := by
  rw [area, triangle, show triangleMap v = fun y => triangleLinear v y + v 0 from rfl,
    volume_affineImage_refTriangle, ENNReal.toReal_ofReal (by positivity)]

/-- **§9.9.2, the local weights on `T` from the reference triangle**: for an integrable `g` on
`T`, `∫_T g = 2|T| ∫_{T̂} g ∘ F_T` when `F_T` is injective (the triangle is nondegenerate) — in
particular `α_T^{(j)} = ∫_T l_{j,T} = 2|T| ∫_{T̂} l̂_j` for the basis functions
`l_{j,T} = l̂_j ∘ F_T⁻¹` of (8.38) — and the weights of the constant rule (`k = 0`) and of the
vertex rule (`k = 1`) are `α_T^{(0)} = 2|T| ∫_{T̂} 1 = |T|` and
`α_T^{(j)} = 2|T| ∫_{T̂} λ_j = |T|/3`, the barycentric
coordinates `λ₀ = 1 - x̂ - ŷ`, `λ₁ = x̂`, `λ₂ = ŷ` integrating to `1/6` (`|T̂| = 1/2`). -/
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

/-- **(9.57), the composite interpolatory rule on a family of triangles.** For triangles `T`
with vertices `v T`, indexed by a finite type, and a reference rule with weights `ŵ_j` and nodes
`ẑ_j` on `T̂`, `I_k^c(f) = ∑_T ∑_j α_j^T f(z̃_j^T)` with the local weights `α_j^T = 2|T| ŵ_j`
(`triangleWeight_eq`) and the local nodes `z̃_j^T = F_T(ẑ_j)`. -/
noncomputable def equation_9_57 {ι K : Type*} [Fintype ι] [Fintype K] (v : ι → Fin 3 → Fin 2 → ℝ)
    (w : K → ℝ) (z : K → Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℝ) : ℝ :=
  ∑ T, ∑ j, (2 * area (v T) * w j) * f (triangleMap (v T) (z j))

/-- **(9.58), the composite midpoint formula** `I_0^c(f) = ∑_T |T| f(a_T)`, `a_T` the centroid
`(a₁ + a₂ + a₃)/3` of `T`. -/
noncomputable def equation_9_58 {ι : Type*} [Fintype ι] (v : ι → Fin 3 → Fin 2 → ℝ)
    (f : (Fin 2 → ℝ) → ℝ) : ℝ :=
  ∑ T, area (v T) * f ((v T 0 + v T 1 + v T 2) / 3)

/-- **(9.59), the composite trapezoidal formula** `I_1^c(f) = (1/3) ∑_T |T| ∑_{j} f(a_T^{(j)})`
at the vertices. -/
noncomputable def equation_9_59 {ι : Type*} [Fintype ι] (v : ι → Fin 3 → Fin 2 → ℝ)
    (f : (Fin 2 → ℝ) → ℝ) : ℝ :=
  1 / 3 * ∑ T, area (v T) * ∑ j, f (v T j)

/-- (9.58) is (9.57) with the centroid reference rule (`ŵ = 1/2` at `(1/3, 1/3)`). -/
theorem equation_9_58_eq {ι : Type*} [Fintype ι] (v : ι → Fin 3 → Fin 2 → ℝ)
    (f : (Fin 2 → ℝ) → ℝ) :
    equation_9_58 v f
      = equation_9_57 v (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => ![1 / 3, 1 / 3]) f := by
  simp only [equation_9_58, equation_9_57, Fin.sum_univ_one, (triangleMap_vertex _).2.2.2]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

/-- (9.59) is (9.57) with the vertex reference rule (`ŵ = 1/6` at the three vertices of `T̂`). -/
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

/-- **Definition 9.1.** The quadrature formula (9.57), with reference weights `ŵ` and nodes `ẑ`,
has degree of exactness `n` if `I_k^{T̂}(p) = ∫_{T̂} p` for every `p ∈ ℙ_n(T̂)`: the backbone's
`Approximation.IsExactOn (volume.restrict refTriangle) ŵ ẑ n`. -/
def definition_9_1 {K : Type*} [Fintype K] (w : K → ℝ) (z : K → Fin 2 → ℝ) (n : ℕ) : Prop :=
  Approximation.IsExactOn (volume.restrict refTriangle) w z n

/-- Definition 9.1 in the book's words: `∑_j ŵ_j p(ẑ_j) = ∫_{T̂} p` for every polynomial `p` of
total degree at most `n` — the space `ℙ_n(T̂)` of (8.35). -/
theorem definition_9_1_iff {K : Type*} [Fintype K] (w : K → ℝ) (z : K → Fin 2 → ℝ) (n : ℕ) :
    definition_9_1 w z n ↔ ∀ p : MvPolynomial (Fin 2) ℝ, p.totalDegree ≤ n →
      ∑ j, w j * MvPolynomial.eval (z j) p = ∫ x in refTriangle, MvPolynomial.eval x p :=
  Iff.rfl

/-- **Exactness on `T̂` transports to every triangle**: if the reference rule has degree of
exactness `n` (Definition 9.1), then on a nondegenerate triangle `T` the local rule of (9.57),
with weights `2|T| ŵ_j` and nodes `F_T(ẑ_j)`, integrates every `p ∈ ℙ_n(T)` exactly — the sense in
which Property 9.4 speaks of the "degree of exactness on `Ω`". The backbone's
`Quadrature.isExactOn_affineImage`. -/
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

/-- **§9.9.2: "the composite formulae (9.58) and (9.59) both have degree of exactness equal to
`1`."** On the reference triangle the centroid rule and the vertex rule are exact on `ℙ₁` and not
on `ℙ₂`. -/
theorem equation_9_58_degreeOfExactness :
    (definition_9_1 (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => ![1 / 3, 1 / 3]) 1 ∧
        ¬ definition_9_1 (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => ![1 / 3, 1 / 3]) 2) ∧
      (definition_9_1 (fun _ : Fin 3 => (1 / 6 : ℝ)) ![![0, 0], ![1, 0], ![0, 1]] 1 ∧
        ¬ definition_9_1 (fun _ : Fin 3 => (1 / 6 : ℝ)) ![![0, 0], ![1, 0], ![0, 1]] 2) :=
  ⟨⟨isExactOn_centroid, not_isExactOn_centroid_two⟩, ⟨isExactOn_vertex, not_isExactOn_vertex_two⟩⟩

/-- **§9.9.2, the symmetric formulae.** On the reference triangle, `I₃(f) = (|T̂|/3) ∑_j f(m_j)`
at the three edge midpoints has degree of exactness `2`, and
`I₇(f) = (|T̂|/60)(3 ∑_i f(a^{(i)}) + 8 ∑_j f(m_j) + 27 f(a_{T̂}))` has degree of exactness `3`;
both transport to every triangle by `definition_9_1_transport`. -/
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

/-! ### §9.9.3: the Monte Carlo method -/

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} {d : ℕ}

/-- **§9.9.3, the integral as a mean value.** For `Ω ⊆ ℝⁿ` measurable of finite positive volume,
`∫_Ω f(x) dx = |Ω| ∫_{ℝⁿ} |Ω|⁻¹ χ_Ω(x) f(x) dx = |Ω| μ(f)`, where `μ(f)` is the mean of `f(X)` for
`X` with the uniform density `|Ω|⁻¹ χ_Ω` — the conditional measure `volume[|Ω]`. -/
theorem monteCarlo_mean {Ω : Set (Fin d → ℝ)} (h0 : volume Ω ≠ 0) (htop : volume Ω ≠ ⊤)
    (f : (Fin d → ℝ) → ℝ) :
    ∫ x in Ω, f x = (volume Ω).toReal * ∫ x, f x ∂(volume[|Ω]) :=
  MonteCarlo.setIntegral_eq_volume_mul_integral_cond h0 htop f

/-- **(9.60) and the strong law of large numbers.** For samples `X₁, X₂, …` on `Ω`, pairwise
independent and each with the uniform law `volume[|Ω]` on `Ω ⊆ ℝⁿ` (`0 < |Ω| < ∞`), and `f`
measurable with `f(X₁)` integrable, the average `I_N(f) = (∑_{i≤N} f(X_i))/N` converges with
probability `1` to the mean value `μ(f) = |Ω|⁻¹ ∫_Ω f` as `N → ∞`. The backbone's
`MonteCarlo.tendsto_sampleMean_ae` (Mathlib's strong law) together with `monteCarlo_mean`. -/
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

/-- **(9.61)**: for mutually independent samples `X_i`, each with the same law as `X₁`, and
`f(X₁) ∈ L²`, the standard deviation of the average is `σ(I_N(f)) = σ(f)/√N`, i.e.
`Var(I_N(f)) = Var(f(X₁))/N`; hence the statistical error decays as `O(N^{-1/2})`, independently
of the dimension `n` — and Chebyshev's inequality makes this quantitative:
`P{|I_N(f) - μ(f)| ≥ c} ≤ σ(f)²/(N c²)`. The backbone's `MonteCarlo.variance_sampleMean` and
`MonteCarlo.meas_ge_le_sampleMean`. -/
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
