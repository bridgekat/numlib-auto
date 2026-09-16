import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Numlib.Approximation.Hyperinterpolation
import Numlib.RingTheory.MvPolynomial.TotalDegree

/-!
# Quadrature on the reference triangle

Quadrature on the reference triangle `T̂ = {(x, y) : x, y ≥ 0, x + y ≤ 1}` and, by the affine map
onto a triangle `T`, on `T` ([quarteroni2000numerical] §9.9.2). The vocabulary is
`Approximation.IsExactOn μ w x m` of `Numlib/Approximation/Hyperinterpolation` — exactness on the
multivariate polynomials of total degree at most `m` against a measure — with
`μ = volume.restrict refTriangle` on `Fin 2 → ℝ`, which is the book's Definition 9.1 verbatim.

## Main definitions

* `Quadrature.refTriangle` — the reference triangle, with `measurableSet_refTriangle`,
  `isCompact_refTriangle` and `volume_refTriangle : volume refTriangle = 1/2`.
* `Quadrature.affinePoly A c` — the affine map `y ↦ A y + c` as a family of polynomials of total
  degree at most one, the tool of the transport lemma.

## Main results

* `integral_pow_mul_one_sub_pow` — the Beta integral with natural exponents,
  `∫₀¹ xᵃ (1 - x)ᵇ = a! b!/(a + b + 1)!`, by integration by parts.
* `Quadrature.integral_refTriangle_pow_mul_pow` — Dirichlet's integral on the triangle,
  `∫_{T̂} xᵃ yᵇ = a! b!/(a + b + 2)!`, by Fubini on `ℝ × ℝ` and the Beta integral.
* `Quadrature.isExactOn_refTriangle_iff` — exactness
  to degree `m` is exactness on the monomials of degree at most `m`; on `T̂` it is the finite
  system `∑_k w_k x_k^a y_k^b = a! b!/(a + b + 2)!`, `a + b ≤ m`.
* `Quadrature.isExactOn_centroid`, `Quadrature.isExactOn_vertex`,
  `Quadrature.isExactOn_edgeMidpoint`, `Quadrature.isExactOn_sevenPoint` — the four rules the
  book displays, exact to degrees `1`, `1`, `2`, `3`, each with its `not_isExactOn_*` companion
  showing the degree is sharp.
* `Quadrature.isExactOn_affineImage` — a rule exact to degree `m` on `T` transports along an
  injective affine map `y ↦ A y + c` to a rule exact to degree `m` on the image, with the weights
  scaled by `|det A|`; `Quadrature.volume_affineImage_refTriangle` gives the area
  `|T| = |det A|/2` of the image triangle, so the scale is the book's `2|T|`.

Property 9.4 of [quarteroni2000numerical] (the `O(h^{n+1})` error of a composite rule of degree
`n` on a triangulation) is **not** here: it is a Bramble–Hilbert estimate in two dimensions, out
of reach (`notes/frontier.md`), and stays a "not formalized" node of the surface. The composite
rule (9.57) over a triangulation is a finite sum of transported rules and is left to the surface.

## Implementation notes

The degree bound for the affine substitution
is `MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one` of
`Numlib/RingTheory/MvPolynomial/TotalDegree`. The integrals on `Fin 2 → ℝ` are transported to
`ℝ × ℝ` by `MeasurableEquiv.finTwoArrow`, which is measure preserving.
-/

open Set Filter MeasureTheory Finset intervalIntegral
open scoped Nat

/-! ### The Beta integral with natural exponents -/

/-- **The Beta integral with natural exponents**: `∫₀¹ xᵃ (1 - x)ᵇ dx = a! b!/(a + b + 1)!`, by
induction on `b` with one integration by parts per step. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b = (a ! * b ! : ℝ) / (a + b + 1)! := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero a), sub_zero,
      Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  | succ b ih =>
    -- integration by parts: `u = (1 - x)^(b+1)`, `v = x^(a+1)/(a+1)`
    have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => (1 - x) ^ (b + 1))
        (-((b + 1 : ℝ) * (1 - x) ^ b)) x := by
      intro x _
      exact (((hasDerivAt_id' x).const_sub 1).pow (b + 1)).congr_deriv (by push_cast; ring)
    have ha1 : ((a : ℝ) + 1) ≠ 0 := by positivity
    have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ (a + 1) / (a + 1)) (x ^ a) x := by
      intro x _
      exact (((hasDerivAt_id' x).pow (a + 1)).div_const ((a : ℝ) + 1)).congr_deriv
        (by push_cast; field_simp)
    have hparts := integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -((b + 1 : ℝ) * (1 - x) ^ b)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => x ^ a).intervalIntegrable _ _)
    have e1 : ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1)
        = ∫ x in (0 : ℝ)..1, (1 - x) ^ (b + 1) * x ^ a :=
      integral_congr fun x _ => mul_comm _ _
    have e2 : ∫ x in (0 : ℝ)..1, -((b + 1 : ℝ) * (1 - x) ^ b) * (x ^ (a + 1) / (a + 1))
        = -((b + 1 : ℝ) / (a + 1)) * ∫ x in (0 : ℝ)..1, x ^ (a + 1) * (1 - x) ^ b := by
      rw [← intervalIntegral.integral_const_mul]
      exact integral_congr fun x _ => by ring
    rw [e1, hparts, e2, ih (a + 1)]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero b), zero_mul, one_pow, sub_zero, zero_sub,
      zero_pow (Nat.succ_ne_zero a), zero_div, mul_zero]
    rw [show a + 1 + b + 1 = (a + b + 1) + 1 by ring,
      show a + (b + 1) + 1 = (a + b + 1) + 1 by ring, Nat.factorial_succ (a + b + 1),
      Nat.factorial_succ b, Nat.factorial_succ a]
    push_cast
    field_simp

/-! ### Generic API: exactness on monomials -/

namespace Quadrature

variable {ι K : Type*} [Fintype ι] [Fintype K]

section Affine

variable [DecidableEq ι]

/-- **The affine map `y ↦ A y + c` as polynomials**: `affinePoly A c i` is the polynomial
`cᵢ + ∑ⱼ Aᵢⱼ Xⱼ` evaluating to `(A y + c) i`. -/
noncomputable def affinePoly (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (i : ι) :
    MvPolynomial ι ℝ :=
  MvPolynomial.C (c i) + ∑ j, MvPolynomial.C (A (Pi.single j 1) i) * MvPolynomial.X j

/-- `affinePoly A c i` evaluates to the `i`-th coordinate of `A y + c`. -/
theorem eval_affinePoly (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (y : ι → ℝ) (i : ι) :
    MvPolynomial.eval y (affinePoly A c i) = (A y + c) i := by
  simp only [affinePoly, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Pi.add_apply]
  rw [LinearMap.pi_apply_eq_sum_univ A y, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  have e : (fun j' => if j = j' then (1 : ℝ) else 0) = Pi.single j 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  rw [e]

/-- The polynomials of an affine map have total degree at most one. -/
theorem totalDegree_affinePoly_le (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (i : ι) :
    (affinePoly A c i).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]; exact zero_le_one
  · refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_X _).le

/-- Evaluating `p` at `A y + c` is evaluating the substituted polynomial at `y`. -/
theorem eval_add_eq_eval_bind₁ (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (p : MvPolynomial ι ℝ)
    (y : ι → ℝ) :
    MvPolynomial.eval (A y + c) p
      = MvPolynomial.eval y (MvPolynomial.bind₁ (affinePoly A c) p) := by
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) (A y + c) p
    = MvPolynomial.eval₂Hom (RingHom.id ℝ) y (MvPolynomial.bind₁ (affinePoly A c) p)
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 2
  funext i
  exact (eval_affinePoly A c y i).symm

omit [DecidableEq ι] in
/-- **Transport of a rule by an affine map** ([quarteroni2000numerical] §9.9.2). For an
injective linear map `A` and a vector `c`, a rule exact to degree `m` on a measurable set `T`
transports along `F y = A y + c` to a rule exact to degree `m` on `F '' T`: the nodes are `F(x_k)`
and the weights are `|det A| w_k`, the Jacobian of the change of variables. A polynomial of total
degree at most `m` composed with `F` is again one (`totalDegree_bind₁_le_of_totalDegree_le_one`).
For the reference triangle and a triangle `T` of area `|T|` the scale is `|det A| = 2|T|`
(`volume_affineImage_refTriangle`), the book's `α_T^{(j)} = 2|T| ∫_{T̂} l̂_j`. -/
theorem isExactOn_affineImage {T : Set (ι → ℝ)} (hT : MeasurableSet T)
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hA : Function.Injective A) (c : ι → ℝ) {w : K → ℝ}
    {x : K → ι → ℝ} {m : ℕ} (h : Approximation.IsExactOn (volume.restrict T) w x m) :
    Approximation.IsExactOn (volume.restrict ((fun y => A y + c) '' T))
      (fun k => |LinearMap.det A| * w k) (fun k => A (x k) + c) m := by
  classical
  intro p hp
  have hinj : InjOn (fun y => A y + c) T := fun y _ z _ hyz => hA (add_right_cancel hyz)
  have hderiv : ∀ y ∈ T, HasFDerivWithinAt (fun y => A y + c)
      (LinearMap.toContinuousLinearMap A) T y := fun y _ =>
    ((LinearMap.toContinuousLinearMap A).hasFDerivAt.add_const c).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hT hderiv hinj]
  simp only [LinearMap.det_toContinuousLinearMap, smul_eq_mul, eval_add_eq_eval_bind₁]
  rw [MeasureTheory.integral_const_mul,
    ← h _ ((MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one
    (totalDegree_affinePoly_le A c) p).trans hp), Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq ι] in
/-- The volume of the affine image of a set: `|det A|` times the volume. -/
theorem volume_affineImage (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (T : Set (ι → ℝ)) :
    volume ((fun y => A y + c) '' T) = ENNReal.ofReal |LinearMap.det A| * volume T := by
  have e : (fun y => A y + c) '' T = (fun y => y + c) '' (A '' T) := by
    rw [image_image]
  rw [e, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_image_linearMap]

end Affine

/-! ### The reference triangle -/

/-- **The reference triangle** `T̂ = {(x, y) : x ≥ 0, y ≥ 0, x + y ≤ 1}`, with vertices `(0, 0)`,
`(1, 0)`, `(0, 1)`, as a subset of `Fin 2 → ℝ`.

Reference: [quarteroni2000numerical], §9.9.2. -/
def refTriangle : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

/-- The reference triangle read in `ℝ × ℝ`, the coordinates on which Fubini's theorem is
stated. -/
def refTriangle' : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

/-- The reference triangle is the preimage of its `ℝ × ℝ` copy under the coordinate
identification. -/
theorem refTriangle_eq_preimage :
    refTriangle = MeasurableEquiv.finTwoArrow ⁻¹' refTriangle' := by
  ext x
  simp [refTriangle, refTriangle', MeasurableEquiv.finTwoArrow]

/-- The `ℝ × ℝ` copy of the reference triangle is compact. -/
theorem isCompact_refTriangle' : IsCompact refTriangle' := by
  refine (isCompact_Icc (a := ((0 : ℝ), (0 : ℝ))) (b := (1, 1))).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    exact ⟨⟨hx, hy⟩, ⟨by simp only at *; linarith, by simp only at *; linarith⟩⟩

/-- The `ℝ × ℝ` copy of the reference triangle is measurable. -/
theorem measurableSet_refTriangle' : MeasurableSet refTriangle' :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))

/-- The reference triangle is measurable. -/
theorem measurableSet_refTriangle : MeasurableSet refTriangle := by
  rw [refTriangle_eq_preimage]
  exact MeasurableEquiv.finTwoArrow.measurable measurableSet_refTriangle'

/-- The reference triangle is compact: a closed subset of the unit square. -/
theorem isCompact_refTriangle : IsCompact refTriangle := by
  refine (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := 1)).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const (continuous_apply 0)).inter
      ((isClosed_le continuous_const (continuous_apply 1)).inter
        (isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const))
  · rintro x ⟨h0, h1, h01⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith

/-- The slice of the triangle at abscissa `x` is the segment `[0, 1 - x]` for `x ∈ [0, 1]` and
empty otherwise. -/
theorem refTriangle'_indicator_slice (g : ℝ × ℝ → ℝ) (x : ℝ) :
    (fun y => refTriangle'.indicator g (x, y))
      = if x ∈ Icc (0 : ℝ) 1 then (Icc 0 (1 - x)).indicator (fun y => g (x, y)) else 0 := by
  funext y
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [ite_eq_left hx]
    by_cases hy : y ∈ Icc 0 (1 - x)
    · rw [indicator_of_mem hy, indicator_of_mem]
      exact ⟨hx.1, hy.1, by linarith [hy.2]⟩
    · rw [indicator_of_notMem hy, indicator_of_notMem]
      rintro ⟨-, h1, h2⟩
      exact hy ⟨h1, by linarith⟩
  · rw [ite_eq_right hx, Pi.zero_apply, indicator_of_notMem]
    rintro ⟨h1, h2, h3⟩
    exact hx ⟨h1, by linarith⟩

/-- Dirichlet's integral on the triangle, in the coordinates of `ℝ × ℝ`: Fubini reduces it to
`∫₀¹ xᵃ (1 - x)^{b+1}/(b + 1) dx`, a Beta integral. -/
theorem integral_refTriangle'_pow_mul_pow (a b : ℕ) :
    ∫ p in refTriangle', p.1 ^ a * p.2 ^ b = (a ! * b ! : ℝ) / (a + b + 2)! := by
  set g : ℝ × ℝ → ℝ := fun p => p.1 ^ a * p.2 ^ b with hg
  have hint : Integrable (refTriangle'.indicator g) volume := by
    rw [integrable_indicator_iff measurableSet_refTriangle']
    exact (by fun_prop : Continuous g).continuousOn.integrableOn_compact isCompact_refTriangle'
  rw [← MeasureTheory.integral_indicator measurableSet_refTriangle', Measure.volume_eq_prod,
    integral_prod _ (by rwa [← Measure.volume_eq_prod])]
  -- the inner integrals
  have hinner : ∀ x : ℝ, (∫ y, refTriangle'.indicator g (x, y))
      = (Icc (0 : ℝ) 1).indicator (fun x => x ^ a * (1 - x) ^ (b + 1) / (b + 1)) x := by
    intro x
    rw [refTriangle'_indicator_slice]
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · rw [ite_eq_left hx, indicator_of_mem hx, MeasureTheory.integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [hx.2])]
      simp only [hg]
      rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero b),
        sub_zero]
      ring
    · rw [ite_eq_right hx, indicator_of_notMem hx]
      simp
  rw [integral_congr_ae (Eventually.of_forall hinner),
    MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  have e : ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1) / (b + 1)
      = (1 / (b + 1 : ℝ)) * ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_congr fun x _ => by ring
  rw [e, integral_pow_mul_one_sub_pow, show a + (b + 1) + 1 = a + b + 2 by ring,
    Nat.factorial_succ b]
  push_cast
  field_simp

/-- The coordinate identification `Fin 2 → ℝ ≃ ℝ × ℝ` preserves Lebesgue measure. -/
theorem measurePreserving_finTwoArrow_volume :
    MeasurePreserving (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) volume volume :=
  measurePreserving_finTwoArrow (volume : Measure ℝ)

/-- **Dirichlet's integral on the reference triangle**: `∫_{T̂} xᵃ yᵇ = a! b!/(a + b + 2)!`. -/
theorem integral_refTriangle_pow_mul_pow (a b : ℕ) :
    ∫ x in refTriangle, x 0 ^ a * x 1 ^ b = (a ! * b ! : ℝ) / (a + b + 2)! := by
  rw [refTriangle_eq_preimage, ← integral_refTriangle'_pow_mul_pow]
  exact measurePreserving_finTwoArrow_volume.setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b)
    refTriangle'

/-- **The area of the reference triangle is `1/2`.** -/
theorem volume_refTriangle : volume refTriangle = ENNReal.ofReal (1 / 2) := by
  have h := integral_refTriangle_pow_mul_pow 0 0
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, zero_add,
    setIntegral_const, smul_eq_mul] at h
  rw [← ENNReal.ofReal_toReal (isCompact_refTriangle.measure_lt_top).ne, ← measureReal_def, h]
  norm_num [Nat.factorial]

/-- **The area of a triangle** `T = F(T̂)`, `F y = A y + c`, is `|det A|/2`; so the Jacobian of
the map from the reference triangle is `|det A| = 2|T|`. -/
theorem volume_affineImage_refTriangle (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (c : Fin 2 → ℝ) :
    volume ((fun y => A y + c) '' refTriangle) = ENNReal.ofReal (|LinearMap.det A| / 2) := by
  rw [volume_affineImage, volume_refTriangle, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-! ### The rules of the book -/

/-- **Exactness on the reference triangle is a finite system of equations**: a rule with weights
`w` and nodes `x` is exact to degree `m` on `T̂` iff
`∑_k w_k x_k^a y_k^b = a! b!/(a + b + 2)!` for all `a + b ≤ m` — the book's Definition 9.1 read
on the monomials. -/
theorem isExactOn_refTriangle_iff (w : K → ℝ) (x : K → Fin 2 → ℝ) (m : ℕ) :
    Approximation.IsExactOn (volume.restrict refTriangle) w x m ↔
      ∀ a b : ℕ, a + b ≤ m →
        ∑ k, w k * (x k 0 ^ a * x k 1 ^ b) = (a ! * b ! : ℝ) / (a + b + 2)! := by
  rw [Approximation.isExactOn_iff_forall_monomial]
  · constructor
    · intro h a b hab
      have := h (Finsupp.equivFunOnFinite.symm ![a, b]) (by
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]; simpa using hab)
      simpa [Fin.prod_univ_two, integral_refTriangle_pow_mul_pow] using this
    · intro h d hd
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
      have := h (d 0) (d 1) hd
      simpa [Fin.prod_univ_two, integral_refTriangle_pow_mul_pow] using this
  · intro d
    exact (by fun_prop : Continuous fun y : Fin 2 → ℝ => ∏ i, y i ^ d i).continuousOn
      |>.integrableOn_compact isCompact_refTriangle

/-- **The centroid rule** `|T̂| f(1/3, 1/3)` is exact to degree `1` on `T̂`
([quarteroni2000numerical] (9.58) on the reference triangle). -/
theorem isExactOn_centroid :
    Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 1 => (1 / 2 : ℝ))
      (fun _ => ![1 / 3, 1 / 3]) 1 := by
  rw [isExactOn_refTriangle_iff]
  intro a b hab
  have ha : a ≤ 1 := by omega
  have hb : b ≤ 1 := by omega
  interval_cases a <;> interval_cases b <;>
    first | omega | norm_num [Fin.sum_univ_succ, Nat.factorial]

/-- The centroid rule is not exact to degree `2`: on `x²` it gives `1/18 ≠ 1/12`. -/
theorem not_isExactOn_centroid_two :
    ¬ Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 1 => (1 / 2 : ℝ))
      (fun _ => ![1 / 3, 1 / 3]) 2 := by
  rw [isExactOn_refTriangle_iff]
  intro h
  have := h 2 0 le_rfl
  norm_num [Fin.sum_univ_succ, Nat.factorial] at this

/-- **The vertex ("trapezoidal") rule** `(|T̂|/3) ∑ⱼ f(aⱼ)` at the three vertices is exact to
degree `1` on `T̂` ([quarteroni2000numerical] (9.59) on the reference triangle). -/
theorem isExactOn_vertex :
    Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 3 => (1 / 6 : ℝ))
      ![![0, 0], ![1, 0], ![0, 1]] 1 := by
  rw [isExactOn_refTriangle_iff]
  intro a b hab
  have ha : a ≤ 1 := by omega
  have hb : b ≤ 1 := by omega
  interval_cases a <;> interval_cases b <;>
    first | omega | norm_num [Fin.sum_univ_succ, Nat.factorial]

/-- The vertex rule is not exact to degree `2`: on `x²` it gives `1/6 ≠ 1/12`. -/
theorem not_isExactOn_vertex_two :
    ¬ Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 3 => (1 / 6 : ℝ))
      ![![0, 0], ![1, 0], ![0, 1]] 2 := by
  rw [isExactOn_refTriangle_iff]
  intro h
  have := h 2 0 le_rfl
  norm_num [Fin.sum_univ_succ, Nat.factorial] at this

/-- **The edge-midpoint rule** `(|T̂|/3) ∑ⱼ f(mⱼ)` at the three edge midpoints is exact to degree
`2` on `T̂` — the first symmetric formula `I₃` of [quarteroni2000numerical] §9.9.2. -/
theorem isExactOn_edgeMidpoint :
    Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 3 => (1 / 6 : ℝ))
      ![![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2]] 2 := by
  rw [isExactOn_refTriangle_iff]
  intro a b hab
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;>
    first | omega | norm_num [Fin.sum_univ_succ, Nat.factorial]

/-- The edge-midpoint rule is not exact to degree `3`. -/
theorem not_isExactOn_edgeMidpoint_three :
    ¬ Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 3 => (1 / 6 : ℝ))
      ![![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2]] 3 := by
  rw [isExactOn_refTriangle_iff]
  intro h
  have := h 3 0 le_rfl
  norm_num [Fin.sum_univ_succ, Nat.factorial] at this

/-- **The seven-point rule** `(|T̂|/60)(3 ∑ f(aⱼ) + 8 ∑ f(mⱼ) + 27 f(centroid))` — weights
`1/40` at the three vertices, `1/15` at the three edge midpoints and `9/40` at the centroid — is
exact to degree `3` on `T̂`: the second symmetric formula `I₇` of [quarteroni2000numerical]
§9.9.2. -/
theorem isExactOn_sevenPoint :
    Approximation.IsExactOn (volume.restrict refTriangle)
      ![1 / 40, 1 / 40, 1 / 40, 1 / 15, 1 / 15, 1 / 15, 9 / 40]
      ![![0, 0], ![1, 0], ![0, 1], ![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2], ![1 / 3, 1 / 3]]
      3 := by
  rw [isExactOn_refTriangle_iff]
  intro a b hab
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;>
    first | omega | norm_num [Fin.sum_univ_succ, Nat.factorial]

/-- The seven-point rule is not exact to degree `4`. -/
theorem not_isExactOn_sevenPoint_four :
    ¬ Approximation.IsExactOn (volume.restrict refTriangle)
      ![1 / 40, 1 / 40, 1 / 40, 1 / 15, 1 / 15, 1 / 15, 9 / 40]
      ![![0, 0], ![1, 0], ![0, 1], ![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2], ![1 / 3, 1 / 3]]
      4 := by
  rw [isExactOn_refTriangle_iff]
  intro h
  have := h 4 0 le_rfl
  norm_num [Fin.sum_univ_succ, Nat.factorial] at this

end Quadrature
