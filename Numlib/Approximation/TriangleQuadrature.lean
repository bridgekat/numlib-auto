/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Numlib.Analysis.SpecialFunctions.Integrals.Beta
import Numlib.Approximation.Hyperinterpolation
import Numlib.RingTheory.MvPolynomial.TotalDegree

/-!
# Quadrature on the reference triangle

This file studies quadrature rules on the reference triangle $\hat T = \{(x, y) : x \ge 0,\ y \ge
0,\ x + y \le 1\}$ and, through an affine map, on any triangle $T$, as in §9.9.2 of
[quarteroni2000numerical]. A rule with weights $w_k$ and nodes $x_k \in \mathbb{R}^2$ approximates
$\int_{\hat T} f$ by $\sum_k w_k f(x_k)$. It is exact to degree $m$ if it integrates every
polynomial of total degree at most $m$ without error (`Approximation.IsExactOn` for the Lebesgue
measure restricted to $\hat T$). This is Definition 9.1 of the source.

The key computation is Dirichlet's integral $\int_{\hat T} x^a y^b = a!\, b! / (a + b + 2)!$. With
it, exactness to degree $m$ becomes a finite system of equations in the weights and the nodes. The
file verifies four rules of the source: the centroid rule and the vertex rule are exact to degree
$1$, the edge-midpoint rule to degree $2$, and the seven-point rule to degree $3$, and none of them
is exact to a higher degree. An injective affine map $F(y) = Ay + c$ transports a rule that is exact
to degree $m$ on a set $T$ to a rule that is exact to degree $m$ on $F(T)$, with the weights
multiplied by $|\det A|$. For $T = \hat T$ this factor is $2|F(\hat T)|$.

## Main definitions

* `Quadrature.affinePoly`: the coordinates of the affine map $y \mapsto Ay + c$, as polynomials of
  total degree at most one.
* `Quadrature.refTriangle`: the reference triangle $\hat T$ in $\mathbb{R}^2$.

## Main results

* `Quadrature.isExactOn_affineImage`: an injective affine map $F(y) = Ay + c$ transports a rule
  exact to degree $m$ on $T$ to a rule exact to degree $m$ on $F(T)$, with nodes $F(x_k)$ and
  weights $|\det A|\, w_k$.
* `Quadrature.integral_refTriangle_pow_mul_pow`: $\int_{\hat T} x^a y^b = a!\, b! / (a + b + 2)!$.
* `Quadrature.volume_refTriangle`: the area of $\hat T$ is $1/2$.
* `Quadrature.volume_affineImage_refTriangle`: the area of $F(\hat T)$ is $|\det A| / 2$.
* `Quadrature.isExactOn_refTriangle_iff`: a rule is exact to degree $m$ on $\hat T$ if and only if
  $\sum_k w_k \xi_k^a \eta_k^b = a!\, b! / (a + b + 2)!$ for all $a + b \le m$, where
  $x_k = (\xi_k, \eta_k)$.
* `Quadrature.isExactOn_centroid`, `Quadrature.isExactOn_vertex`,
  `Quadrature.isExactOn_edgeMidpoint`, `Quadrature.isExactOn_sevenPoint`: the centroid, vertex,
  edge-midpoint and seven-point rules are exact to degrees $1$, $1$, $2$ and $3$ on $\hat T$.
* `Quadrature.not_isExactOn_centroid_two`, `Quadrature.not_isExactOn_vertex_two`,
  `Quadrature.not_isExactOn_edgeMidpoint_three`, `Quadrature.not_isExactOn_sevenPoint_four`: these
  degrees are sharp.

## Proof outline

Fubini's theorem reduces Dirichlet's integral to the Beta integral
$\int_0^1 x^a (1 - x)^{b+1} / (b + 1)\, dx$ (`integral_pow_mul_one_sub_pow`). Since a polynomial is
a linear combination of monomials, exactness to degree $m$ is exactness on the monomials $x^a y^b$
with $a + b \le m$. For the transport, a polynomial of total degree at most $m$ composed with an
affine map is again a polynomial of total degree at most $m$, and the change of variables formula
gives the Jacobian $|\det A|$.

## Implementation notes

* Points of the plane are `Fin 2 → ℝ`, and $(x, y)$ is `(x 0, x 1)`. Integrals are moved to `ℝ × ℝ`,
  where Fubini's theorem is stated, by `MeasurableEquiv.finTwoArrow`, which preserves Lebesgue
  measure.
* The bound on the total degree after the affine substitution is
  `MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one`.
* Property 9.4 of [quarteroni2000numerical], the error $O(h^{n+1})$ of a composite rule of degree
  $n$ on a triangulation, is not in this file. It needs a Bramble–Hilbert estimate in two
  dimensions. The composite rule (9.57) over a triangulation is a finite sum of transported rules
  and is not defined here.
-/

open Set Filter MeasureTheory Finset intervalIntegral
open scoped Nat

/-! ### Exactness under affine maps -/

namespace Quadrature

variable {ι K : Type*} [Fintype ι] [Fintype K]

section Affine

variable [DecidableEq ι]

/-- For a linear map $A$ on $\mathbb{R}^\iota$, a vector $c \in \mathbb{R}^\iota$ and an index $i$,
`Quadrature.affinePoly A c i` is the polynomial $c_i + \sum_j A_{ij} X_j$, where $A_{ij}$ is the
$i$-th coordinate of $A e_j$. It is the $i$-th coordinate of the **affine map**
$y \mapsto Ay + c$. -/
noncomputable def affinePoly (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (i : ι) :
    MvPolynomial ι ℝ :=
  MvPolynomial.C (c i) + ∑ j, MvPolynomial.C (A (Pi.single j 1) i) * MvPolynomial.X j

/-- The polynomial `Quadrature.affinePoly A c i` evaluated at $y$ is $(Ay + c)_i$. -/
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

/-- Each coordinate polynomial `Quadrature.affinePoly A c i` of an affine map has total degree at
most one. -/
theorem totalDegree_affinePoly_le (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (i : ι) :
    (affinePoly A c i).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]; exact zero_le_one
  · refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_X _).le

/-- Let $p$ be a polynomial in the variables $X_i$, and let $q$ be the polynomial obtained from $p$
by the substitution $X_i \mapsto c_i + \sum_j A_{ij} X_j$. Then $p(Ay + c) = q(y)$ for every
$y$.

The substituted polynomial is `MvPolynomial.bind₁ (Quadrature.affinePoly A c) p`. -/
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
/-- **Transport of a rule by an affine map.** Let $T \subseteq \mathbb{R}^\iota$ be measurable, let
$A$ be an injective linear map on $\mathbb{R}^\iota$, let $c \in \mathbb{R}^\iota$, and let
$F(y) = Ay + c$. If the rule with weights $w_k$ and nodes $x_k$ is exact to degree $m$ for the
Lebesgue measure on $T$, then the rule with weights $|\det A|\, w_k$ and nodes $F(x_k)$ is exact
to degree $m$ for the Lebesgue measure on $F(T)$.

This is the transport of a rule from the reference triangle in §9.9.2 of
[quarteroni2000numerical]. For $T = \hat T$ the factor is $|\det A| = 2|F(\hat T)|$ by
`Quadrature.volume_affineImage_refTriangle`, which gives the weights
$\alpha_T^{(j)} = 2|T| \int_{\hat T} \hat l_j$ of the source. The proof uses the change of
variables formula and the fact that a polynomial of total degree at most $m$ composed with $F$
has total degree at most $m$ (`MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one`). -/
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
/-- For a linear map $A$ on $\mathbb{R}^\iota$, a vector $c$ and any set $T$, the Lebesgue measure
of the image of $T$ under $y \mapsto Ay + c$ is $|\det A|$ times the measure of $T$. -/
theorem volume_affineImage (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ι → ℝ) (T : Set (ι → ℝ)) :
    volume ((fun y => A y + c) '' T) = ENNReal.ofReal |LinearMap.det A| * volume T := by
  have e : (fun y => A y + c) '' T = (fun y => y + c) '' (A '' T) := by
    rw [image_image]
  rw [e, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_image_linearMap]

end Affine

/-! ### The reference triangle -/

/-- The **reference triangle** $\hat T = \{(x, y) : x \ge 0,\ y \ge 0,\ x + y \le 1\}$, with
vertices $(0, 0)$, $(1, 0)$ and $(0, 1)$, as a subset of `Fin 2 → ℝ`.

This is the reference triangle of §9.9.2 of [quarteroni2000numerical]. The point $(x, y)$ is the
function `![x, y]`. -/
def refTriangle : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

/-- The reference triangle $\hat T$ as a subset of `ℝ × ℝ`, where Fubini's theorem is stated. -/
def refTriangle' : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

/-- The reference triangle `Quadrature.refTriangle` is the preimage of its copy
`Quadrature.refTriangle'` in `ℝ × ℝ` under the identification `MeasurableEquiv.finTwoArrow`. -/
theorem refTriangle_eq_preimage :
    refTriangle = MeasurableEquiv.finTwoArrow ⁻¹' refTriangle' := by
  ext x
  simp [refTriangle, refTriangle', MeasurableEquiv.finTwoArrow]

/-- The copy of the reference triangle in `ℝ × ℝ` is compact. -/
theorem isCompact_refTriangle' : IsCompact refTriangle' := by
  refine (isCompact_Icc (a := ((0 : ℝ), (0 : ℝ))) (b := (1, 1))).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    exact ⟨⟨hx, hy⟩, ⟨by simp only at *; linarith, by simp only at *; linarith⟩⟩

/-- The copy of the reference triangle in `ℝ × ℝ` is measurable. -/
theorem measurableSet_refTriangle' : MeasurableSet refTriangle' :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))

/-- The reference triangle $\hat T$ is measurable. -/
theorem measurableSet_refTriangle : MeasurableSet refTriangle := by
  rw [refTriangle_eq_preimage]
  exact MeasurableEquiv.finTwoArrow.measurable measurableSet_refTriangle'

/-- The reference triangle $\hat T$ is compact, because it is a closed subset of the unit square. -/
theorem isCompact_refTriangle : IsCompact refTriangle := by
  refine (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := 1)).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const (continuous_apply 0)).inter
      ((isClosed_le continuous_const (continuous_apply 1)).inter
        (isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const))
  · rintro x ⟨h0, h1, h01⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith

/-- For $g : \mathbb{R}^2 \to \mathbb{R}$ and $x \in \mathbb{R}$, the restriction of the indicator
$1_{\hat T}\, g$ to the vertical line through $x$ is the function
$y \mapsto 1_{[0, 1 - x]}(y)\, g(x, y)$ if $x \in [0, 1]$, and the zero function otherwise. -/
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

/-- **Dirichlet's integral** on the copy of the reference triangle in `ℝ × ℝ`: for natural numbers
$a$ and $b$,
$$\int_{\hat T} x^a y^b \, d(x, y) = \frac{a!\, b!}{(a + b + 2)!}.$$
Fubini's theorem reduces the integral to the Beta integral
$\int_0^1 x^a (1 - x)^{b+1} / (b + 1)\, dx$. -/
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

/-- The identification `MeasurableEquiv.finTwoArrow` of `Fin 2 → ℝ` with `ℝ × ℝ` preserves Lebesgue
measure. -/
theorem measurePreserving_finTwoArrow_volume :
    MeasurePreserving (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) volume volume :=
  measurePreserving_finTwoArrow (volume : Measure ℝ)

/-- **Dirichlet's integral on the reference triangle.** For natural numbers $a$ and $b$,
$$\int_{\hat T} x^a y^b \, d(x, y) = \frac{a!\, b!}{(a + b + 2)!}.$$

The point $(x, y)$ is `![x 0, x 1]`. The proof transports
`Quadrature.integral_refTriangle'_pow_mul_pow` along `MeasurableEquiv.finTwoArrow`. -/
theorem integral_refTriangle_pow_mul_pow (a b : ℕ) :
    ∫ x in refTriangle, x 0 ^ a * x 1 ^ b = (a ! * b ! : ℝ) / (a + b + 2)! := by
  rw [refTriangle_eq_preimage, ← integral_refTriangle'_pow_mul_pow]
  exact measurePreserving_finTwoArrow_volume.setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b)
    refTriangle'

/-- The area of the reference triangle $\hat T$ is $1/2$. -/
theorem volume_refTriangle : volume refTriangle = ENNReal.ofReal (1 / 2) := by
  have h := integral_refTriangle_pow_mul_pow 0 0
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, zero_add,
    setIntegral_const, smul_eq_mul] at h
  rw [← ENNReal.ofReal_toReal (isCompact_refTriangle.measure_lt_top).ne, ← measureReal_def, h]
  norm_num [Nat.factorial]

/-- **The area of a triangle.** Let $A$ be a linear map on $\mathbb{R}^2$, let $c \in \mathbb{R}^2$,
and let $F(y) = Ay + c$. The area of $F(\hat T)$ is $|\det A| / 2$.

Hence, when $A$ is injective, the Jacobian of the map from the reference triangle onto
$T = F(\hat T)$ is $|\det A| = 2|T|$. -/
theorem volume_affineImage_refTriangle (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (c : Fin 2 → ℝ) :
    volume ((fun y => A y + c) '' refTriangle) = ENNReal.ofReal (|LinearMap.det A| / 2) := by
  rw [volume_affineImage, volume_refTriangle, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-! ### The rules of the source -/

/-- **Exactness on the reference triangle is a finite system of equations.** Let $w_k$ be weights
and $x_k = (\xi_k, \eta_k) \in \mathbb{R}^2$ be nodes, indexed by a finite set. The rule is
exact to degree $m$ on $\hat T$ if and only if
$$\sum_k w_k\, \xi_k^a \eta_k^b = \frac{a!\, b!}{(a + b + 2)!} \quad \text{for all natural
  numbers } a, b \text{ with } a + b \le m.$$

This is Definition 9.1 of [quarteroni2000numerical], tested on the monomials $x^a y^b$. -/
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

/-- **The centroid rule** $|\hat T|\, f(1/3, 1/3)$, with the single weight $1/2$ at the centroid, is
exact to degree $1$ on $\hat T$.

This is formula (9.58) of [quarteroni2000numerical] on the reference triangle. -/
theorem isExactOn_centroid :
    Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 1 => (1 / 2 : ℝ))
      (fun _ => ![1 / 3, 1 / 3]) 1 := by
  rw [isExactOn_refTriangle_iff]
  intro a b hab
  have ha : a ≤ 1 := by omega
  have hb : b ≤ 1 := by omega
  interval_cases a <;> interval_cases b <;>
    first | omega | norm_num [Fin.sum_univ_succ, Nat.factorial]

/-- The centroid rule $|\hat T|\, f(1/3, 1/3)$ is not exact to degree $2$ on $\hat T$.

On $x^2$ the rule gives $1/18$, and the integral is $1/12$. -/
theorem not_isExactOn_centroid_two :
    ¬ Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 1 => (1 / 2 : ℝ))
      (fun _ => ![1 / 3, 1 / 3]) 2 := by
  rw [isExactOn_refTriangle_iff]
  intro h
  have := h 2 0 le_rfl
  norm_num [Fin.sum_univ_succ, Nat.factorial] at this

/-- **The vertex rule** $(|\hat T| / 3) \sum_j f(a_j)$, with the weight $1/6$ at each of the
vertices $a_j = (0, 0)$, $(1, 0)$, $(0, 1)$, is exact to degree $1$ on $\hat T$.

This is the trapezoidal formula (9.59) of [quarteroni2000numerical] on the reference triangle. -/
theorem isExactOn_vertex :
    Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 3 => (1 / 6 : ℝ))
      ![![0, 0], ![1, 0], ![0, 1]] 1 := by
  rw [isExactOn_refTriangle_iff]
  intro a b hab
  have ha : a ≤ 1 := by omega
  have hb : b ≤ 1 := by omega
  interval_cases a <;> interval_cases b <;>
    first | omega | norm_num [Fin.sum_univ_succ, Nat.factorial]

/-- The vertex rule $(|\hat T| / 3) \sum_j f(a_j)$ is not exact to degree $2$ on $\hat T$.

On $x^2$ the rule gives $1/6$, and the integral is $1/12$. -/
theorem not_isExactOn_vertex_two :
    ¬ Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 3 => (1 / 6 : ℝ))
      ![![0, 0], ![1, 0], ![0, 1]] 2 := by
  rw [isExactOn_refTriangle_iff]
  intro h
  have := h 2 0 le_rfl
  norm_num [Fin.sum_univ_succ, Nat.factorial] at this

/-- **The edge-midpoint rule** $(|\hat T| / 3) \sum_j f(m_j)$, with the weight $1/6$ at each of the
edge midpoints $m_j = (1/2, 0)$, $(0, 1/2)$, $(1/2, 1/2)$, is exact to degree $2$ on $\hat T$.

This is the first symmetric formula $I_3$ of §9.9.2 of [quarteroni2000numerical]. -/
theorem isExactOn_edgeMidpoint :
    Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 3 => (1 / 6 : ℝ))
      ![![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2]] 2 := by
  rw [isExactOn_refTriangle_iff]
  intro a b hab
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;>
    first | omega | norm_num [Fin.sum_univ_succ, Nat.factorial]

/-- The edge-midpoint rule $(|\hat T| / 3) \sum_j f(m_j)$ is not exact to degree $3$ on $\hat T$.

On $x^3$ the rule gives $1/24$, and the integral is $1/20$. -/
theorem not_isExactOn_edgeMidpoint_three :
    ¬ Approximation.IsExactOn (volume.restrict refTriangle) (fun _ : Fin 3 => (1 / 6 : ℝ))
      ![![1 / 2, 0], ![0, 1 / 2], ![1 / 2, 1 / 2]] 3 := by
  rw [isExactOn_refTriangle_iff]
  intro h
  have := h 3 0 le_rfl
  norm_num [Fin.sum_univ_succ, Nat.factorial] at this

/-- **The seven-point rule**
$$\frac{|\hat T|}{60} \Bigl(3 \sum_j f(a_j) + 8 \sum_j f(m_j) + 27 f(1/3, 1/3)\Bigr),$$
with the weight $1/40$ at each vertex $a_j$, the weight $1/15$ at each edge midpoint $m_j$ and
the weight $9/40$ at the centroid, is exact to degree $3$ on $\hat T$.

This is the second symmetric formula $I_7$ of §9.9.2 of [quarteroni2000numerical]. -/
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

/-- The seven-point rule is not exact to degree $4$ on $\hat T$.

On $x^4$ the rule gives $13/360$, and the integral is $1/30$. -/
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
