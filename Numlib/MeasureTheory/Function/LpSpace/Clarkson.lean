/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpSpace.Clarkson` for the `L^p` statements and the
instance (`Mathlib.Analysis.Convex.Uniform` lists Hanner's inequalities as a to-do), and
`Mathlib.Analysis.MeanInequalitiesPow` for the pointwise inequalities on `ℝ`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Numlib.MeasureTheory.Function.LpInterpolation
import Numlib.MeasureTheory.Function.LpSpace.Convergence

/-!
# Clarkson's inequalities and the uniform convexity of `L^p`

For `1 < p < ∞` the space `L^p(μ)` of real-valued functions is uniformly convex
(`MeasureTheory.Lp.instUniformConvexSpace`). The proof is by **Clarkson's inequalities**:

* for `2 ≤ p < ∞`, the first inequality
  `‖(f + g)/2‖ₚ ^ p + ‖(f - g)/2‖ₚ ^ p ≤ (‖f‖ₚ ^ p + ‖g‖ₚ ^ p) / 2`
  (`MeasureTheory.Lp.clarkson_of_two_le`), integrated from the pointwise inequality
  `|(a + b)/2| ^ p + |(a - b)/2| ^ p ≤ (|a| ^ p + |b| ^ p) / 2`
  (`Real.clarkson_pointwise_of_two_le`), itself a consequence of the comparison
  `α ^ p + β ^ p ≤ (α ^ 2 + β ^ 2) ^ (p/2)` of the `ℓ^p` and `ℓ^2` norms on `ℝ²` and of the
  convexity of `t ↦ t ^ (p/2)`;
* for `1 < p ≤ 2` with conjugate exponent `q`, the second inequality
  `‖f + g‖ₚ ^ q + ‖f - g‖ₚ ^ q ≤ 2 (‖f‖ₚ ^ p + ‖g‖ₚ ^ p) ^ (q/p)`
  (`MeasureTheory.Lp.clarkson_of_le_two`), obtained from the pointwise inequality
  `|x + y| ^ q + |x - y| ^ q ≤ 2 (|x| ^ p + |y| ^ p) ^ (q/p)`
  (`Real.abs_add_rpow_add_abs_sub_rpow_le`, stated with the roles of `p` and `q` exchanged, so
  for an exponent `≥ 2` and its conjugate) raised to the power `p/q ≤ 1`, integrated, and combined
  with the *reverse* Minkowski inequality for the exponent `p/q ∈ (0, 1]`
  (`ENNReal.Lp_add_le_lintegral_Lp_add_of_le_one`).

The pointwise inequality behind the second one is the difficult step. By homogeneity and
symmetry it reduces to a one-variable inequality on `[0, 1]`,
`(1 + r) ^ p + (1 - r) ^ p ≤ 2 (1 + r ^ q) ^ (p - 1)` (`Real.one_add_rpow_add_one_sub_rpow_le`,
`2 ≤ p`, `q` conjugate), which is proved as follows: the function
`F x = (1 + x ^ (1/p)) ^ p + (1 - x ^ (1/p)) ^ p` is concave on `(0, 1)`, because its derivative
`F' x = (1 + x ^ (-1/p)) ^ (p-1) - (x ^ (-1/p) - 1) ^ (p-1)` is antitone there, so `F` lies below
its tangent line at any point `y`, `F x ≤ F y + (x - y) F' y`; at `x = r ^ p` and the tangent
point `y = r ^ (p q)` the right-hand side collapses to `2 (1 + r ^ q) ^ (p - 1)`, because
`p / q = p - 1` for conjugate exponents. This is the argument of [brezis2011functional]
Problem 20, part A. The one-variable inequality in the book's form,
`(1 + x ^ (1/p)) ^ p + (1 - x ^ (1/p)) ^ p ≤ 2 (1 + x ^ (q/p)) ^ (p/q)` on `(0, 1)`, is
`Real.clarkson_one_var_le`.

The inequalities of the book's Problem 20, part B — for `2 ≤ p`,
`‖f + g‖ₚ ^ p + ‖f - g‖ₚ ^ p ≤ 2 (‖f‖ₚ ^ q + ‖g‖ₚ ^ q) ^ (p/q) ≤ 2 ^ (p-1) (‖f‖ₚ ^ p + ‖g‖ₚ ^ p)` —
are `MeasureTheory.Lp.norm_add_rpow_add_norm_sub_rpow_le` and
`MeasureTheory.Lp.two_mul_norm_rpow_add_norm_rpow_le`; together they give the first inequality
again.

## Implementation notes

The integrated inequalities are first proved at the level of `eLpNorm` for measurable functions
(`MeasureTheory.eLpNorm_add_rpow_add_eLpNorm_sub_rpow_le_of_two_le` and
`MeasureTheory.eLpNorm_add_rpow_add_eLpNorm_sub_rpow_le_of_le_two`), where the exponent
bookkeeping is done once in `ℝ≥0∞`, and then read on `Lp ℝ p μ` through
`‖f‖ ^ r = (eLpNorm f p μ ^ r).toReal`. The uniform convexity instance is stated with the
hypotheses `[Fact (1 < p)] [Fact (p ≠ ∞)]`; the theorem form
`MeasureTheory.Lp.uniformConvexSpace_of_one_lt_of_ne_top` takes them as explicit arguments.

The first inequality and its proof would go through verbatim for functions with values in an
inner product space (the only input is the parallelogram law); the second is genuinely about
real scalars, which is why everything is stated for `Lp ℝ p μ`.

## References

Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Universitext, Springer, 2011 [brezis2011functional], Theorem 4.10 (Clarkson's first inequality
and uniform convexity for `2 ≤ p`), Remark 3 of chapter 4 (the second inequality), Problem 20
(its proof), Exercise 4.11 (the reverse Minkowski inequality).
-/

open Filter Set Topology MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-! ### Pointwise inequalities on `ℝ` -/

namespace Real

/-- Comparison of the `ℓ^p` and `ℓ^2` norms on `ℝ²`: for `2 ≤ p`,
`α ^ p + β ^ p ≤ (α ^ 2 + β ^ 2) ^ (p / 2)` ([brezis2011functional] Theorem 4.10, inequality
(10)). This is `NNReal.rpow_add_rpow_le` at the exponents `2 ≤ p`, raised to the power `p`. -/
theorem rpow_add_rpow_le_rpow_sq_add_sq {α β p : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 2 ≤ p) :
    α ^ p + β ^ p ≤ (α ^ 2 + β ^ 2) ^ (p / 2) := by
  have hp0 : (0:ℝ) < p := by linarith
  lift α to ℝ≥0 using hα
  lift β to ℝ≥0 using hβ
  have h := NNReal.rpow_le_rpow (NNReal.rpow_add_rpow_le α β (by norm_num : (0:ℝ) < 2) hp) hp0.le
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul, one_div_mul_cancel hp0.ne', NNReal.rpow_one,
    show (1 / 2 : ℝ) * p = p / 2 by ring] at h
  have h2 : ∀ x : ℝ≥0, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [← NNReal.rpow_natCast]; norm_num
  rw [h2, h2] at h
  exact_mod_cast h

/-- **Clarkson's first inequality** on `ℝ`: for `2 ≤ p`,
`|(a + b) / 2| ^ p + |(a - b) / 2| ^ p ≤ (|a| ^ p + |b| ^ p) / 2` ([brezis2011functional]
Theorem 4.10, inequality (9)). It is `Real.rpow_add_rpow_le_rpow_sq_add_sq` followed by the
convexity of `t ↦ t ^ (p / 2)`. -/
theorem clarkson_pointwise_of_two_le {p : ℝ} (hp : 2 ≤ p) (a b : ℝ) :
    |(a + b) / 2| ^ p + |(a - b) / 2| ^ p ≤ (|a| ^ p + |b| ^ p) / 2 := by
  have hp0 : (0:ℝ) < p := by linarith
  have h1 : (1:ℝ) ≤ p / 2 := by linarith
  have hsq : |(a + b) / 2| ^ 2 + |(a - b) / 2| ^ 2 = (1 / 2) * a ^ 2 + (1 / 2) * b ^ 2 := by
    rw [sq_abs, sq_abs]; ring
  have habs : ∀ x : ℝ, (x ^ 2) ^ (p / 2) = |x| ^ p := fun x => by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    push_cast
    ring
  calc |(a + b) / 2| ^ p + |(a - b) / 2| ^ p
      ≤ (|(a + b) / 2| ^ 2 + |(a - b) / 2| ^ 2) ^ (p / 2) :=
        rpow_add_rpow_le_rpow_sq_add_sq (abs_nonneg _) (abs_nonneg _) hp
    _ = ((1 / 2) * a ^ 2 + (1 / 2) * b ^ 2) ^ (p / 2) := by rw [hsq]
    _ ≤ (1 / 2) * (a ^ 2) ^ (p / 2) + (1 / 2) * (b ^ 2) ^ (p / 2) :=
        (convexOn_rpow h1).2 (sq_nonneg a) (sq_nonneg b) (by norm_num) (by norm_num) (by norm_num)
    _ = (|a| ^ p + |b| ^ p) / 2 := by rw [habs, habs]; ring

/-- [brezis2011functional] Problem 20, inequality (2): for `2 ≤ p` with conjugate exponent `q`,
`2 (|x| ^ q + |y| ^ q) ^ (p / q) ≤ 2 ^ (p - 1) (|x| ^ p + |y| ^ p)`, by the convexity of
`t ↦ t ^ (p / q)` (`p / q = p - 1 ≥ 1`). -/
theorem two_mul_rpow_add_rpow_le {p q : ℝ} (hp : 2 ≤ p) (hpq : p.HolderConjugate q) (x y : ℝ) :
    2 * (|x| ^ q + |y| ^ q) ^ (p / q) ≤ 2 ^ (p - 1) * (|x| ^ p + |y| ^ p) := by
  have hq0 : 0 < q := hpq.symm.pos
  have hpq' : p / q = p - 1 := hpq.div_conj_eq_sub_one
  have h1 : (1:ℝ) ≤ p / q := by rw [hpq']; linarith
  have habs : ∀ z : ℝ, (|z| ^ q) ^ (p / q) = |z| ^ p := fun z => by
    rw [← Real.rpow_mul (abs_nonneg z), mul_div_cancel₀ _ hq0.ne']
  have hconv := (convexOn_rpow h1).2 (Real.rpow_nonneg (abs_nonneg x) q)
    (Real.rpow_nonneg (abs_nonneg y) q) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul, habs] at hconv
  have hsplit : (|x| ^ q + |y| ^ q) ^ (p / q)
      = 2 ^ (p / q) * (1 / 2 * |x| ^ q + 1 / 2 * |y| ^ q) ^ (p / q) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    ring
  rw [hsplit, ← hpq']
  have h2pos : (0:ℝ) < 2 ^ (p / q) := by positivity
  calc 2 * (2 ^ (p / q) * (1 / 2 * |x| ^ q + 1 / 2 * |y| ^ q) ^ (p / q))
      ≤ 2 * (2 ^ (p / q) * (1 / 2 * |x| ^ p + 1 / 2 * |y| ^ p)) := by gcongr
    _ = 2 ^ (p / q) * (|x| ^ p + |y| ^ p) := by ring

/-! ### The one-variable inequality of Problem 20 -/

/-- A function with an antitone derivative lies below its tangent lines: if
`HasDerivAt F (F' x) x` on `Ioo a b` and `F'` is antitone there, then
`F x ≤ F y + (x - y) * F' y` for `x, y ∈ Ioo a b`. This is the mean value theorem. -/
theorem le_add_mul_of_antitoneOn_hasDerivAt {F F' : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Ioo a b, HasDerivAt F (F' x) x) (hF' : AntitoneOn F' (Ioo a b))
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : F x ≤ F y + (x - y) * F' y := by
  have hcont : ∀ s t, s ∈ Ioo a b → t ∈ Ioo a b → ContinuousOn F (Icc s t) := fun s t hs ht =>
    fun z hz => (hF z ⟨hs.1.trans_le hz.1, hz.2.trans_lt ht.2⟩).continuousAt.continuousWithinAt
  have hderiv : ∀ s t, s ∈ Ioo a b → t ∈ Ioo a b → ∀ z ∈ Ioo s t, HasDerivAt F (F' z) z :=
    fun s t hs ht z hz => hF z ⟨hs.1.trans hz.1, hz.2.trans ht.2⟩
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope F F' hxy (hcont x y hx hy) (hderiv x y hx hy)
    have hcm : c ∈ Ioo a b := ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
    have hle : F' y ≤ F' c := hF' hcm hy hc.2.le
    rw [hc', le_div_iff₀ (sub_pos.2 hxy)] at hle
    nlinarith
  · simp
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope F F' hyx (hcont y x hy hx) (hderiv y x hy hx)
    have hcm : c ∈ Ioo a b := ⟨hy.1.trans hc.1, hc.2.trans hx.2⟩
    have hle : F' c ≤ F' y := hF' hy hcm hc.1.le
    rw [hc', div_le_iff₀ (sub_pos.2 hyx)] at hle
    nlinarith

/-- The auxiliary function `v ↦ (1 + v) ^ (p - 1) - (v - 1) ^ (p - 1)` is monotone on `[1, ∞)`
when `2 ≤ p`: its derivative `(p - 1) ((1 + v) ^ (p - 2) - (v - 1) ^ (p - 2))` is nonnegative. -/
theorem monotoneOn_one_add_rpow_sub_sub_one_rpow {p : ℝ} (hp : 2 ≤ p) :
    MonotoneOn (fun v : ℝ => (1 + v) ^ (p - 1) - (v - 1) ^ (p - 1)) (Ici 1) := by
  have h1 : (1:ℝ) ≤ p - 1 := by linarith
  have hderiv : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (1 + v) ^ (p - 1) - (v - 1) ^ (p - 1))
      (1 * (p - 1) * (1 + v) ^ (p - 1 - 1) - 1 * (p - 1) * (v - 1) ^ (p - 1 - 1)) v := fun v =>
    (((hasDerivAt_id v).const_add 1).rpow_const (Or.inr h1)).sub
      (((hasDerivAt_id v).sub_const 1).rpow_const (Or.inr h1))
  refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
    (fun v _ => (hderiv v).continuousAt.continuousWithinAt)
    (fun v _ => (hderiv v).differentiableAt.differentiableWithinAt) fun v hv => ?_
  rw [interior_Ici, mem_Ioi] at hv
  rw [(hderiv v).deriv]
  have : (v - 1) ^ (p - 1 - 1) ≤ (1 + v) ^ (p - 1 - 1) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  nlinarith

/-- The derivative of `F x = (1 + x ^ (1/p)) ^ p + (1 - x ^ (1/p)) ^ p` on `(0, 1)`, in the form
`(1 + x ^ (-1/p)) ^ (p - 1) - (x ^ (-1/p) - 1) ^ (p - 1)` which makes its antitonicity visible. -/
theorem hasDerivAt_one_add_rpow_add_one_sub_rpow {p : ℝ} (hp : 2 ≤ p) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun x : ℝ => (1 + x ^ (1 / p)) ^ p + (1 - x ^ (1 / p)) ^ p)
      ((1 + x ^ (-(1 / p))) ^ (p - 1) - (x ^ (-(1 / p)) - 1) ^ (p - 1)) x := by
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : (1:ℝ) ≤ p := by linarith
  obtain ⟨hx0, hx1⟩ := hx
  set u : ℝ := x ^ (1 / p) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hx0 _
  have hu1 : u < 1 := Real.rpow_lt_one hx0.le hx1 (by positivity)
  have hdu : HasDerivAt (fun x : ℝ => x ^ (1 / p)) (1 / p * x ^ (1 / p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
  have h := ((hdu.const_add 1).rpow_const (Or.inr hp1)).add
    ((hdu.const_sub 1).rpow_const (Or.inr hp1))
  refine h.congr_deriv ?_
  -- the algebra: `x ^ (1/p - 1) = u⁻¹ ^ (p - 1) / ... `
  have hw : x ^ (1 / p - 1) = (u ^ (p - 1))⁻¹ := by
    rw [hu, ← Real.rpow_mul hx0.le, ← Real.rpow_neg hx0.le]
    congr 1
    field_simp
    ring
  have hxinv : x ^ (-(1 / p)) = u⁻¹ := by rw [Real.rpow_neg hx0.le]
  have hA : (u ^ (p - 1))⁻¹ * (1 + u) ^ (p - 1) = (1 + u⁻¹) ^ (p - 1) := by
    rw [← Real.inv_rpow hu0.le, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hB : (u ^ (p - 1))⁻¹ * (1 - u) ^ (p - 1) = (u⁻¹ - 1) ^ (p - 1) := by
    rw [← Real.inv_rpow hu0.le, ← Real.mul_rpow (by positivity) (by linarith)]
    congr 1
    field_simp
  rw [hxinv, ← hA, ← hB, hw]
  field_simp
  ring

/-- The derivative of `F` is antitone on `(0, 1)`, so `F` is concave there. -/
theorem antitoneOn_deriv_one_add_rpow_add_one_sub_rpow {p : ℝ} (hp : 2 ≤ p) :
    AntitoneOn (fun x : ℝ => (1 + x ^ (-(1 / p))) ^ (p - 1) - (x ^ (-(1 / p)) - 1) ^ (p - 1))
      (Ioo 0 1) := by
  intro x hx y hy hxy
  have hp0 : (0:ℝ) < p := by linarith
  have hneg : -(1 / p) ≤ 0 := by rw [neg_nonpos]; positivity
  have h1 : ∀ z ∈ Ioo (0:ℝ) 1, 1 ≤ z ^ (-(1 / p)) := fun z hz =>
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz.1 hz.2.le hneg
  exact monotoneOn_one_add_rpow_sub_sub_one_rpow hp (h1 y hy) (h1 x hx)
    (Real.rpow_le_rpow_of_nonpos hx.1 hxy hneg)

/-- **The one-variable inequality of Clarkson's second inequality** ([brezis2011functional]
Problem 20, part A, questions 2–3, in the variable `r ∈ [0, 1]`): for `2 ≤ p` with conjugate
exponent `q`, `(1 + r) ^ p + (1 - r) ^ p ≤ 2 (1 + r ^ q) ^ (p - 1)`.

The function `F x = (1 + x ^ (1/p)) ^ p + (1 - x ^ (1/p)) ^ p` is concave on `(0, 1)`, hence lies
below its tangent line at `y = r ^ (p q)`; evaluated at `x = r ^ p` the tangent line is
`2 (1 + r ^ q) ^ (p - 1)`, because `p / q = p - 1`. -/
theorem one_add_rpow_add_one_sub_rpow_le {p q : ℝ} (hp : 2 ≤ p) (hpq : p.HolderConjugate q)
    {r : ℝ} (hr : r ∈ Icc 0 1) : (1 + r) ^ p + (1 - r) ^ p ≤ 2 * (1 + r ^ q) ^ (p - 1) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hq0 : (0:ℝ) < q := hpq.symm.pos
  have hpq' : p / q = p - 1 := hpq.div_conj_eq_sub_one
  have hp1 : (0:ℝ) < p - 1 := by linarith
  rcases hr.1.eq_or_lt with rfl | hr0
  · simp [Real.zero_rpow hq0.ne']
    norm_num
  rcases hr.2.eq_or_lt with rfl | hr1
  · have h2 : (2:ℝ) ^ (p - 1) = 2 ^ p / 2 := Real.rpow_sub_one two_ne_zero p
    rw [sub_self, Real.zero_rpow hp0.ne', add_zero, Real.one_rpow, one_add_one_eq_two, h2]
    linarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) p]
  -- the tangent-line inequality at `x = r ^ p`, `y = r ^ (p * q) = s ^ p` with `s = r ^ q`
  set s : ℝ := r ^ q with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hr0 _
  have hs1 : s < 1 := Real.rpow_lt_one hr0.le hr1 hq0
  set x : ℝ := r ^ p with hx
  set y : ℝ := s ^ p with hy
  have hxm : x ∈ Ioo 0 1 := ⟨Real.rpow_pos_of_pos hr0 _, Real.rpow_lt_one hr0.le hr1 hp0⟩
  have hym : y ∈ Ioo 0 1 := ⟨Real.rpow_pos_of_pos hs0 _, Real.rpow_lt_one hs0.le hs1 hp0⟩
  have htan := le_add_mul_of_antitoneOn_hasDerivAt
    (fun z hz => hasDerivAt_one_add_rpow_add_one_sub_rpow hp hz)
    (antitoneOn_deriv_one_add_rpow_add_one_sub_rpow hp) hxm hym
  -- evaluate the pieces
  have hxr : x ^ (1 / p) = r := by
    rw [hx, ← Real.rpow_mul hr0.le, mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hys : y ^ (1 / p) = s := by
    rw [hy, ← Real.rpow_mul hs0.le, mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hyinv : y ^ (-(1 / p)) = s⁻¹ := by
    rw [Real.rpow_neg hym.1.le, hys]
  have hxs : x = s ^ (p - 1) := by
    rw [hx, hs, ← Real.rpow_mul hr0.le, ← hpq', mul_div_cancel₀ _ hq0.ne']
  have hys' : y = s ^ (p - 1) * s := by
    rw [hy, ← Real.rpow_add_one hs0.ne', sub_add_cancel]
  set A : ℝ := (1 + s) ^ (p - 1) with hA
  set B : ℝ := (1 - s) ^ (p - 1) with hB
  set S : ℝ := s ^ (p - 1) with hS
  have hA' : (1 + s) ^ p = A * (1 + s) := by
    rw [hA, Real.rpow_sub_one (by positivity) p, div_mul_cancel₀ _ (by positivity)]
  have hB' : (1 - s) ^ p = B * (1 - s) := by
    rw [hB, Real.rpow_sub_one (by linarith) p, div_mul_cancel₀ _ (by linarith)]
  have hSA : S * (1 + s⁻¹) ^ (p - 1) = A := by
    rw [hS, hA, ← Real.mul_rpow hs0.le (by positivity), mul_add, mul_one,
      mul_inv_cancel₀ hs0.ne', add_comm]
  have hSB : S * (s⁻¹ - 1) ^ (p - 1) = B := by
    rw [hS, hB, ← Real.mul_rpow hs0.le (by rw [sub_nonneg]; exact one_le_inv_iff₀.2 ⟨hs0, hs1.le⟩),
      mul_sub, mul_inv_cancel₀ hs0.ne', mul_one]
  simp only [hxr, hys, hyinv] at htan
  rw [hA', hB', hxs, hys'] at htan
  -- `htan : (1 + r) ^ p + (1 - r) ^ p ≤ A (1 + s) + B (1 - s) + (S - S s) (C - D)` with
  -- `S C = A`, `S D = B`
  calc (1 + r) ^ p + (1 - r) ^ p
      ≤ A * (1 + s) + B * (1 - s) + (S - S * s) * ((1 + s⁻¹) ^ (p - 1) - (s⁻¹ - 1) ^ (p - 1)) :=
        htan
    _ = A * (1 + s) + B * (1 - s)
          + (1 - s) * (S * (1 + s⁻¹) ^ (p - 1) - S * (s⁻¹ - 1) ^ (p - 1)) := by
        ring
    _ = 2 * A := by rw [hSA, hSB]; ring

/-- [brezis2011functional] Problem 20, part A, questions 2–3, in the book's form: for `2 ≤ p`
with conjugate exponent `q` and `x ∈ (0, 1)`,
`(1 + x ^ (1/p)) ^ p + (1 - x ^ (1/p)) ^ p ≤ 2 (1 + x ^ (q/p)) ^ (p/q)`. This is
`Real.one_add_rpow_add_one_sub_rpow_le` at `r = x ^ (1/p)`. -/
theorem clarkson_one_var_le {p q : ℝ} (hp : 2 ≤ p) (hpq : p.HolderConjugate q) {x : ℝ}
    (hx : x ∈ Ioo 0 1) :
    (1 + x ^ (1 / p)) ^ p + (1 - x ^ (1 / p)) ^ p ≤ 2 * (1 + x ^ (q / p)) ^ (p / q) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hr : x ^ (1 / p) ∈ Icc (0:ℝ) 1 :=
    ⟨Real.rpow_nonneg hx.1.le _, (Real.rpow_lt_one hx.1.le hx.2 (by positivity)).le⟩
  have h := one_add_rpow_add_one_sub_rpow_le hp hpq hr
  rwa [← Real.rpow_mul hx.1.le, one_div_mul_eq_div, ← hpq.div_conj_eq_sub_one] at h

/-- [brezis2011functional] Problem 20, inequality (1): for `2 ≤ p` with conjugate exponent `q`,
`|x + y| ^ p + |x - y| ^ p ≤ 2 (|x| ^ q + |y| ^ q) ^ (p / q)` for all real `x`, `y`. By symmetry
and homogeneity this is `Real.one_add_rpow_add_one_sub_rpow_le`. -/
theorem abs_add_rpow_add_abs_sub_rpow_le {p q : ℝ} (hp : 2 ≤ p) (hpq : p.HolderConjugate q)
    (x y : ℝ) : |x + y| ^ p + |x - y| ^ p ≤ 2 * (|x| ^ q + |y| ^ q) ^ (p / q) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hq0 : (0:ℝ) < q := hpq.symm.pos
  have hpq' : p / q = p - 1 := hpq.div_conj_eq_sub_one
  -- reduce to `0 ≤ y ≤ x`
  wlog hxy : |y| ≤ |x| generalizing x y
  · have h := this y x (le_of_not_ge hxy)
    rwa [add_comm y x, abs_sub_comm, add_comm (|y| ^ q)] at h
  wlog hx : 0 ≤ x generalizing x y
  · have h := this (-x) (-y) (by simpa using hxy) (by linarith)
    rwa [← neg_add, abs_neg, neg_sub_neg, abs_sub_comm, abs_neg, abs_neg] at h
  wlog hy : 0 ≤ y generalizing y
  · have h := this (-y) (by simpa using hxy) (by linarith)
    rwa [← sub_eq_add_neg, sub_neg_eq_add, abs_neg, add_comm (|x - y| ^ p)] at h
  rw [abs_of_nonneg hx, abs_of_nonneg hy] at *
  rw [abs_of_nonneg (by linarith : 0 ≤ x + y), abs_of_nonneg (by linarith : 0 ≤ x - y)]
  rcases hx.eq_or_lt with rfl | hx0
  · have hy0 : y = 0 := le_antisymm hxy hy
    subst hy0
    simp [Real.zero_rpow hp0.ne', Real.zero_rpow hq0.ne',
      Real.zero_rpow (by positivity : p / q ≠ 0)]
  -- the core inequality at `r = y / x`, multiplied by `x ^ p`
  have hr : y / x ∈ Icc (0:ℝ) 1 := ⟨by positivity, (div_le_one hx0).2 hxy⟩
  have h := one_add_rpow_add_one_sub_rpow_le hp hpq hr
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx0 _
  have hxpq : x ^ p = (x ^ q) ^ (p / q) := by
    rw [← Real.rpow_mul hx0.le, mul_div_cancel₀ _ hq0.ne']
  calc (x + y) ^ p + (x - y) ^ p
      = x ^ p * ((1 + y / x) ^ p + (1 - y / x) ^ p) := by
        rw [mul_add, ← Real.mul_rpow hx0.le (by positivity),
          ← Real.mul_rpow hx0.le (by rw [sub_nonneg]; exact hr.2), mul_add, mul_sub,
          mul_div_cancel₀ _ hx0.ne', mul_one]
    _ ≤ x ^ p * (2 * (1 + (y / x) ^ q) ^ (p - 1)) := by gcongr
    _ = 2 * (x ^ q + y ^ q) ^ (p / q) := by
        rw [← hpq', hxpq, mul_left_comm, ← Real.mul_rpow (by positivity) (by positivity), mul_add,
          mul_one, ← Real.mul_rpow hx0.le (by positivity), mul_div_cancel₀ _ hx0.ne']

end Real

/-! ### The reverse Minkowski inequality for exponents in `(0, 1]` -/

namespace ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **The reverse Minkowski inequality** for an exponent `0 < s ≤ 1`
([brezis2011functional] Exercise 4.11, question 1): for nonnegative `u`, `v`,
`(∫⁻ u ^ s) ^ (1/s) + (∫⁻ v ^ s) ^ (1/s) ≤ (∫⁻ (u + v) ^ s) ^ (1/s)`. Mathlib's
`ENNReal.lintegral_Lp_add_le` is the case `1 ≤ s` with the inequality the other way round, and
`ENNReal.lintegral_Lp_add_le_of_le_one` is the upper bound with the constant `2 ^ (1/s - 1)`.

With `a = (∫⁻ u ^ s) ^ (1/s)` and `b = (∫⁻ v ^ s) ^ (1/s)` both nonzero and finite, the concavity
of `t ↦ t ^ s` with the weights `a / (a + b)` and `b / (a + b)` gives pointwise
`a/(a+b) (u/a) ^ s + b/(a+b) (v/b) ^ s ≤ ((u + v)/(a + b)) ^ s`; integrating, the left side is
`1`, so `(a + b) ^ s ≤ ∫⁻ (u + v) ^ s`. Only one of the two functions needs to be measurable. -/
theorem Lp_add_le_lintegral_Lp_add_of_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {u v : α → ℝ≥0∞} (hu : AEMeasurable u μ) :
    (∫⁻ x, u x ^ s ∂μ) ^ (1 / s) + (∫⁻ x, v x ^ s ∂μ) ^ (1 / s)
      ≤ (∫⁻ x, (u x + v x) ^ s ∂μ) ^ (1 / s) := by
  have hs' : (0:ℝ) < 1 / s := by positivity
  have h1s : (1:ℝ) ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
  set A := ∫⁻ x, u x ^ s ∂μ with hA
  set B := ∫⁻ x, v x ^ s ∂μ with hB
  set C := ∫⁻ x, (u x + v x) ^ s ∂μ with hC
  have hAC : A ≤ C := lintegral_mono fun x => ENNReal.rpow_le_rpow le_self_add hs0.le
  have hBC : B ≤ C := lintegral_mono fun x => ENNReal.rpow_le_rpow le_add_self hs0.le
  -- the degenerate cases follow from the monotonicity `A, B ≤ C`
  rcases eq_or_ne A 0 with hA0 | hA0
  · rw [hA0, ENNReal.zero_rpow_of_pos hs', zero_add]
    exact ENNReal.rpow_le_rpow hBC hs'.le
  rcases eq_or_ne B 0 with hB0 | hB0
  · rw [hB0, ENNReal.zero_rpow_of_pos hs', add_zero]
    exact ENNReal.rpow_le_rpow hAC hs'.le
  rcases eq_or_ne A ∞ with hAt | hAt
  · have hCt : C = ∞ := top_le_iff.1 (hAt ▸ hAC)
    rw [hCt, ENNReal.top_rpow_of_pos hs']
    exact le_top
  rcases eq_or_ne B ∞ with hBt | hBt
  · have hCt : C = ∞ := top_le_iff.1 (hBt ▸ hBC)
    rw [hCt, ENNReal.top_rpow_of_pos hs']
    exact le_top
  -- the main case
  set a := A ^ (1 / s) with ha
  set b := B ^ (1 / s) with hb
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hAt).ne'
  have hat : a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hs'.le hAt
  have hb0 : b ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hB0) hBt).ne'
  have hbt : b ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hs'.le hBt
  have hab0 : a + b ≠ 0 := by simp [ha0]
  have habt : a + b ≠ ∞ := ENNReal.add_ne_top.2 ⟨hat, hbt⟩
  have has : a ^ s = A := by
    rw [ha, ← ENNReal.rpow_mul, one_div_mul_cancel hs0.ne', ENNReal.rpow_one]
  have hbs : b ^ s = B := by
    rw [hb, ← ENNReal.rpow_mul, one_div_mul_cancel hs0.ne', ENNReal.rpow_one]
  have hw : a / (a + b) + b / (a + b) = 1 := by
    rw [ENNReal.div_add_div_same, ENNReal.div_self hab0 habt]
  -- pointwise concavity of `t ↦ t ^ s`
  have hpt : ∀ x, a / (a + b) * (u x / a) ^ s + b / (a + b) * (v x / b) ^ s
      ≤ ((u x + v x) / (a + b)) ^ s := by
    intro x
    have h := ENNReal.rpow_arith_mean_le_arith_mean2_rpow (a / (a + b)) (b / (a + b))
      ((u x / a) ^ s) ((v x / b) ^ s) hw h1s
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel hs0.ne', ENNReal.rpow_one,
      ENNReal.rpow_one] at h
    have h2 := ENNReal.rpow_le_rpow h hs0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hs0.ne', ENNReal.rpow_one] at h2
    refine h2.trans (le_of_eq ?_)
    congr 1
    simp only [div_eq_mul_inv]
    calc a * (a + b)⁻¹ * (u x * a⁻¹) + b * (a + b)⁻¹ * (v x * b⁻¹)
        = a * a⁻¹ * (u x * (a + b)⁻¹) + b * b⁻¹ * (v x * (a + b)⁻¹) := by ring
      _ = (u x + v x) * (a + b)⁻¹ := by
          rw [ENNReal.mul_inv_cancel ha0 hat, ENNReal.mul_inv_cancel hb0 hbt, one_mul, one_mul,
            add_mul]
  -- the weighted averages integrate to `1`
  have hIa : ∫⁻ x, (u x / a) ^ s ∂μ = 1 := by
    simp_rw [ENNReal.div_rpow_of_nonneg _ _ hs0.le, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (has ▸ hA0)), has, ← div_eq_mul_inv,
      ENNReal.div_self hA0 hAt]
  have hIb : ∫⁻ x, (v x / b) ^ s ∂μ = 1 := by
    simp_rw [ENNReal.div_rpow_of_nonneg _ _ hs0.le, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hbs ▸ hB0)), hbs, ← div_eq_mul_inv,
      ENNReal.div_self hB0 hBt]
  have hint : ∫⁻ x, a / (a + b) * (u x / a) ^ s + b / (a + b) * (v x / b) ^ s ∂μ = 1 := by
    have hua : AEMeasurable (fun x => (u x / a) ^ s) μ := (hu.div_const a).pow_const s
    rw [lintegral_add_left' (hua.const_mul _),
      lintegral_const_mul' _ _ (ENNReal.div_ne_top hat hab0),
      lintegral_const_mul' _ _ (ENNReal.div_ne_top hbt hab0), hIa, hIb, mul_one, mul_one, hw]
  have hne0 : (a + b) ^ s ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hab0) habt).ne'
  have hnet : (a + b) ^ s ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hs0.le habt
  have hmain : 1 ≤ C / (a + b) ^ s := by
    calc (1:ℝ≥0∞) = ∫⁻ x, a / (a + b) * (u x / a) ^ s + b / (a + b) * (v x / b) ^ s ∂μ :=
          hint.symm
      _ ≤ ∫⁻ x, ((u x + v x) / (a + b)) ^ s ∂μ := lintegral_mono hpt
      _ = C / (a + b) ^ s := by
          simp_rw [ENNReal.div_rpow_of_nonneg _ _ hs0.le, div_eq_mul_inv]
          rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hne0)]
  have hpow : (a + b) ^ s ≤ C := by
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet), one_mul] at hmain
  calc a + b = ((a + b) ^ s) ^ (1 / s) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hs0.ne', ENNReal.rpow_one]
    _ ≤ C ^ (1 / s) := ENNReal.rpow_le_rpow hpow hs'.le

end ENNReal

/-! ### Clarkson's inequalities for `eLpNorm` -/

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}

/-- `‖a‖ₑ ^ t = ENNReal.ofReal (|a| ^ t)` for real `a` and `0 ≤ t`. -/
theorem enorm_rpow_eq_ofReal_abs_rpow (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖a‖ₑ ^ t = ENNReal.ofReal (|a| ^ t) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg a) ht]

/-- **Clarkson's first inequality** for `eLpNorm`, `2 ≤ p < ∞`:
`‖(f + g)/2‖ₚ ^ p + ‖(f - g)/2‖ₚ ^ p ≤ (‖f‖ₚ ^ p + ‖g‖ₚ ^ p) / 2`, the integrated form of
`Real.clarkson_pointwise_of_two_le`. -/
theorem eLpNorm_add_rpow_add_eLpNorm_sub_rpow_le_of_two_le (hp : 2 ≤ p) (hp' : p ≠ ∞)
    {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm ((2:ℝ)⁻¹ • (f + g)) p μ ^ p.toReal + eLpNorm ((2:ℝ)⁻¹ • (f - g)) p μ ^ p.toReal
      ≤ (eLpNorm f p μ ^ p.toReal + eLpNorm g p μ ^ p.toReal) / 2 := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans_le hp).ne'
  have hP : (2:ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_ofNat 2]
    exact ENNReal.toReal_mono hp' hp
  have hP0 : (0:ℝ) ≤ p.toReal := ENNReal.toReal_nonneg
  have hfg1 : AEStronglyMeasurable ((2:ℝ)⁻¹ • (f + g)) μ := (hf.add hg).const_smul _
  have hfg2 : AEStronglyMeasurable ((2:ℝ)⁻¹ • (f - g)) μ := (hf.sub hg).const_smul _
  have hpt : ∀ x, ‖(2:ℝ)⁻¹ * (f x + g x)‖ₑ ^ p.toReal + ‖(2:ℝ)⁻¹ * (f x - g x)‖ₑ ^ p.toReal
      ≤ (‖f x‖ₑ ^ p.toReal + ‖g x‖ₑ ^ p.toReal) / 2 := by
    intro x
    rw [enorm_rpow_eq_ofReal_abs_rpow _ hP0, enorm_rpow_eq_ofReal_abs_rpow _ hP0,
      enorm_rpow_eq_ofReal_abs_rpow _ hP0, enorm_rpow_eq_ofReal_abs_rpow _ hP0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_div_of_pos two_pos]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [inv_mul_eq_div] using Real.clarkson_pointwise_of_two_le hP (f x) (g x)
  calc eLpNorm ((2:ℝ)⁻¹ • (f + g)) p μ ^ p.toReal + eLpNorm ((2:ℝ)⁻¹ • (f - g)) p μ ^ p.toReal
      = ∫⁻ x, ‖(2:ℝ)⁻¹ * (f x + g x)‖ₑ ^ p.toReal + ‖(2:ℝ)⁻¹ * (f x - g x)‖ₑ ^ p.toReal ∂μ := by
        rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hfg1,
          ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hfg2,
          ← lintegral_add_left' (hfg1.enorm.pow_const _)]
        rfl
    _ ≤ ∫⁻ x, (‖f x‖ₑ ^ p.toReal + ‖g x‖ₑ ^ p.toReal) / 2 ∂μ := lintegral_mono hpt
    _ = (eLpNorm f p μ ^ p.toReal + eLpNorm g p μ ^ p.toReal) / 2 := by
        simp_rw [div_eq_mul_inv]
        rw [lintegral_mul_const' _ _ (by simp), lintegral_add_left' (hf.enorm.pow_const _),
          ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hf,
          ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hg]

/-- **Clarkson's second inequality** for `eLpNorm`, `1 < p ≤ 2` with conjugate exponent `q`:
`‖f + g‖ₚ ^ q + ‖f - g‖ₚ ^ q ≤ 2 (‖f‖ₚ ^ p + ‖g‖ₚ ^ p) ^ (q/p)`. The pointwise inequality
`Real.abs_add_rpow_add_abs_sub_rpow_le` at the exponent `q ≥ 2` is raised to the power
`p/q ≤ 1` and integrated, and the reverse Minkowski inequality
`ENNReal.Lp_add_le_lintegral_Lp_add_of_le_one` bounds the result from below by
`(‖f + g‖ₚ ^ q + ‖f - g‖ₚ ^ q) ^ (p/q)`. -/
theorem eLpNorm_add_rpow_add_eLpNorm_sub_rpow_le_of_le_two [p.HolderConjugate q] (hp : 1 < p)
    (hp2 : p ≤ 2) {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f + g) p μ ^ q.toReal + eLpNorm (f - g) p μ ^ q.toReal
      ≤ 2 * (eLpNorm f p μ ^ p.toReal + eLpNorm g p μ ^ p.toReal) ^ (q.toReal / p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hp' : p ≠ ∞ := (hp2.trans_lt (by simp)).ne
  have hq' : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp' hq'
  set P := p.toReal with hPdef
  set Q := q.toReal with hQdef
  have hP1 : 1 < P := hPQ.lt
  have hP2 : P ≤ 2 := by
    rw [hPdef, ← ENNReal.toReal_ofNat 2]
    exact ENNReal.toReal_mono (by simp) hp2
  have hQ0 : 0 < Q := hPQ.symm.pos
  have hQ2 : (2:ℝ) ≤ Q := by
    rw [hPQ.conjugate_eq, le_div_iff₀ (by linarith)]
    linarith
  have hQP : Q / P = Q - 1 := hPQ.symm.div_conj_eq_sub_one
  have hs0 : 0 < P / Q := by positivity
  have hs1 : P / Q ≤ 1 := by rw [hPQ.div_conj_eq_sub_one]; linarith
  have hQs : Q * (P / Q) = P := mul_div_cancel₀ _ hQ0.ne'
  have hPs : P * (1 / (P / Q)) = Q := by rw [one_div_div, mul_div_cancel₀ _ (by linarith)]
  have hinv : 1 / (P / Q) = Q / P := one_div_div _ _
  -- the pointwise inequality, raised to the power `P / Q`
  have hpt : ∀ x, (‖f x + g x‖ₑ ^ Q + ‖f x - g x‖ₑ ^ Q) ^ (P / Q)
      ≤ (2:ℝ≥0∞) ^ (P / Q) * (‖f x‖ₑ ^ P + ‖g x‖ₑ ^ P) := by
    intro x
    have h := Real.abs_add_rpow_add_abs_sub_rpow_le hQ2 hPQ.symm (f x) (g x)
    have h2 := Real.rpow_le_rpow (by positivity) h hs0.le
    have hQPs : Q / P * (P / Q) = 1 := by field_simp
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity), hQPs,
      Real.rpow_one] at h2
    rw [enorm_rpow_eq_ofReal_abs_rpow _ hQ0.le, enorm_rpow_eq_ofReal_abs_rpow _ hQ0.le,
      enorm_rpow_eq_ofReal_abs_rpow _ (by linarith), enorm_rpow_eq_ofReal_abs_rpow _ (by linarith),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hs0.le, ← ENNReal.ofReal_ofNat 2,
      ENNReal.ofReal_rpow_of_nonneg (by norm_num) hs0.le,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h2
  -- the reverse Minkowski inequality
  have hU : AEMeasurable (fun x => ‖f x + g x‖ₑ ^ Q) μ := (hf.add hg).enorm.pow_const _
  have hrev := ENNReal.Lp_add_le_lintegral_Lp_add_of_le_one (v := fun x => ‖f x - g x‖ₑ ^ Q)
    hs0 hs1 hU
  have hU' : ∫⁻ x, (‖f x + g x‖ₑ ^ Q) ^ (P / Q) ∂μ = eLpNorm (f + g) p μ ^ P := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' (hf.add hg)]
    simp_rw [← ENNReal.rpow_mul, hQs]
    rfl
  have hV' : ∫⁻ x, (‖f x - g x‖ₑ ^ Q) ^ (P / Q) ∂μ = eLpNorm (f - g) p μ ^ P := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' (hf.sub hg)]
    simp_rw [← ENNReal.rpow_mul, hQs]
    rfl
  rw [hU', hV', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hPs] at hrev
  -- the integrated pointwise inequality
  have hint : ∫⁻ x, (‖f x + g x‖ₑ ^ Q + ‖f x - g x‖ₑ ^ Q) ^ (P / Q) ∂μ
      ≤ (2:ℝ≥0∞) ^ (P / Q) * (eLpNorm f p μ ^ P + eLpNorm g p μ ^ P) := by
    calc ∫⁻ x, (‖f x + g x‖ₑ ^ Q + ‖f x - g x‖ₑ ^ Q) ^ (P / Q) ∂μ
        ≤ ∫⁻ x, (2:ℝ≥0∞) ^ (P / Q) * (‖f x‖ₑ ^ P + ‖g x‖ₑ ^ P) ∂μ := lintegral_mono hpt
      _ = (2:ℝ≥0∞) ^ (P / Q) * (eLpNorm f p μ ^ P + eLpNorm g p μ ^ P) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left' (hf.enorm.pow_const _),
            ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hf,
            ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hg]
  calc eLpNorm (f + g) p μ ^ Q + eLpNorm (f - g) p μ ^ Q
      ≤ (∫⁻ x, (‖f x + g x‖ₑ ^ Q + ‖f x - g x‖ₑ ^ Q) ^ (P / Q) ∂μ) ^ (1 / (P / Q)) := hrev
    _ ≤ ((2:ℝ≥0∞) ^ (P / Q) * (eLpNorm f p μ ^ P + eLpNorm g p μ ^ P)) ^ (1 / (P / Q)) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = 2 * (eLpNorm f p μ ^ P + eLpNorm g p μ ^ P) ^ (Q / P) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hs0.ne', ENNReal.rpow_one, hinv]

/-! ### Clarkson's inequalities on `Lp` -/

namespace Lp

variable {E : Type*} [NormedAddCommGroup E]

/-- `‖f‖ ^ r = (eLpNorm f p μ ^ r).toReal` for `f : Lp E p μ`. -/
theorem norm_rpow (f : Lp E p μ) (r : ℝ) : ‖f‖ ^ r = (eLpNorm f p μ ^ r).toReal := by
  rw [Lp.norm_def, ENNReal.toReal_rpow]

/-- `eLpNorm f p μ ^ r` is finite for `f : Lp E p μ` and `0 ≤ r`. -/
theorem eLpNorm_rpow_ne_top (f : Lp E p μ) {r : ℝ} (hr : 0 ≤ r) : eLpNorm f p μ ^ r ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg hr (Lp.memLp f).eLpNorm_ne_top

/-- **Clarkson's first inequality** in `Lp ℝ p μ`, `2 ≤ p < ∞` ([brezis2011functional]
Theorem 4.10, inequality (8)):
`‖(f + g)/2‖ ^ p + ‖(f - g)/2‖ ^ p ≤ (‖f‖ ^ p + ‖g‖ ^ p) / 2`. -/
theorem clarkson_of_two_le (hp : 2 ≤ p) (hp' : p ≠ ∞) (f g : Lp ℝ p μ) :
    ‖(2:ℝ)⁻¹ • (f + g)‖ ^ p.toReal + ‖(2:ℝ)⁻¹ • (f - g)‖ ^ p.toReal
      ≤ (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) / 2 := by
  have hP0 : (0:ℝ) ≤ p.toReal := ENNReal.toReal_nonneg
  have h := eLpNorm_add_rpow_add_eLpNorm_sub_rpow_le_of_two_le hp hp' (Lp.aestronglyMeasurable f)
    (Lp.aestronglyMeasurable g)
  have e1 : eLpNorm (⇑((2:ℝ)⁻¹ • (f + g))) p μ = eLpNorm ((2:ℝ)⁻¹ • (⇑f + ⇑g)) p μ :=
    eLpNorm_congr_ae ((Lp.coeFn_smul _ _).trans ((Lp.coeFn_add f g).const_smul _))
  have e2 : eLpNorm (⇑((2:ℝ)⁻¹ • (f - g))) p μ = eLpNorm ((2:ℝ)⁻¹ • (⇑f - ⇑g)) p μ :=
    eLpNorm_congr_ae ((Lp.coeFn_smul _ _).trans ((Lp.coeFn_sub f g).const_smul _))
  rw [norm_rpow, norm_rpow, norm_rpow, norm_rpow, e1, e2,
    ← ENNReal.toReal_add (by rw [← e1]; exact eLpNorm_rpow_ne_top _ hP0)
      (by rw [← e2]; exact eLpNorm_rpow_ne_top _ hP0),
    ← ENNReal.toReal_add (eLpNorm_rpow_ne_top _ hP0) (eLpNorm_rpow_ne_top _ hP0),
    ← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_div]
  exact ENNReal.toReal_mono (ENNReal.div_ne_top
    (ENNReal.add_ne_top.2 ⟨eLpNorm_rpow_ne_top _ hP0, eLpNorm_rpow_ne_top _ hP0⟩) (by simp)) h

/-- **Clarkson's second inequality** in `Lp ℝ p μ`, `1 < p ≤ 2` with conjugate exponent `q`
([brezis2011functional] Remark 3 of chapter 4, Problem 20, inequality (6)):
`‖f + g‖ ^ q + ‖f - g‖ ^ q ≤ 2 (‖f‖ ^ p + ‖g‖ ^ p) ^ (q / p)`. -/
theorem clarkson_of_le_two [p.HolderConjugate q] (hp : 1 < p) (hp2 : p ≤ 2) (f g : Lp ℝ p μ) :
    ‖f + g‖ ^ q.toReal + ‖f - g‖ ^ q.toReal
      ≤ 2 * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ^ (q.toReal / p.toReal) := by
  have hP0 : (0:ℝ) ≤ p.toReal := ENNReal.toReal_nonneg
  have hQ0 : (0:ℝ) ≤ q.toReal := ENNReal.toReal_nonneg
  have h := eLpNorm_add_rpow_add_eLpNorm_sub_rpow_le_of_le_two (q := q) hp hp2
    (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g)
  have e1 : eLpNorm (⇑(f + g)) p μ = eLpNorm (⇑f + ⇑g) p μ := eLpNorm_congr_ae (Lp.coeFn_add f g)
  have e2 : eLpNorm (⇑(f - g)) p μ = eLpNorm (⇑f - ⇑g) p μ := eLpNorm_congr_ae (Lp.coeFn_sub f g)
  rw [norm_rpow, norm_rpow, norm_rpow, norm_rpow, e1, e2,
    ← ENNReal.toReal_add (by rw [← e1]; exact eLpNorm_rpow_ne_top _ hQ0)
      (by rw [← e2]; exact eLpNorm_rpow_ne_top _ hQ0),
    ← ENNReal.toReal_add (eLpNorm_rpow_ne_top _ hP0) (eLpNorm_rpow_ne_top _ hP0),
    ENNReal.toReal_rpow, ← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ?_) h
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.add_ne_top.2 ⟨eLpNorm_rpow_ne_top _ hP0, eLpNorm_rpow_ne_top _ hP0⟩)

/-! ### Uniform convexity -/

/-- **`L^p` is uniformly convex for `1 < p < ∞`** ([brezis2011functional] Theorem 4.10, Step 2,
for `2 ≤ p`, and Remark 3 of chapter 4 / Problem 20, part C, for `1 < p ≤ 2`), theorem form. For
`2 ≤ p` the modulus is `δ = 2 - 2 (1 - (ε/2) ^ p) ^ (1/p)` from Clarkson's first inequality, for
`p ≤ 2` it is `δ = 2 - (2 ^ q - ε ^ q) ^ (1/q)` from the second. -/
theorem uniformConvexSpace_of_one_lt_of_ne_top [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    UniformConvexSpace (Lp ℝ p μ) := by
  refine ⟨fun ε hε => ?_⟩
  -- it suffices to treat `ε ≤ 2`
  set ε' := min ε 2 with hε'
  have hε'0 : 0 < ε' := lt_min hε two_pos
  have hε'2 : ε' ≤ 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hP1 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by simp) hp').2 hp
  have hnorm2 : ∀ x : Lp ℝ p μ, ‖(2:ℝ)⁻¹ • x‖ = 2⁻¹ * ‖x‖ := fun x => by
    rw [norm_smul, norm_inv, Real.norm_ofNat]
  rcases le_total 2 p with hp2 | hp2
  · -- `2 ≤ p`: Clarkson's first inequality
    set P := p.toReal with hP
    have hP2 : (2:ℝ) ≤ P := by
      rw [hP, ← ENNReal.toReal_ofNat 2]
      exact ENNReal.toReal_mono hp' hp2
    have hP0 : 0 < P := by linarith
    have hc0 : 0 < (ε' / 2) ^ P := Real.rpow_pos_of_pos (by positivity) _
    have hc1 : (ε' / 2) ^ P ≤ 1 :=
      Real.rpow_le_one (by positivity) (by linarith [div_le_one_of_le₀ hε'2 zero_le_two]) hP0.le
    have hlt : (1 - (ε' / 2) ^ P) ^ (1 / P) < 1 :=
      Real.rpow_lt_one (by linarith) (by linarith) (by positivity)
    refine ⟨2 - 2 * (1 - (ε' / 2) ^ P) ^ (1 / P), by linarith, fun f hf g hg hfg => ?_⟩
    have h := clarkson_of_two_le hp2 hp' f g
    rw [hf, hg, Real.one_rpow, hnorm2, hnorm2] at h
    have hsub : ε' / 2 ≤ 2⁻¹ * ‖f - g‖ := by rw [inv_mul_eq_div]; linarith
    have h1 : (ε' / 2) ^ P ≤ (2⁻¹ * ‖f - g‖) ^ P := Real.rpow_le_rpow (by positivity) hsub hP0.le
    have h2 : (2⁻¹ * ‖f + g‖) ^ P ≤ 1 - (ε' / 2) ^ P := by linarith
    have h3 : 2⁻¹ * ‖f + g‖ ≤ (1 - (ε' / 2) ^ P) ^ (1 / P) := by
      rw [one_div]
      exact (Real.le_rpow_inv_iff_of_pos (by positivity) (by linarith) hP0).2 h2
    linarith
  · -- `1 < p ≤ 2`: Clarkson's second inequality with the conjugate exponent
    have hpq : p.HolderConjugate (ENNReal.conjExponent p) :=
      ENNReal.HolderConjugate.conjExponent hp.le
    set q := ENNReal.conjExponent p with hq
    have hq' : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
    have hPQ : p.toReal.HolderConjugate q.toReal :=
      ENNReal.HolderConjugate.toReal_of_ne_top hp' hq'
    set P := p.toReal with hP
    set Q := q.toReal with hQ
    have hQ0 : 0 < Q := hPQ.symm.pos
    have hQP : Q / P = Q - 1 := hPQ.symm.div_conj_eq_sub_one
    have hεQ : ε' ^ Q ≤ 2 ^ Q := Real.rpow_le_rpow hε'0.le hε'2 hQ0.le
    have hεQ0 : 0 < ε' ^ Q := Real.rpow_pos_of_pos hε'0 _
    have h2Q : ((2:ℝ) ^ Q) ^ (1 / Q) = 2 := by
      rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hQ0.ne', Real.rpow_one]
    have hlt : (2 ^ Q - ε' ^ Q) ^ (1 / Q) < 2 :=
      calc (2 ^ Q - ε' ^ Q) ^ (1 / Q) < ((2:ℝ) ^ Q) ^ (1 / Q) :=
            Real.rpow_lt_rpow (by linarith) (by linarith) (by positivity)
        _ = 2 := h2Q
    refine ⟨2 - (2 ^ Q - ε' ^ Q) ^ (1 / Q), by linarith, fun f hf g hg hfg => ?_⟩
    have h := clarkson_of_le_two (q := q) hp hp2 f g
    have h2 : (2:ℝ) * (2 ^ Q / 2) = 2 ^ Q := by ring
    rw [hf, hg, Real.one_rpow, one_add_one_eq_two, ← hQ, ← hP, hQP, Real.rpow_sub_one two_ne_zero,
      h2] at h
    have h1 : ε' ^ Q ≤ ‖f - g‖ ^ Q := Real.rpow_le_rpow hε'0.le (hε'ε.trans hfg) hQ0.le
    have h2 : ‖f + g‖ ^ Q ≤ 2 ^ Q - ε' ^ Q := by linarith
    have h3 : ‖f + g‖ ≤ (2 ^ Q - ε' ^ Q) ^ (1 / Q) := by
      rw [one_div]
      exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (by linarith) hQ0).2 h2
    linarith

/-- **`L^p` is uniformly convex for `1 < p < ∞`** ([brezis2011functional] Theorem 4.10 and
Remark 3 of chapter 4), as an instance under `[Fact (1 < p)] [Fact (p ≠ ∞)]`. -/
instance instUniformConvexSpace [hp : Fact (1 < p)] [hp' : Fact (p ≠ ∞)] :
    UniformConvexSpace (Lp ℝ p μ) :=
  uniformConvexSpace_of_one_lt_of_ne_top hp.out hp'.out

/-! ### The inequalities of Problem 20, part B -/

/-- [brezis2011functional] Problem 20, inequality (4): for `2 ≤ p < ∞` with conjugate exponent
`q` and `f g : Lp ℝ p μ`, `‖f + g‖ ^ p + ‖f - g‖ ^ p ≤ 2 (‖f‖ ^ q + ‖g‖ ^ q) ^ (p / q)`. The
pointwise inequality `Real.abs_add_rpow_add_abs_sub_rpow_le` is integrated and Minkowski's
inequality in `L^{p/q}` (`ENNReal.lintegral_Lp_add_le`, `p / q = p - 1 ≥ 1`) bounds
`∫ (|f| ^ q + |g| ^ q) ^ (p/q)` by `(‖f‖ ^ q + ‖g‖ ^ q) ^ (p/q)`. -/
theorem norm_add_rpow_add_norm_sub_rpow_le [p.HolderConjugate q] (hp : 2 ≤ p) (hp' : p ≠ ∞)
    (f g : Lp ℝ p μ) :
    ‖f + g‖ ^ p.toReal + ‖f - g‖ ^ p.toReal
      ≤ 2 * (‖f‖ ^ q.toReal + ‖g‖ ^ q.toReal) ^ (p.toReal / q.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans_le hp).ne'
  have hq' : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2
    (by rintro rfl; exact absurd hp (by norm_num))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp' hq'
  set P := p.toReal with hPdef
  set Q := q.toReal with hQdef
  have hP2 : (2:ℝ) ≤ P := by
    rw [hPdef, ← ENNReal.toReal_ofNat 2]
    exact ENNReal.toReal_mono hp' hp
  have hQ0 : 0 < Q := hPQ.symm.pos
  have hPQ' : P / Q = P - 1 := hPQ.div_conj_eq_sub_one
  have ht1 : 1 ≤ P / Q := by rw [hPQ']; linarith
  have ht0 : 0 < P / Q := by linarith
  have hQt : Q * (P / Q) = P := mul_div_cancel₀ _ hQ0.ne'
  have hf := Lp.aestronglyMeasurable f
  have hg := Lp.aestronglyMeasurable g
  -- pointwise
  have hpt : ∀ x, ‖f x + g x‖ₑ ^ P + ‖f x - g x‖ₑ ^ P
      ≤ 2 * (‖f x‖ₑ ^ Q + ‖g x‖ₑ ^ Q) ^ (P / Q) := by
    intro x
    rw [enorm_rpow_eq_ofReal_abs_rpow _ (by linarith),
      enorm_rpow_eq_ofReal_abs_rpow _ (by linarith),
      enorm_rpow_eq_ofReal_abs_rpow _ hQ0.le, enorm_rpow_eq_ofReal_abs_rpow _ hQ0.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) ht0.le, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (Real.abs_add_rpow_add_abs_sub_rpow_le hP2 hPQ (f x) (g x))
  -- Minkowski in `L^{P/Q}`
  have hU : AEMeasurable (fun x => ‖f x‖ₑ ^ Q) μ := hf.enorm.pow_const _
  have hV : AEMeasurable (fun x => ‖g x‖ₑ ^ Q) μ := hg.enorm.pow_const _
  have hmink := ENNReal.lintegral_Lp_add_le hU hV ht1
  have hU' : ∫⁻ x, (‖f x‖ₑ ^ Q) ^ (P / Q) ∂μ = eLpNorm f p μ ^ P := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hf]
    simp_rw [← ENNReal.rpow_mul, hQt]
    rfl
  have hV' : ∫⁻ x, (‖g x‖ₑ ^ Q) ^ (P / Q) ∂μ = eLpNorm g p μ ^ P := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' hg]
    simp_rw [← ENNReal.rpow_mul, hQt]
    rfl
  have hPinv : P * (1 / (P / Q)) = Q := by rw [one_div_div, mul_div_cancel₀ _ (by linarith)]
  rw [hU', hV', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hPinv] at hmink
  have hmink' : ∫⁻ x, (‖f x‖ₑ ^ Q + ‖g x‖ₑ ^ Q) ^ (P / Q) ∂μ
      ≤ (eLpNorm f p μ ^ Q + eLpNorm g p μ ^ Q) ^ (P / Q) := by
    have := ENNReal.rpow_le_rpow hmink ht0.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel ht0.ne', ENNReal.rpow_one] at this
  -- assemble, in `ℝ≥0∞`
  have e1 : eLpNorm (⇑(f + g)) p μ = eLpNorm (⇑f + ⇑g) p μ := eLpNorm_congr_ae (Lp.coeFn_add f g)
  have e2 : eLpNorm (⇑(f - g)) p μ = eLpNorm (⇑f - ⇑g) p μ := eLpNorm_congr_ae (Lp.coeFn_sub f g)
  have key : eLpNorm (⇑f + ⇑g) p μ ^ P + eLpNorm (⇑f - ⇑g) p μ ^ P
      ≤ 2 * (eLpNorm f p μ ^ Q + eLpNorm g p μ ^ Q) ^ (P / Q) := by
    calc eLpNorm (⇑f + ⇑g) p μ ^ P + eLpNorm (⇑f - ⇑g) p μ ^ P
        = ∫⁻ x, ‖f x + g x‖ₑ ^ P + ‖f x - g x‖ₑ ^ P ∂μ := by
          rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' (hf.add hg),
            ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp0 hp' (hf.sub hg),
            ← lintegral_add_left' ((hf.add hg).enorm.pow_const _)]
          rfl
      _ ≤ ∫⁻ x, 2 * (‖f x‖ₑ ^ Q + ‖g x‖ₑ ^ Q) ^ (P / Q) ∂μ := lintegral_mono hpt
      _ = 2 * ∫⁻ x, (‖f x‖ₑ ^ Q + ‖g x‖ₑ ^ Q) ^ (P / Q) ∂μ :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ 2 * (eLpNorm f p μ ^ Q + eLpNorm g p μ ^ Q) ^ (P / Q) := by gcongr
  have hP0 : (0:ℝ) ≤ P := by linarith
  rw [norm_rpow, norm_rpow, norm_rpow, norm_rpow, e1, e2,
    ← ENNReal.toReal_add (by rw [← e1]; exact eLpNorm_rpow_ne_top _ hP0)
      (by rw [← e2]; exact eLpNorm_rpow_ne_top _ hP0),
    ← ENNReal.toReal_add (eLpNorm_rpow_ne_top _ hQ0.le) (eLpNorm_rpow_ne_top _ hQ0.le),
    ENNReal.toReal_rpow, ← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ?_) key
  exact ENNReal.rpow_ne_top_of_nonneg ht0.le
    (ENNReal.add_ne_top.2 ⟨eLpNorm_rpow_ne_top _ hQ0.le, eLpNorm_rpow_ne_top _ hQ0.le⟩)

/-- [brezis2011functional] Problem 20, inequality (5): for `2 ≤ p < ∞` with conjugate exponent
`q` and `f g : Lp ℝ p μ`,
`2 (‖f‖ ^ q + ‖g‖ ^ q) ^ (p / q) ≤ 2 ^ (p - 1) (‖f‖ ^ p + ‖g‖ ^ p)`; this is
`Real.two_mul_rpow_add_rpow_le` at `‖f‖` and `‖g‖`. Together with
`MeasureTheory.Lp.norm_add_rpow_add_norm_sub_rpow_le` it gives Clarkson's first inequality
again. -/
theorem two_mul_norm_rpow_add_norm_rpow_le [Fact (1 ≤ p)] [p.HolderConjugate q] (hp : 2 ≤ p)
    (hp' : p ≠ ∞) (f g : Lp ℝ p μ) :
    2 * (‖f‖ ^ q.toReal + ‖g‖ ^ q.toReal) ^ (p.toReal / q.toReal)
      ≤ 2 ^ (p.toReal - 1) * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) := by
  have hq' : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2
    (by rintro rfl; exact absurd hp (by norm_num))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp' hq'
  have hP2 : (2:ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_ofNat 2]
    exact ENNReal.toReal_mono hp' hp
  have h := Real.two_mul_rpow_add_rpow_le hP2 hPQ ‖f‖ ‖g‖
  rwa [abs_norm, abs_norm] at h

end Lp

end MeasureTheory

end
