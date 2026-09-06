import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Divided differences as continuous functions of their nodes

The divided differences of a function are usually written as quotients,
`f[t, s] = (f s - f t) / (s - t)` and `f[s, s, t] = (f' s - f[t, s]) / (s - t)`, which are junk on
the diagonal. This file gives them by their **Hermite–Genocchi integrals** instead,

`firstOrder f' s t = ∫₀¹ f' ((s - t) θ + t) dθ`,
`secondOrder f'' s t = ∫₀¹ (1 - θ) f'' ((t - s) θ + s) dθ`,

which agree with the quotients off the diagonal and are jointly *continuous* in the nodes, with the
values `f' t` and `f'' t / 2` on it. The two defining identities

`f s - f t = (s - t) * firstOrder f' s t` and
`f' s - firstOrder f' s t = (s - t) * secondOrder f'' s t`

are the first- and second-order Taylor expansions with integral remainder, which Mathlib does not
have: `Mathlib/Analysis/Calculus/Taylor.lean` carries only the mean-value forms.

The point of the exercise is that a quotient whose numerator and denominator both vanish to second
order on the diagonal — the parametrized double-layer kernel of a plane curve is the example — has a
continuous extension that can be *defined*, not merely proved to exist, by cancelling the divided
differences against each other.

## Main definitions

* `DividedDifference.firstOrder`, `DividedDifference.secondOrder`.

## Main statements

* `DividedDifference.sub_eq_mul_firstOrder`, `DividedDifference.sub_firstOrder_eq` — the two Taylor
  identities, which are what make the definitions divided differences.
* `DividedDifference.firstOrder_self`, `DividedDifference.secondOrder_self` — the diagonal values.
* `DividedDifference.continuous_firstOrder`, `DividedDifference.continuous_secondOrder`.

## References

The Hermite–Genocchi formula is classical; see [han2009theoretical], §3.2, and
[kress1998numerical], §8.2. The use made of it here is [han2009theoretical], (13.1.33)–(13.1.34).
-/

open MeasureTheory Set

namespace DividedDifference

variable {f f' f'' : ℝ → ℝ}

/-- **The first divided difference** `f[t, s]`, given by its Hermite–Genocchi integral
`∫₀¹ f' ((s - t) θ + t) dθ` rather than by the quotient `(f s - f t) / (s - t)`, so that it is
defined and continuous on the diagonal as well.

The argument is the *derivative* `f'`, since that is all the integral sees. -/
noncomputable def firstOrder (f' : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, f' ((s - t) * θ + t)

/-- **The second divided difference** `f[s, s, t]` at the repeated node `s`, given by its
Hermite–Genocchi integral `∫₀¹ (1 - θ) f'' ((t - s) θ + s) dθ`. -/
noncomputable def secondOrder (f'' : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, (1 - θ) * f'' ((t - s) * θ + s)

/-- On the diagonal the first divided difference is the derivative. -/
@[simp]
theorem firstOrder_self (f' : ℝ → ℝ) (t : ℝ) : firstOrder f' t t = f' t := by
  simp [firstOrder]

/-- On the diagonal the second divided difference is half the second derivative. -/
@[simp]
theorem secondOrder_self (f'' : ℝ → ℝ) (t : ℝ) : secondOrder f'' t t = f'' t / 2 := by
  have hhalf : (∫ θ in (0 : ℝ)..1, (1 - θ)) = 1 / 2 := by
    have hd : ∀ x : ℝ, HasDerivAt (fun θ : ℝ => θ - θ * θ / 2) (1 - x) x := fun x => by
      have h : HasDerivAt (fun θ : ℝ => θ - θ * θ / 2) (1 - (1 * x + x * 1) / 2) x :=
        (hasDerivAt_id x).sub (((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2)
      convert h using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
    norm_num
  simp only [secondOrder, sub_self, zero_mul, zero_add]
  rw [intervalIntegral.integral_mul_const, hhalf]
  ring

/-- **The first Taylor identity**: `f s - f t = (s - t) * f[t, s]`, which is what makes
`DividedDifference.firstOrder` a divided difference. It is the fundamental theorem of calculus after
the change of variables `v = (s - t) θ + t`. -/
theorem sub_eq_mul_firstOrder (hf : ∀ x, HasDerivAt f (f' x) x) (hc' : Continuous f') (s t : ℝ) :
    f s - f t = (s - t) * firstOrder f' s t := by
  rcases eq_or_ne s t with rfl | hst
  · simp
  · have hne : s - t ≠ 0 := sub_ne_zero.2 hst
    have hcv : firstOrder f' s t = (s - t)⁻¹ * ∫ v in t..s, f' v := by
      rw [firstOrder, intervalIntegral.integral_comp_mul_add (f := f') hne t]
      simp
    have hftc : (∫ v in t..s, f' v) = f s - f t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
        (hc'.intervalIntegrable _ _)
    rw [hcv, hftc]
    field_simp

/-- **The second Taylor identity**: `f' s - f[t, s] = (s - t) * f[s, s, t]`, which is what makes
`DividedDifference.secondOrder` the second divided difference at the repeated node `s`.

The change of variables `v = (t - s) θ + s` turns `secondOrder` into
`(t - s)⁻² ∫_s^t (t - v) f'' v dv`, and integration by parts against `u v = t - v` turns that into
`(f t - f s) - (t - s) f' s`. -/
theorem sub_firstOrder_eq (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hc' : Continuous f') (hc'' : Continuous f'') (s t : ℝ) :
    f' s - firstOrder f' s t = (s - t) * secondOrder f'' s t := by
  rcases eq_or_ne s t with rfl | hst
  · simp
  · have hne : t - s ≠ 0 := sub_ne_zero.2 (Ne.symm hst)
    have hnes : s - t ≠ 0 := sub_ne_zero.2 hst
    -- the change of variables
    have hcongr : ∀ θ : ℝ, (1 - θ) * f'' ((t - s) * θ + s)
        = (fun v => (t - s)⁻¹ * ((t - v) * f'' v)) ((t - s) * θ + s) := by
      intro θ
      have h1 : t - ((t - s) * θ + s) = (t - s) * (1 - θ) := by ring
      simp only [h1]
      field_simp
    have hcv : secondOrder f'' s t = (t - s)⁻¹ * ((t - s)⁻¹ * ∫ v in s..t, (t - v) * f'' v) := by
      rw [secondOrder, intervalIntegral.integral_congr (g := fun θ =>
        (fun v => (t - s)⁻¹ * ((t - v) * f'' v)) ((t - s) * θ + s)) fun θ _ => hcongr θ,
        intervalIntegral.integral_comp_mul_add
          (f := fun v => (t - s)⁻¹ * ((t - v) * f'' v)) hne s]
      simp only [mul_zero, zero_add, mul_one, smul_eq_mul]
      rw [intervalIntegral.integral_const_mul, show t - s + s = t from by ring]
    -- integration by parts
    have hparts : (∫ v in s..t, (t - v) * f'' v)
        = (t - t) * f' t - (t - s) * f' s - ∫ v in s..t, (-1 : ℝ) * f' v := by
      refine intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun v => t - v)
        (u' := fun _ => (-1 : ℝ)) (v := f') (v' := f'') (fun x _ => ?_) (fun x _ => hf' x)
        (intervalIntegrable_const) (hc''.intervalIntegrable _ _)
      simpa using (hasDerivAt_id x).const_sub t
    have hftc : (∫ v in s..t, f' v) = f t - f s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
        (hc'.intervalIntegrable _ _)
    have hparts' : (∫ v in s..t, (t - v) * f'' v) = -((t - s) * f' s) + (f t - f s) := by
      rw [hparts, intervalIntegral.integral_const_mul, hftc]
      ring
    -- the first divided difference through the first identity
    have hfirst : firstOrder f' s t = (s - t)⁻¹ * (f s - f t) := by
      rw [sub_eq_mul_firstOrder hf hc' s t]
      field_simp
    rw [hcv, hparts', hfirst]
    field_simp
    ring

/-- The first divided difference is jointly continuous in its two nodes, the diagonal included. -/
@[fun_prop]
theorem continuous_firstOrder (hc' : Continuous f') :
    Continuous fun p : ℝ × ℝ => firstOrder f' p.1 p.2 :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℝ) (θ : ℝ) => f' ((p.1 - p.2) * θ + p.2)) (by fun_prop) 0 1

/-- The second divided difference is jointly continuous in its two nodes, the diagonal included. -/
@[fun_prop]
theorem continuous_secondOrder (hc'' : Continuous f'') :
    Continuous fun p : ℝ × ℝ => secondOrder f'' p.1 p.2 :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℝ) (θ : ℝ) => (1 - θ) * f'' ((p.2 - p.1) * θ + p.1)) (by fun_prop) 0 1

end DividedDifference
