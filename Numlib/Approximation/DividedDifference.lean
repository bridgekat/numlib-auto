import Mathlib.LinearAlgebra.Lagrange
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

A second section carries the classical object at `m + 1` distinct nodes, `f[v₀, …, v_m]`, whose use
is the divided-difference form of the interpolation error, `f(t) - p(t) = ω(t) f[v₀, …, v_m, t]`.
Mathlib has the top coefficient of an interpolating polynomial as `Lagrange.coeff_eq_sum` but not
the name or the error formula.

## Main definitions

* `DividedDifference.firstOrder`, `DividedDifference.secondOrder`.
* `DividedDifference.newton` — the Newton divided difference `f[v₀, …, v_m]` at `m + 1` nodes.

## Main statements

* `DividedDifference.sub_eq_mul_firstOrder`, `DividedDifference.sub_firstOrder_eq` — the two Taylor
  identities, which are what make the definitions divided differences.
* `DividedDifference.firstOrder_self`, `DividedDifference.secondOrder_self` — the diagonal values.
* `DividedDifference.continuous_firstOrder`, `DividedDifference.continuous_secondOrder`.
* `DividedDifference.newton_eq_coeff` — the Newton divided difference is the coefficient of `X^m`
  in the interpolating polynomial, and `DividedDifference.newton_pair` identifies the two-node case
  with `firstOrder`.
* `DividedDifference.sub_eval_interpolate_eq_newton` — the divided-difference form of the
  interpolation error.

## References

The Hermite–Genocchi formula is classical; see [han2009theoretical], §3.2, and
[kress1998numerical], §8.2. The use made of it here is [han2009theoretical], (13.1.33)–(13.1.34).
The divided-difference form of the interpolation error is [han2009theoretical], (3.2.5).
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

/-! ### The Newton divided differences at finitely many nodes

The divided difference of the previous section is the two-node one, written so as to survive the
collision of its nodes. This section is the classical object at `m + 1` distinct nodes: the
coefficient `f[v₀, …, v_m]` of the Newton form of the interpolating polynomial. -/

open Polynomial

/-- The **Newton divided difference** `f[v₀, …, v_m]` of `f` at the `m + 1` nodes `v`, in its
explicit form `∑ᵢ f(vᵢ) / ∏_{j ≠ i} (vᵢ - vⱼ)`.

For distinct nodes it is the coefficient of `X^m` in the polynomial interpolating `f` at them
(`DividedDifference.newton_eq_coeff`) — its *leading* coefficient exactly when that interpolant has
degree `m`, and `0` when it has lower degree. That is the property the theory uses; the explicit
form is taken as the definition because it is visibly symmetric in the nodes and needs no
hypothesis. -/
noncomputable def newton {m : ℕ} (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, f (v i) / ∏ j ∈ Finset.univ.erase i, (v i - v j)

/-- **The Newton divided difference is the coefficient of `X^m` in the interpolating polynomial.**
This is `Lagrange.coeff_eq_sum` read backwards. -/
theorem newton_eq_coeff {m : ℕ} (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v) :
    newton f v = (Lagrange.interpolate Finset.univ v fun i => f (v i)).coeff m := by
  have hcard : (Finset.univ : Finset (Fin (m + 1))).card = m + 1 := by simp
  have hdeg : (Lagrange.interpolate Finset.univ v fun i => f (v i)).degree
      < (Finset.univ : Finset (Fin (m + 1))).card :=
    Lagrange.degree_interpolate_lt _ hv.injOn
  have h := Lagrange.coeff_eq_sum (v := v) hv.injOn hdeg
  rw [hcard, Nat.add_sub_cancel] at h
  simp only [newton]
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Lagrange.eval_interpolate_at_node _ hv.injOn (Finset.mem_univ i)]

/-- **The divided-difference form of the interpolation error** ([han2009theoretical], (3.2.5)): if
`p` interpolates `f` at the `m + 1` distinct nodes `v₀, …, v_m` and `t` is none of them, then

`f(t) - p(t) = ω(t) · f[v₀, …, v_m, t]`,   `ω(t) = ∏ᵢ (t - vᵢ)`.

Unlike the mean-value form `ω(t) f⁽ᵐ⁺¹⁾(ξ)/(m + 1)!` it asks nothing of `f` beyond its values.

The proof is Newton's form of the interpolant: the interpolant `q` at the enlarged node set differs
from `p` by `f[v₀, …, v_m, t] ω`, because subtracting that multiple of `ω` from `q` leaves a
polynomial of degree at most `m` that still takes the values of `f` at `v₀, …, v_m`. -/
theorem sub_eval_interpolate_eq_newton {m : ℕ} (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) {t : ℝ} (ht : ∀ i, v i ≠ t) :
    f t - (Lagrange.interpolate Finset.univ v fun i => f (v i)).eval t
      = (∏ i, (t - v i)) * newton f (Fin.snoc v t) := by
  classical
  set w : Fin (m + 2) → ℝ := Fin.snoc v t with hwdef
  have hwcast : ∀ i : Fin (m + 1), w i.castSucc = v i := by
    intro i; rw [hwdef]; simp
  have hwlast : w (Fin.last (m + 1)) = t := by rw [hwdef]; simp
  have hwinj : Function.Injective w := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast j => rw [hwlast, hwcast] at hab; exact absurd hab.symm (ht j)
    | cast i =>
      induction b using Fin.lastCases with
      | last => rw [hwlast, hwcast] at hab; exact absurd hab (ht i)
      | cast j => rw [hwcast, hwcast] at hab; rw [hv hab]
  set c : ℝ := newton f w with hcdef
  set q : ℝ[X] := Lagrange.interpolate Finset.univ w fun j => f (w j) with hqdef
  set ω : ℝ[X] := Lagrange.nodal Finset.univ v with hωdef
  -- the top coefficient of the enlarged interpolant is the divided difference
  have hqc : q.coeff (m + 1) = c := (newton_eq_coeff f hwinj).symm
  have hqdeg : q.degree < ((m + 2 : ℕ) : WithBot ℕ) := by
    have h := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (m + 2))))
      (fun j => f (w j)) hwinj.injOn
    have hcard : (Finset.univ : Finset (Fin (m + 2))).card = m + 2 := by simp
    rw [hcard] at h
    rw [hqdef]
    exact h
  have hωdeg : ω.degree = ((m + 1 : ℕ) : WithBot ℕ) := by
    rw [hωdef, Lagrange.degree_nodal]
    simp
  have hωcoeff : ω.coeff (m + 1) = 1 := by
    have hnd : ω.natDegree = m + 1 := by rw [hωdef, Lagrange.natDegree_nodal]; simp
    rw [← hnd, ← Polynomial.leadingCoeff, hωdef]
    exact Lagrange.nodal_monic
  -- subtracting `c ω` from the enlarged interpolant drops the degree back to `m`
  have hdeglt : (q - C c * ω).degree < ((m + 1 : ℕ) : WithBot ℕ) := by
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 fun k hk => ?_
    have hk' : m + 1 ≤ k := by exact_mod_cast hk
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rcases eq_or_lt_of_le hk' with heq | hlt
    · rw [← heq, hqc, hωcoeff, mul_one, sub_self]
    · have h1 : q.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt (hqdeg.trans_le (by exact_mod_cast hlt))
      have h2 : ω.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt (hωdeg ▸ (by exact_mod_cast hlt))
      rw [h1, h2, mul_zero, sub_zero]
  have hvals : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      (q - C c * ω).eval (v i) = f (v i) := by
    intro i _
    have hq : q.eval (v i) = f (v i) := by
      have h := Lagrange.eval_interpolate_at_node (fun j => f (w j)) hwinj.injOn
        (Finset.mem_univ i.castSucc)
      rwa [hwcast] at h
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hωdef,
      Lagrange.eval_nodal_at_node (Finset.mem_univ i), mul_zero, sub_zero, hq]
  have hcard1 : (Finset.univ : Finset (Fin (m + 1))).card = m + 1 := by simp
  have hp : q - C c * ω = Lagrange.interpolate Finset.univ v fun i => f (v i) :=
    Lagrange.eq_interpolate_of_eval_eq (fun i => f (v i)) hv.injOn
      (by rw [hcard1]; exact hdeglt) hvals
  -- evaluate at `t`
  have hqt : q.eval t = f t := by
    have h := Lagrange.eval_interpolate_at_node (fun j => f (w j)) hwinj.injOn
      (Finset.mem_univ (Fin.last (m + 1)))
    rwa [hwlast] at h
  have hωt : ω.eval t = ∏ i, (t - v i) := by rw [hωdef, Lagrange.eval_nodal]
  have := congrArg (Polynomial.eval t) hp
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hqt, hωt] at this
  rw [← this]
  ring

/-- The Newton divided difference at two distinct nodes is the difference quotient, hence the value
of `DividedDifference.firstOrder` there: the two sections describe the same object. -/
theorem newton_pair (hf : ∀ x, HasDerivAt f (f' x) x) (hc' : Continuous f') {s t : ℝ}
    (hst : s ≠ t) : newton f ![t, s] = firstOrder f' s t := by
  have hne : s - t ≠ 0 := sub_ne_zero.2 hst
  have hval : newton f ![t, s] = (f s - f t) / (s - t) := by
    rw [newton, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (Finset.univ.erase (0 : Fin 2)) = {1} from rfl,
      show (Finset.univ.erase (1 : Fin 2)) = {0} from rfl]
    simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  rw [hval, sub_eq_mul_firstOrder hf hc' s t]
  field_simp

end DividedDifference
