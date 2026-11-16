/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Divided differences as continuous functions of their nodes

The divided differences of a function $f$ are usually defined as quotients,
$f[t, s] = (f(s) - f(t))/(s - t)$ and $f[s, s, t] = (f'(s) - f[t, s])/(s - t)$. These quotients have
no meaning on the diagonal $s = t$. This module defines them instead by their **Hermite–Genocchi
integrals**,
$$f[t, s] = \int_0^1 f'\bigl((s - t)\theta + t\bigr) \, d\theta, \qquad f[s, s, t] = \int_0^1 (1 -
  \theta) f''\bigl((t - s)\theta + s\bigr) \, d\theta.$$
They agree with the quotients off the diagonal, they are jointly continuous in the nodes, and on the
diagonal they take the values $f'(t)$ and $f''(t)/2$. The two identities
$f(s) - f(t) = (s - t) f[t, s]$ and $f'(s) - f[t, s] = (s - t) f[s, s, t]$ are the first- and
second-order Taylor expansions with integral remainder. The Hermite–Genocchi formula is classical;
see §3.2 of [han2009theoretical] and §8.2 of [kress1998numerical].

With these integrals, a quotient whose numerator and denominator both vanish to second order on the
diagonal has a continuous extension that is defined explicitly, not only proved to exist: the
divided differences cancel against each other. An example is the parametrized double-layer kernel of
a plane curve, as in (13.1.33)–(13.1.34) of [han2009theoretical]. The module also has the Newton
divided difference $f[v_0, \dots, v_m]$ at $m + 1$ distinct nodes, and the divided-difference form
$f(t) - p(t) = \omega(t) f[v_0, \dots, v_m, t]$ of the interpolation error, (3.2.5) of
[han2009theoretical].

## Main definitions

* `DividedDifference.firstOrder`: the first divided difference $f[t, s]$, as an integral of $f'$.
* `DividedDifference.secondOrder`: the second divided difference $f[s, s, t]$ with the repeated node
  $s$, as an integral of $f''$.
* `DividedDifference.newton`: the Newton divided difference $f[v_0, \dots, v_m] = \sum_i f(v_i) /
  \prod_{j \neq i} (v_i - v_j)$.

## Main results

* `DividedDifference.sub_eq_mul_firstOrder`: $f(s) - f(t) = (s - t) f[t, s]$.
* `DividedDifference.sub_firstOrder_eq`: $f'(s) - f[t, s] = (s - t) f[s, s, t]$.
* `DividedDifference.firstOrder_self` and `DividedDifference.secondOrder_self`: $f[t, t] = f'(t)$
  and $f[t, t, t] = f''(t)/2$.
* `DividedDifference.continuous_firstOrder` and `DividedDifference.continuous_secondOrder`: the two
  divided differences are jointly continuous in their nodes.
* `DividedDifference.newton_eq_coeff`: at distinct nodes, $f[v_0, \dots, v_m]$ is the coefficient of
  $X^m$ in the polynomial that interpolates $f$.
* `DividedDifference.newton_pair`: the Newton divided difference at two distinct nodes equals
  `DividedDifference.firstOrder`.
* `DividedDifference.sub_eval_interpolate_eq_newton`: the divided-difference form of the
  interpolation error.
* `DividedDifference.newton_two_eq`, `DividedDifference.newton_three_eq` and
  `DividedDifference.newton_four_eq`: the explicit forms at two, three and four nodes.
* `DividedDifference.newton_three_swap₁` and `DividedDifference.newton_three_swap₂`: the three-node
  divided difference is symmetric in its nodes.
* `DividedDifference.newton_three_eq_newton_two_dslope` and
  `DividedDifference.newton_four_eq_newton_three_dslope`: a divided difference with a node $a$ is a
  divided difference of $\operatorname{dslope} f \, a$ of one order less.
* `DividedDifference.exists_newton_three_eq`: at three distinct nodes, $f[x, y, z] = f''(\xi)/2$ for
  some $\xi$.

## Implementation notes

* `DividedDifference.firstOrder` and `DividedDifference.secondOrder` take the derivatives $f'$ and
  $f''$ as arguments, not $f$, because the integrals use only these.
* Mathlib has Taylor's theorem only with the mean value forms of the remainder
  (`Mathlib.Analysis.Calculus.Taylor`), and not with the integral remainder.
* Mathlib has the top coefficient of an interpolating polynomial (`Lagrange.coeff_eq_sum`), but not
  the divided difference as a named object or the error formula.
-/

open MeasureTheory Set

namespace DividedDifference

variable {f f' f'' : ℝ → ℝ}

/-- **The first divided difference** $f[t, s]$, defined by its Hermite–Genocchi integral
$$f[t, s] = \int_0^1 f'\bigl((s - t)\theta + t\bigr) \, d\theta.$$
Unlike the quotient $(f(s) - f(t))/(s - t)$, the integral is defined and continuous on the
diagonal $s = t$.

The argument is $f'$, not $f$, because the integral uses only $f'$. -/
noncomputable def firstOrder (f' : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, f' ((s - t) * θ + t)

/-- **The second divided difference** $f[s, s, t]$ with the repeated node $s$, defined by its
Hermite–Genocchi integral
$$f[s, s, t] = \int_0^1 (1 - \theta) f''\bigl((t - s)\theta + s\bigr) \, d\theta.$$
Here the argument is the second derivative $f''$. -/
noncomputable def secondOrder (f'' : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, (1 - θ) * f'' ((t - s) * θ + s)

/-- On the diagonal, the first divided difference is the derivative: $f[t, t] = f'(t)$. -/
@[simp]
theorem firstOrder_self (f' : ℝ → ℝ) (t : ℝ) : firstOrder f' t t = f' t := by
  simp [firstOrder]

/-- On the diagonal, the second divided difference is half the second derivative:
$f[t, t, t] = f''(t)/2$. -/
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

/-- **The first Taylor identity.** Let $f$ have the continuous derivative $f'$ on $\mathbb{R}$. Then
for all $s, t \in \mathbb{R}$,
$$f(s) - f(t) = (s - t) \, f[t, s].$$

This identity makes `DividedDifference.firstOrder` a divided difference. The proof is the
fundamental theorem of calculus after the change of variables $v = (s - t)\theta + t$. -/
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

/-- **The second Taylor identity.** Let $f$ have the continuous derivative $f'$ on $\mathbb{R}$, and
let $f'$ have the continuous derivative $f''$. Then for all $s, t \in \mathbb{R}$,
$$f'(s) - f[t, s] = (s - t) \, f[s, s, t].$$

This identity makes `DividedDifference.secondOrder` the second divided difference with the
repeated node $s$. The change of variables $v = (t - s)\theta + s$ gives $f[s, s, t] = (t -
s)^{-2} \int_s^t (t - v) f''(v) \, dv$. Integration by parts turns this into $(t - s)^{-2}
\bigl(f(t) - f(s) - (t - s) f'(s)\bigr)$. -/
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

/-- If $f'$ is continuous, the first divided difference $(s, t) \mapsto f[t, s]$ is jointly
continuous on $\mathbb{R}^2$, the diagonal included. -/
@[fun_prop]
theorem continuous_firstOrder (hc' : Continuous f') :
    Continuous fun p : ℝ × ℝ => firstOrder f' p.1 p.2 :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℝ) (θ : ℝ) => f' ((p.1 - p.2) * θ + p.2)) (by fun_prop) 0 1

/-- If $f''$ is continuous, the second divided difference $(s, t) \mapsto f[s, s, t]$ is jointly
continuous on $\mathbb{R}^2$, the diagonal included. -/
@[fun_prop]
theorem continuous_secondOrder (hc'' : Continuous f'') :
    Continuous fun p : ℝ × ℝ => secondOrder f'' p.1 p.2 :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℝ) (θ : ℝ) => (1 - θ) * f'' ((p.2 - p.1) * θ + p.1)) (by fun_prop) 0 1

/-!
### The Newton divided differences at finitely many nodes

The divided difference of the previous section has two nodes, and it is defined also when the nodes
coincide. This section has the classical object at $m + 1$ distinct nodes: the coefficient
$f[v_0, \dots, v_m]$ of the Newton form of the interpolating polynomial.
-/

open Polynomial

/-- The **Newton divided difference** of $f$ at the $m + 1$ nodes $v_0, \dots, v_m$:
$$f[v_0, \dots, v_m] = \sum_{i=0}^{m} \frac{f(v_i)}{\prod_{j \neq i} (v_i - v_j)}.$$

For distinct nodes it is the coefficient of $X^m$ in the polynomial that interpolates $f$ at the
nodes (`DividedDifference.newton_eq_coeff`). This is the leading coefficient when the
interpolant has degree $m$, and $0$ when it has a lower degree. The explicit form is the
definition because it is visibly symmetric in the nodes and needs no hypothesis. When two nodes
coincide, a quotient with a zero denominator is $0$ by the Lean convention. -/
noncomputable def newton {m : ℕ} (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, f (v i) / ∏ j ∈ Finset.univ.erase i, (v i - v j)

/-- **The Newton divided difference is the coefficient of $X^m$ in the interpolating polynomial.**
Let $v_0, \dots, v_m$ be distinct real numbers, and let $p$ be the polynomial of degree at most
$m$ with $p(v_i) = f(v_i)$ for all $i$. Then $f[v_0, \dots, v_m]$ is the coefficient of $X^m$ in
$p$.

The interpolant is `Lagrange.interpolate`, and the proof is `Lagrange.coeff_eq_sum`. -/
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

/-- **The divided-difference form of the interpolation error**, (3.2.5) of [han2009theoretical]. Let
$v_0, \dots, v_m$ be distinct real numbers, let $p$ be the polynomial of degree at most $m$ that
interpolates $f$ at them, and let $t$ be different from all $v_i$. Then
$$f(t) - p(t) = \omega(t) \, f[v_0, \dots, v_m, t], \qquad \omega(t) = \prod_{i=0}^{m} (t -
  v_i).$$
Unlike the mean value form $\omega(t) f^{(m+1)}(\xi)/(m + 1)!$, it needs nothing of $f$ beyond
its values.

The proof uses the Newton form of the interpolant. The interpolant $q$ at the nodes
$v_0, \dots, v_m, t$ differs from $p$ by $f[v_0, \dots, v_m, t] \, \omega$. Indeed, $q$ minus
this multiple of $\omega$ is a polynomial of degree at most $m$ that takes the values of $f$ at
$v_0, \dots, v_m$. The node list $v_0, \dots, v_m, t$ is `Fin.snoc v t`. -/
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

/-!
### Explicit formulas at two, three and four nodes

These follow from the definition of `DividedDifference.newton`. They are algebraic identities in the
values of $f$ at the nodes: the quotient forms, the symmetry of a three-node divided difference in
its nodes, the Newton form of the quadratic interpolant, and the reduction of a divided difference
with a fixed node $a$ to a divided difference of $\operatorname{dslope} f \, a$ of one order less.
-/

section Explicit

variable (f : ℝ → ℝ) {w x y z : ℝ}

/-- For $x \neq y$, the Newton divided difference at two nodes is $f[x, y] = (f(y) - f(x))/(y - x)$.
-/
theorem newton_two_eq (hxy : x ≠ y) : newton f ![x, y] = (f y - f x) / (y - x) := by
  have hne : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  rw [newton, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (Finset.univ.erase (0 : Fin 2)) = {1} from rfl,
    show (Finset.univ.erase (1 : Fin 2)) = {0} from rfl]
  simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- The Newton divided difference at three nodes is
$$f[x, y, z] = \frac{f(x)}{(x - y)(x - z)} + \frac{f(y)}{(y - x)(y - z)} + \frac{f(z)}{(z -
  x)(z - y)}.$$
-/
theorem newton_three_eq :
    newton f ![x, y, z] = f x / ((x - y) * (x - z)) + f y / ((y - x) * (y - z)) +
      f z / ((z - x) * (z - y)) := by
  rw [newton, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [show (Finset.univ.erase (0 : Fin 3)) = {1, 2} from rfl,
    show (Finset.univ.erase (1 : Fin 3)) = {0, 2} from rfl,
    show (Finset.univ.erase (2 : Fin 3)) = {0, 1} from rfl]
  simp

/-- **A divided difference with the node $a$ is a divided difference of
$\operatorname{dslope} f \, a$.** For distinct $x$, $y$ and $a$,
$$f[x, y, a] = g[x, y], \qquad g = \operatorname{dslope} f \, a,$$
where $g(u) = (f(u) - f(a))/(u - a)$ for $u \neq a$.

This is the recursive definition of divided differences, read with $a$ as the first node. -/
theorem newton_three_eq_newton_two_dslope (a : ℝ) (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    newton f ![x, y, a] = newton (dslope f a) ![x, y] := by
  rw [newton_three_eq, newton_two_eq _ hxy, dslope_of_ne f hxa, dslope_of_ne f hya,
    slope_def_field, slope_def_field]
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h2 : x - a ≠ 0 := sub_ne_zero.2 hxa
  have h3 : y - a ≠ 0 := sub_ne_zero.2 hya
  have h4 : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have h5 : a - x ≠ 0 := sub_ne_zero.2 hxa.symm
  have h6 : a - y ≠ 0 := sub_ne_zero.2 hya.symm
  field_simp
  ring

/-- The Newton divided difference at four nodes is
$$f[w, x, y, z] = \frac{f(w)}{(w - x)(w - y)(w - z)} + \frac{f(x)}{(x - w)(x - y)(x - z)} +
  \frac{f(y)}{(y - w)(y - x)(y - z)} + \frac{f(z)}{(z - w)(z - x)(z - y)}.$$
-/
theorem newton_four_eq {w : ℝ} :
    newton f ![w, x, y, z] =
      f w / ((w - x) * (w - y) * (w - z)) + f x / ((x - w) * (x - y) * (x - z)) +
        f y / ((y - w) * (y - x) * (y - z)) + f z / ((z - w) * (z - x) * (z - y)) := by
  rw [newton, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  rw [show (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} from rfl,
    show (Finset.univ.erase (1 : Fin 4)) = {0, 2, 3} from rfl,
    show (Finset.univ.erase (2 : Fin 4)) = {0, 1, 3} from rfl,
    show (Finset.univ.erase (3 : Fin 4)) = {0, 1, 2} from rfl]
  simp
  ring

/-- **A four-node divided difference with the node $a$ is a three-node divided difference of
$\operatorname{dslope} f \, a$.** For distinct $x$, $y$, $z$ and $a$,
$$f[x, y, z, a] = g[x, y, z], \qquad g = \operatorname{dslope} f \, a.$$

This is the four-node analogue of `DividedDifference.newton_three_eq_newton_two_dslope`. It
turns a third divided difference with the node $a$ into a second divided difference of a
function whose second derivative at $a$ is $f'''(a)/3$. -/
theorem newton_four_eq_newton_three_dslope (a : ℝ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxa : x ≠ a) (hya : y ≠ a) (hza : z ≠ a) :
    newton f ![x, y, z, a] = newton (dslope f a) ![x, y, z] := by
  rw [newton_four_eq, newton_three_eq, dslope_of_ne f hxa, dslope_of_ne f hya,
    dslope_of_ne f hza, slope_def_field, slope_def_field, slope_def_field]
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h2 : x - z ≠ 0 := sub_ne_zero.2 hxz
  have h3 : y - z ≠ 0 := sub_ne_zero.2 hyz
  have h4 : x - a ≠ 0 := sub_ne_zero.2 hxa
  have h5 : y - a ≠ 0 := sub_ne_zero.2 hya
  have h6 : z - a ≠ 0 := sub_ne_zero.2 hza
  have h1' : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have h2' : z - x ≠ 0 := sub_ne_zero.2 hxz.symm
  have h3' : z - y ≠ 0 := sub_ne_zero.2 hyz.symm
  have h4' : a - x ≠ 0 := sub_ne_zero.2 hxa.symm
  have h5' : a - y ≠ 0 := sub_ne_zero.2 hya.symm
  have h6' : a - z ≠ 0 := sub_ne_zero.2 hza.symm
  field_simp
  ring

/-- The three-node divided difference is symmetric in its first two nodes:
$f[x, y, z] = f[y, x, z]$. -/
theorem newton_three_swap₁ : newton f ![x, y, z] = newton f ![y, x, z] := by
  rw [newton_three_eq, newton_three_eq]; ring

/-- The three-node divided difference is symmetric in its last two nodes: $f[x, y, z] = f[x, z, y]$.
-/
theorem newton_three_swap₂ : newton f ![x, y, z] = newton f ![x, z, y] := by
  rw [newton_three_eq, newton_three_eq]; ring

/-- **The Newton form of the quadratic interpolant, at the third node.** For distinct $x$, $y$ and
$z$,
$$f(z) = f(x) + (z - x) \frac{f(y) - f(x)}{y - x} + (z - x)(z - y) \, f[x, y, z].$$
-/
theorem newton_three_eq_of_newton_form (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    f z = f x + (z - x) * ((f y - f x) / (y - x)) + (z - x) * (z - y) * newton f ![x, y, z] := by
  rw [newton_three_eq]
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h2 : x - z ≠ 0 := sub_ne_zero.2 hxz
  have h3 : y - z ≠ 0 := sub_ne_zero.2 hyz
  have h1' : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have h2' : z - x ≠ 0 := sub_ne_zero.2 hxz.symm
  have h3' : z - y ≠ 0 := sub_ne_zero.2 hyz.symm
  field_simp
  ring

end Explicit

/-- Let $f$ have the continuous derivative $f'$ on $\mathbb{R}$, and let $s \neq t$. Then the Newton
divided difference $f[t, s]$ equals `DividedDifference.firstOrder f' s t`. So the two sections
describe the same object. -/
theorem newton_pair (hf : ∀ x, HasDerivAt f (f' x) x) (hc' : Continuous f') {s t : ℝ}
    (hst : s ≠ t) : newton f ![t, s] = firstOrder f' s t := by
  have hne : s - t ≠ 0 := sub_ne_zero.2 hst
  have hval : newton f ![t, s] = (f s - f t) / (s - t) := newton_two_eq f hst.symm
  rw [hval, sub_eq_mul_firstOrder hf hc' s t]
  field_simp

/-! ### The mean value form of the second divided difference -/

section MeanValueForm

variable {f f₁ f₂ : ℝ → ℝ} {x y z : ℝ}

/-- **The mean value form of the second divided difference, for sorted nodes.** Let
$S \subseteq \mathbb{R}$ be convex, let $f$ have the derivative $f_1$ and $f_1$ the derivative
$f_2$ at every point of $S$, and let $x < y < z$ with $x, z \in S$. Then there is $\xi \in S$
with
$$f[x, y, z] = \frac{f_2(\xi)}{2}.$$
This is in §3.2 of [han2009theoretical].

The proof applies Rolle's theorem twice to $f$ minus its Newton interpolant $f(x) + (t - x) f[x,
y] + (t - x)(t - y) f[x, y, z]$, whose second derivative is $f_2 - 2 f[x, y, z]$. No node is
distinguished here, so `DividedDifference.newton_three_eq_newton_two_dslope` cannot reduce the
order. -/
theorem exists_newton_three_eq_of_lt {s : Set ℝ} (hs : Convex ℝ s)
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z)
    (hf : ∀ u ∈ s, HasDerivAt f (f₁ u) u) (hf₁ : ∀ u ∈ s, HasDerivAt f₁ (f₂ u) u) :
    ∃ ξ ∈ s, newton f ![x, y, z] = f₂ ξ / 2 := by
  have hsub : Icc x z ⊆ s := hs.ordConnected.out hx hz
  set c : ℝ := newton f ![x, y, z] with hc
  set b : ℝ := (f y - f x) / (y - x) with hb
  set E : ℝ → ℝ := fun t => f t - (f x + (t - x) * b + (t - x) * (t - y) * c) with hE
  set E₁ : ℝ → ℝ := fun t => f₁ t - (b + ((t - x) + (t - y)) * c) with hE₁
  have hxz : x < z := hxy.trans hyz
  have hEd : ∀ u ∈ s, HasDerivAt E (E₁ u) u := fun u hu => by
    have hd1 : HasDerivAt (fun t : ℝ => (t - x) * b) b u := by
      simpa using ((hasDerivAt_id u).sub_const x).mul_const b
    have hd2 : HasDerivAt (fun t : ℝ => (t - x) * (t - y) * c) ((u - y + (u - x)) * c) u := by
      simpa using (((hasDerivAt_id u).sub_const x).mul
        ((hasDerivAt_id u).sub_const y)).mul_const c
    have h := (hf u hu).sub (((hasDerivAt_const u (f x)).add hd1).add hd2)
    simp only [hE, hE₁]
    exact h.congr_deriv (by ring)
  have hE₁d : ∀ u ∈ s, HasDerivAt E₁ (f₂ u - 2 * c) u := fun u hu => by
    have hd : HasDerivAt (fun t : ℝ => b + (t - x + (t - y)) * c) (2 * c) u := by
      have h0 := ((((hasDerivAt_id u).sub_const x).add
        ((hasDerivAt_id u).sub_const y)).mul_const c).const_add b
      exact h0.congr_deriv (by ring)
    simp only [hE₁]
    exact ((hf₁ u hu).sub hd).congr_deriv (by ring)
  have hEx : E x = 0 := by simp [hE]
  have hEy : E y = 0 := by
    have hyx : y - x ≠ 0 := sub_ne_zero.2 hxy.ne'
    simp only [hE, hb, sub_self, mul_zero, zero_mul, add_zero]
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hyx, mul_one]
    ring
  have hEz : E z = 0 := by
    have h := newton_three_eq_of_newton_form (f := f) hxy.ne hxz.ne hyz.ne
    simp only [hE, hb, hc]
    linarith
  have hsubxy : Icc x y ⊆ s := (Icc_subset_Icc le_rfl hyz.le).trans hsub
  have hsubyz : Icc y z ⊆ s := (Icc_subset_Icc hxy.le le_rfl).trans hsub
  have hcont : ∀ t : Set ℝ, t ⊆ s → ContinuousOn E t :=
    fun t ht u hu => (hEd u (ht hu)).continuousAt.continuousWithinAt
  obtain ⟨ξ₁, hξ₁, h1⟩ := exists_hasDerivAt_eq_zero hxy (hcont _ hsubxy) (hEx.trans hEy.symm)
    fun u hu => hEd u (hsubxy (Ioo_subset_Icc_self hu))
  obtain ⟨ξ₂, hξ₂, h2⟩ := exists_hasDerivAt_eq_zero hyz (hcont _ hsubyz) (hEy.trans hEz.symm)
    fun u hu => hEd u (hsubyz (Ioo_subset_Icc_self hu))
  have hξ₁₂ : ξ₁ < ξ₂ := hξ₁.2.trans hξ₂.1
  have hsub₁₂ : Icc ξ₁ ξ₂ ⊆ s := (Icc_subset_Icc hξ₁.1.le hξ₂.2.le).trans hsub
  have hcont₁ : ContinuousOn E₁ (Icc ξ₁ ξ₂) :=
    fun u hu => (hE₁d u (hsub₁₂ hu)).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, h3⟩ := exists_hasDerivAt_eq_zero hξ₁₂ hcont₁ (h1.trans h2.symm)
    fun u hu => hE₁d u (hsub₁₂ (Ioo_subset_Icc_self hu))
  exact ⟨ξ, hsub ⟨(hξ₁.1.trans hξ.1).le, (hξ.2.trans hξ₂.2).le⟩, by linarith⟩

/-- **The mean value form of the second divided difference.** Let $S \subseteq \mathbb{R}$ be
convex, let $f$ have the derivative $f_1$ and $f_1$ the derivative $f_2$ at every point of $S$,
and let $x$, $y$ and $z$ be distinct points of $S$. Then there is $\xi \in S$ with
$$f[x, y, z] = \frac{f_2(\xi)}{2}.$$

The proof is `DividedDifference.exists_newton_three_eq_of_lt` after sorting the nodes, by the
symmetry of `DividedDifference.newton` in its nodes. -/
theorem exists_newton_three_eq {s : Set ℝ} (hs : Convex ℝ s)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hf : ∀ u ∈ s, HasDerivAt f (f₁ u) u) (hf₁ : ∀ u ∈ s, HasDerivAt f₁ (f₂ u) u) :
    ∃ ξ ∈ s, newton f ![x, y, z] = f₂ ξ / 2 := by
  rcases hxy.lt_or_gt with h1 | h1
  · rcases hyz.lt_or_gt with h2 | h2
    · exact exists_newton_three_eq_of_lt hs hx hz h1 h2 hf hf₁
    · rcases hxz.lt_or_gt with h3 | h3
      · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hx hy h3 h2 hf hf₁
        exact ⟨ξ, hξ, by rw [newton_three_swap₂]; exact hv⟩
      · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hz hy h3 h1 hf hf₁
        exact ⟨ξ, hξ, by rw [newton_three_swap₂, newton_three_swap₁]; exact hv⟩
  · rcases hyz.lt_or_gt with h2 | h2
    · rcases hxz.lt_or_gt with h3 | h3
      · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hy hz h1 h3 hf hf₁
        exact ⟨ξ, hξ, by rw [newton_three_swap₁]; exact hv⟩
      · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hy hx h2 h3 hf hf₁
        exact ⟨ξ, hξ, by rw [newton_three_swap₁, newton_three_swap₂]; exact hv⟩
    · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hz hx h2 h1 hf hf₁
      exact ⟨ξ, hξ, by
        rw [newton_three_swap₂, newton_three_swap₁, newton_three_swap₂]; exact hv⟩

end MeanValueForm

end DividedDifference
