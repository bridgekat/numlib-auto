/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots

/-!
# Horner's scheme and synthetic division

Let $p = a_n X^n + \dots + a_1 X + a_0$ be a polynomial of degree $n$ and let $z$ be a point.
**Horner's scheme** evaluates $p(z)$ in the nested form $a_0 + z(a_1 + z(a_2 + \dots))$: it sets
$b_n = a_n$ and $b_k = a_k + b_{k+1} z$ for $k = n - 1, \dots, 0$, and then $b_0 = p(z)$. This
module encodes the scheme as a left fold over the coefficient list $[a_n, \dots, a_0]$ of Mathlib,
and proves that it evaluates the polynomial. The intermediate values $b_n, \dots, b_1$ are the
coefficients of the quotient $q(\cdot\,; z)$ of $p$ by $X - z$, and $b_0 = p(z)$ is the remainder:
this is **synthetic division**, $p = (X - z)\, q(\cdot\,; z) + p(z)$. The presentation follows
[quarteroni2000numerical], §6.4.1, equations (6.25)–(6.26); see also [kress1998numerical], §6.3, and
[higham2002accuracy], §5.1.

The module also proves two facts that Mathlib does not have. The first is $q(z; z) = p'(z)$, which
lets the Newton–Horner method of [quarteroni2000numerical], (6.29), compute $p'(z)$ by a second
synthetic division. The second is the deflation identity: at a root $r$ of $p \neq 0$, the roots of
$p$, with multiplicities, are the roots of $q(\cdot\,; r)$ together with $r$. The deflation loop of
[quarteroni2000numerical], §6.4.1, relies on it.

## Main definitions

* `Polynomial.hornerEval`: Horner's scheme $b \leftarrow a_k + b z$ over a list of coefficients,
  leading coefficient first.
* `Polynomial.hornerScan`: the list $[b_n, \dots, b_0]$ of all intermediate values of Horner's
  scheme.
* `NewtonHorner.step`: the Newton–Horner step $z \mapsto z - p(z) / q(z; z)$.

## Main results

* `Polynomial.hornerEval_coeffList`: Horner's scheme over the coefficient list of $p$ gives $p(z)$.
* `Polynomial.hornerScan_coeffList`: for $p \neq 0$, the list of intermediate values is the
  coefficient list of $q(\cdot\,; z)$ followed by $p(z)$.
* `Polynomial.eq_X_sub_C_mul_divByMonic_add_C_eval`: synthetic division,
  $p = (X - z)\, q(\cdot\,; z) + p(z)$.
* `Polynomial.eval_divByMonic_X_sub_C_self`: $q(z; z) = p'(z)$.
* `Polynomial.roots_divByMonic_X_sub_C`: at a root $r$ of $p \neq 0$, the roots of $p$ are the roots
  of $q(\cdot\,; r)$ together with $r$.
* `NewtonHorner.step_eq`: the Newton–Horner step is the Newton step $z - p(z)/p'(z)$.

## Implementation notes

* The coefficient list is Mathlib's `Polynomial.coeffList`, which lists the coefficients from the
  leading one down to the constant one. The quotient $q(\cdot\,; z)$, the associated polynomial of
  [quarteroni2000numerical], has no separate definition: it is `p /ₘ (X - C z)`.
* The recurrence for the coefficients of the quotient is Mathlib's
  `Polynomial.coeff_divByMonic_X_sub_C_rec`. Synthetic division follows from Mathlib's
  `Polynomial.modByMonic_add_div` and `Polynomial.modByMonic_X_sub_C_eq_C_eval`.
* Descartes' rule of signs and Cauchy's bound, the localization results that the source states with
  Horner's scheme, are Mathlib's `Polynomial.roots_countP_pos_le_signVariations` and
  `Polynomial.IsRoot.norm_lt_cauchyBound`. The parity clause of Descartes' rule is in
  `Numlib.RingTheory.Polynomial.RuleOfSigns`.
-/

open Polynomial

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R]

/-- **Horner's scheme** over a list of coefficients $[a_n, \dots, a_0]$, leading coefficient first.
Starting from $b = 0$, it performs $b \leftarrow a_k + b z$ for each $a_k$ in turn and returns
the final $b$, which is $\sum_k a_k z^k$.

This is (6.25)–(6.26) of [quarteroni2000numerical]. The order of the list is that of Mathlib's
`Polynomial.coeffList`. The empty list gives $0$. -/
def hornerEval (l : List R) (z : R) : R := l.foldl (fun b a => a + b * z) 0

/-- Horner's scheme over the empty list gives $0$. -/
@[simp]
theorem hornerEval_nil (z : R) : hornerEval ([] : List R) z = 0 := rfl

/-- Horner's scheme started from $b_0$ instead of $0$: for a list $l$ of length $m$ and any $b_0$,
$z$, the fold of $b \leftarrow a + b z$ over $l$ from $b_0$ equals $b_0 z^m$ plus Horner's
scheme over $l$ at $z$. -/
theorem foldl_horner_eq (l : List R) (z b₀ : R) :
    l.foldl (fun b a => a + b * z) b₀ = b₀ * z ^ l.length + hornerEval l z := by
  induction l generalizing b₀ with
  | nil => simp [hornerEval]
  | cons a l ih =>
    simp only [List.foldl_cons, List.length_cons, hornerEval] at ih ⊢
    rw [ih (a + b₀ * z), ih (a + 0 * z), pow_succ', ← mul_assoc, add_mul, zero_mul, add_zero]
    abel

/-- Horner's scheme on a list with head $a$ and tail $l$ of length $m$ is $a z^m$ plus Horner's
scheme on $l$. -/
theorem hornerEval_cons (a : R) (l : List R) (z : R) :
    hornerEval (a :: l) z = a * z ^ l.length + hornerEval l z := by
  rw [hornerEval, List.foldl_cons, foldl_horner_eq]
  simp

/-- Horner's scheme on a list $l$ followed by one more coefficient $a$ is $a + h z$, where $h$ is
Horner's scheme on $l$. -/
theorem hornerEval_append_singleton (l : List R) (a z : R) :
    hornerEval (l ++ [a]) z = a + hornerEval l z * z := by
  simp [hornerEval, List.foldl_append]

/-- For a sequence $c_0, c_1, \dots$ and $n \in \mathbb{N}$, Horner's scheme over the list
$[c_n, \dots, c_0]$ at $z$ is the sum $\sum_{i=0}^{n} c_i z^i$. -/
theorem hornerEval_map_reverse_range (c : ℕ → R) (z : R) (n : ℕ) :
    hornerEval (((List.range (n + 1)).reverse.map c)) z =
      ∑ i ∈ Finset.range (n + 1), c i * z ^ i := by
  induction n with
  | zero => simp [hornerEval]
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, hornerEval_cons, ih, Finset.sum_range_succ _ (n + 1), add_comm]
    simp

/-- **Horner's scheme evaluates the polynomial.** For a polynomial $p$ over a semiring and any point
$z$, Horner's scheme over the coefficient list of $p$ gives $p(z)$.

This is (6.25)–(6.26) of [quarteroni2000numerical]. The coefficient list is
`Polynomial.coeffList`, leading coefficient first. -/
theorem hornerEval_coeffList (p : R[X]) (z : R) : hornerEval p.coeffList z = p.eval z := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [coeffList, withBotSucc_degree_eq_natDegree_add_one hp, hornerEval_map_reverse_range,
      eval_eq_sum_range]

/-- The **list of intermediate values of Horner's scheme**: for a list $[a_n, \dots, a_0]$, it is
$[b_n, b_{n-1}, \dots, b_0]$ with $b_n = a_n$ and $b_k = a_k + b_{k+1} z$.

This is the output vector $b$ of Program 52 of [quarteroni2000numerical]. It is the list of
`List.scanl` without its initial value $0$. -/
def hornerScan (l : List R) (z : R) : List R := (l.scanl (fun b a => a + b * z) 0).tail

/-- The list of intermediate values of Horner's scheme has one entry for each coefficient. -/
@[simp]
theorem length_hornerScan (l : List R) (z : R) : (hornerScan l z).length = l.length := by
  simp [hornerScan, List.length_tail, List.length_scanl]

/-- For $i$ less than the length of the list $l$, entry $i$ (from $0$) of the list of intermediate
values is Horner's scheme on the first $i + 1$ entries of $l$. -/
theorem getElem_hornerScan (l : List R) (z : R) {i : ℕ} (h : i < l.length) :
    (hornerScan l z)[i]'(by simpa using h) = hornerEval (l.take (i + 1)) z := by
  simp [hornerScan, List.getElem_tail, List.getElem_scanl, hornerEval]

/-- For a nonempty list $l$, the last entry of the list of intermediate values is Horner's scheme on
all of $l$. For the coefficient list of $p$, this is the value $b_0 = p(z)$ of
[quarteroni2000numerical]. -/
theorem getLast?_hornerScan (l : List R) (z : R) (hl : l ≠ []) :
    (hornerScan l z).getLast? = some (hornerEval l z) := by
  have hlen : 0 < l.length := List.length_pos_iff.2 hl
  rw [List.getLast?_eq_getElem?, length_hornerScan, List.getElem?_eq_getElem (by simpa using hlen),
    getElem_hornerScan l z (by omega), Nat.sub_add_cancel hlen, List.take_length]

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

/-- **Synthetic division.** Let $p$ be a polynomial over a commutative ring and let $z$ be a point.
Then
$$p = (X - z)\, q(\cdot\,; z) + p(z),$$
where $q(\cdot\,; z)$ is the quotient of $p$ by the monic polynomial $X - z$.

This is the display after (6.28) in §6.4.1 of [quarteroni2000numerical], where $q(\cdot\,; z)$
is the associated polynomial and the remainder $b_0$ is $p(z)$. The quotient is
`p /ₘ (X - C z)`. The proof combines Mathlib's `Polynomial.modByMonic_add_div` and
`Polynomial.modByMonic_X_sub_C_eq_C_eval`. -/
theorem eq_X_sub_C_mul_divByMonic_add_C_eval (p : R[X]) (z : R) :
    p = (X - C z) * (p /ₘ (X - C z)) + C (p.eval z) := by
  conv_lhs => rw [← p.modByMonic_add_div (X - C z), modByMonic_X_sub_C_eq_C_eval]
  ring

/-- The constant term of synthetic division: $p(z) = a_0 + z\, b_1$, where $a_0$ is the constant
coefficient of $p$ and $b_1$ is the constant coefficient of the quotient $q(\cdot\,; z)$ of $p$
by $X - z$. This is the last step of the recurrence (6.26) of [quarteroni2000numerical]. -/
theorem eval_eq_coeff_zero_add_mul_coeff_divByMonic (p : R[X]) (z : R) :
    p.eval z = p.coeff 0 + z * (p /ₘ (X - C z)).coeff 0 := by
  have h := congrArg (fun q => q.coeff 0) (eq_X_sub_C_mul_divByMonic_add_C_eval p z)
  simp only [coeff_add, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub,
    neg_mul] at h
  rw [h]
  ring

/-- The **derivative is the value of the associated polynomial**. Let $p$ be a polynomial over a
commutative ring, let $z$ be a point, and let $q(\cdot\,; z)$ be the quotient of $p$ by $X - z$.
Then
$$q(z; z) = p'(z).$$

This is used in §6.4.2 of [quarteroni2000numerical]. It follows from $p' = q + (X - z) q'$. It
lets one synthetic division of the quotient give the derivative for Newton's method. -/
theorem eval_divByMonic_X_sub_C_self (p : R[X]) (z : R) :
    (p /ₘ (X - C z)).eval z = p.derivative.eval z := by
  have h := congrArg (fun q => q.derivative.eval z) (eq_X_sub_C_mul_divByMonic_add_C_eval p z)
  simp only [derivative_add, derivative_mul, derivative_X_sub_C, derivative_C, eval_add, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, one_mul] at h
  exact h.symm

/-- Let $p \neq 0$ have degree $n$. For $i \le n$, entry $i$ (from $0$) of the coefficient list
`Polynomial.coeffList p` is the coefficient of $X^{n - i}$ in $p$. -/
theorem getElem_coeffList {p : R[X]} (hp : p ≠ 0) {i : ℕ} (hi : i < p.natDegree + 1) :
    p.coeffList[i]'(by simp [coeffList, withBotSucc_degree_eq_natDegree_add_one hp, hi]) =
      p.coeff (p.natDegree - i) := by
  simp [coeffList, withBotSucc_degree_eq_natDegree_add_one hp, List.getElem_reverse]

/-- Let $p$ have degree $n \ge 1$. Then the quotient of $p$ by $X - z$ is nonzero and has degree
$n - 1$. -/
theorem natDegree_divByMonic_X_sub_C {p : R[X]} (hp : 0 < p.natDegree) (z : R) :
    p /ₘ (X - C z) ≠ 0 ∧ (p /ₘ (X - C z)).natDegree = p.natDegree - 1 := by
  have hnt : Nontrivial R := ⟨⟨p.leadingCoeff, 0,
    leadingCoeff_ne_zero.2 (ne_zero_of_natDegree_gt hp)⟩⟩
  refine ⟨fun h => ?_, by rw [natDegree_divByMonic _ (monic_X_sub_C z), natDegree_X_sub_C]⟩
  rw [divByMonic_eq_zero_iff (monic_X_sub_C z)] at h
  have := natDegree_lt_natDegree (ne_zero_of_natDegree_gt hp) h
  rw [natDegree_X_sub_C] at this
  omega

/-- **The intermediate values of Horner's scheme are the coefficients of the quotient.** Let $p$
have degree $n$ and let $i < n$. Then Horner's scheme on the first $i + 1$ coefficients
$a_n, \dots, a_{n-i}$ of $p$ at $z$ is the coefficient of $X^{n-1-i}$ in the quotient
$q(\cdot\,; z)$ of $p$ by $X - z$.

The proof is by induction on $i$, with Mathlib's recurrence
`Polynomial.coeff_divByMonic_X_sub_C_rec`. -/
theorem hornerEval_take_coeffList (p : R[X]) (z : R) {i : ℕ} (hi : i < p.natDegree) :
    hornerEval (p.coeffList.take (i + 1)) z = (p /ₘ (X - C z)).coeff (p.natDegree - 1 - i) := by
  have hp : p ≠ 0 := ne_zero_of_natDegree_gt hi
  obtain ⟨-, hdeg⟩ := natDegree_divByMonic_X_sub_C (Nat.zero_lt_of_lt hi) z
  have hlen : p.coeffList.length = p.natDegree + 1 := by
    simp [coeffList, withBotSucc_degree_eq_natDegree_add_one hp]
  induction i with
  | zero =>
    have hq0 : (p /ₘ (X - C z)).coeff p.natDegree = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      getElem_coeffList hp (by omega), Nat.sub_zero]
    simp only [Option.toList_some]
    rw [hornerEval_cons, coeff_divByMonic_X_sub_C_rec, Nat.sub_zero, Nat.sub_add_cancel hi, hq0]
    simp
  | succ i ih =>
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      hornerEval_append_singleton, ih (by omega), getElem_coeffList hp (by omega),
      coeff_divByMonic_X_sub_C_rec (n := p.natDegree - 1 - (i + 1)),
      show p.natDegree - 1 - (i + 1) + 1 = p.natDegree - (i + 1) by omega,
      show p.natDegree - 1 - i = p.natDegree - (i + 1) by omega]
    ring

/-- **Synthetic division computes the quotient and the remainder.** Let $p \neq 0$ be a polynomial
over a commutative ring and let $z$ be a point. Then the list $[b_n, \dots, b_0]$ of
intermediate values of Horner's scheme over the coefficients of $p$ is the coefficient list of
the quotient $q(\cdot\,; z)$ of $p$ by $X - z$, followed by $b_0 = p(z)$.

This is the algorithm (6.26) of [quarteroni2000numerical], §6.4.1. For a constant $p$, the
quotient is $0$, its coefficient list is empty, and the list of intermediate values is $[p(z)]$. -/
theorem hornerScan_coeffList {p : R[X]} (hp : p ≠ 0) (z : R) :
    hornerScan p.coeffList z = (p /ₘ (X - C z)).coeffList ++ [p.eval z] := by
  have hlen : p.coeffList.length = p.natDegree + 1 := by
    simp [coeffList, withBotSucc_degree_eq_natDegree_add_one hp]
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · -- a constant: the quotient is `0`
    have hnt : Nontrivial R := ⟨⟨p.leadingCoeff, 0, leadingCoeff_ne_zero.2 hp⟩⟩
    have hq : p /ₘ (X - C z) = 0 := by
      rw [divByMonic_eq_zero_iff (monic_X_sub_C z), degree_X_sub_C, degree_eq_natDegree hp, h0]
      exact zero_lt_one
    have hc : p.coeff 0 ≠ 0 := fun h => hp (by rw [eq_C_of_natDegree_eq_zero h0, h, C_0])
    rw [hq, coeffList_zero, List.nil_append, eq_C_of_natDegree_eq_zero h0, coeffList_C hc, eval_C]
    simp [hornerScan]
  · obtain ⟨hq0, hqdeg⟩ := natDegree_divByMonic_X_sub_C hpos z
    have hqlen : (p /ₘ (X - C z)).coeffList.length = p.natDegree := by
      rw [coeffList, List.length_map, List.length_reverse, List.length_range,
        withBotSucc_degree_eq_natDegree_add_one hq0, hqdeg]
      omega
    refine List.ext_getElem (by simp [hlen, hqlen]) fun i hi hi' => ?_
    rw [length_hornerScan, hlen] at hi
    rw [getElem_hornerScan _ _ (by omega)]
    rcases lt_or_ge i p.natDegree with hlt | hge
    · rw [List.getElem_append_left (by omega), getElem_coeffList hq0 (by omega), hqdeg,
        hornerEval_take_coeffList p z hlt]
    · obtain rfl : i = p.natDegree := by omega
      rw [List.getElem_append_right (by omega), ← hlen, List.take_length, hornerEval_coeffList]
      simp [hqlen]

end CommRing

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Deflation removes one copy of the root.** Let $p \neq 0$ be a polynomial over an integral
domain and let $r$ be a root of $p$. Then the multiset of roots of $p$ is the multiset of roots
of the quotient $q(\cdot\,; r)$ of $p$ by $X - r$, with one more copy of $r$. Thus the remaining
roots of $p$, with multiplicities, are the roots of the deflated polynomial $q(\cdot\,; r)$.

This is the deflation step of [quarteroni2000numerical], §6.4.1. The roots are
`Polynomial.roots`. -/
theorem roots_divByMonic_X_sub_C {p : R[X]} (hp : p ≠ 0) {r : R} (hr : p.IsRoot r) :
    p.roots = (p /ₘ (X - C r)).roots + {r} := by
  have h := mul_divByMonic_eq_iff_isRoot.2 hr
  conv_lhs => rw [← h]
  rw [roots_mul (h.symm ▸ hp), roots_X_sub_C, add_comm]

end Domain

end Polynomial

namespace NewtonHorner

variable {K : Type*} [Field K]

/-- The **Newton–Horner step**: for a polynomial $p$ over a field $K$ and a point $z \in K$,
$$z \mapsto z - \frac{p(z)}{q(z; z)},$$
where $q(\cdot\,; z)$ is the quotient of $p$ by $X - z$. The value $q(z; z) = p'(z)$ comes from
a second synthetic division. If $q(z; z) = 0$, the step returns $z$, because division by zero
gives $0$.

This is (6.29) of [quarteroni2000numerical]. The source works over $\mathbb{R}$ or $\mathbb{C}$
and recommends complex arithmetic for complex roots; the definition is stated over any field. -/
noncomputable def step (p : K[X]) (z : K) : K := z - p.eval z / (p /ₘ (X - C z)).eval z

/-- The Newton–Horner step is the Newton step for $p$: for a polynomial $p$ over a field and a point
$z$,
$$\operatorname{step}(p, z) = z - \frac{p(z)}{p'(z)}.$$
Hence every theorem about Newton's method for the function $x \mapsto p(x)$ applies to it. The
proof uses `Polynomial.eval_divByMonic_X_sub_C_self`. -/
theorem step_eq (p : K[X]) (z : K) : step p z = z - p.eval z / p.derivative.eval z := by
  rw [step, Polynomial.eval_divByMonic_X_sub_C_self]

end NewtonHorner
