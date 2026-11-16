/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases
import Numlib.FloatingPoint.System

/-!
# Quarteroni, Sacco and Saleri, Section 2.5: Machine Representation of Numbers

This module formalizes Section 2.5 of [quarteroni2000numerical]: the positional system (Section
2.5.1), the floating-point number system $\mathbb{F}(\beta, t, L, U)$ (Section 2.5.2), the
distribution of its numbers (Section 2.5.3), the parameters of IEC 559 arithmetic (Section 2.5.4),
rounding and Property 2.1 (Section 2.5.5), and the machine operations (Section 2.5.6). The book
defines $\mathbb{F}(\beta, t, L, U)$ as the set of $0$ and of the numbers
$(-1)^s \beta^e \sum_{i=1}^t a_i \beta^{-i}$ with digits $0 \le a_i \le \beta - 1$, $a_1 \neq 0$,
and exponent $L \le e \le U$. The unit roundoff is $u = \frac{1}{2} \beta^{1-t}$, and rounding to
nearest satisfies $fl(x) = x(1 + \delta)$ with $|\delta| \le u$ (Property 2.1).

All results specialize the backbone module `Numlib.FloatingPoint.System` to $\mathbb{R}$, and to
$\mathbb{Q}$ for the two examples that are decided by computation. The module restates $\mathbb{F}$
in the digit form of the book and proves that it equals the integer-mantissa form
$\pm m \beta^{e-t}$ of the backbone. It also restates the rounding (2.32) as the digit rule of the
book and identifies it with `FloatingPoint.System.round`. The facts that the text asserts without a
number (the cardinality of $\mathbb{F}$, the smallest de-normalized number, the spacing of the
numbers, the machine epsilon $\varepsilon_M$ as the gap above $1$, the commutativity and the failure
of associativity of $\oplus$) have descriptive names.

## Main definitions

* Section 2.5.2, `QuarteroniSaccoSaleri.Chapter02.floatingPointNumbers`: the set
  $\mathbb{F}(\beta, t, L, U)$ in the digit form of the book.
* Example 2.11, `QuarteroniSaccoSaleri.Chapter02.example_2_11_system`: the system
  $\mathbb{F}(2, 3, -1, 2)$.
* Section 2.5.6, `QuarteroniSaccoSaleri.Chapter02.machineOp`: the machine operation
  $fl(fl(x) \circ fl(y))$.
* Section 2.5.6, `QuarteroniSaccoSaleri.Chapter02.decimalSystem`: the decimal system
  $\mathbb{F}(10, 2, -1, 2)$.

## Main results

* Section 2.5.1, `QuarteroniSaccoSaleri.Chapter02.positionalDensity`: numbers with finitely many
  digits in base $\beta$ are dense in $\mathbb{R}$.
* Section 2.5.2, `QuarteroniSaccoSaleri.Chapter02.floatingPointNumbers_eq`: the digit form of
  $\mathbb{F}$ is the integer-mantissa form of the backbone.
* Equation (2.30), `QuarteroniSaccoSaleri.Chapter02.equation_2_30`: $x_{min} \le |x| \le x_{max}$
  for every nonzero $x \in \mathbb{F}$.
* Section 2.5.2, `QuarteroniSaccoSaleri.Chapter02.cardFloatingPoint`: $\mathbb{F}$ has
  $2(\beta - 1)\beta^{t-1}(U - L + 1) + 1$ elements.
* Section 2.5.2, `QuarteroniSaccoSaleri.Chapter02.denormalizedMin`: the smallest positive
  de-normalized number is $\beta^{L-t}$.
* Example 2.11, `QuarteroniSaccoSaleri.Chapter02.example_2_11`: the sixteen positive numbers of
  $\mathbb{F}(2, 3, -1, 2)$.
* Example 2.11, `QuarteroniSaccoSaleri.Chapter02.example_2_11_bounds`: $x_{min} = 1/4$,
  $x_{max} = 7/2$, and $33$ numbers in all.
* Example 2.11, `QuarteroniSaccoSaleri.Chapter02.example_2_11_denormalized`: the positive
  de-normalized numbers $3/16$, $1/8$ and $1/16$.
* Section 2.5.3, `QuarteroniSaccoSaleri.Chapter02.spacing`: the numbers of one exponent are equally
  spaced, and the spacing near $x$ lies between $\beta^{-1} \varepsilon_M |x|$ and
  $\varepsilon_M |x|$.
* Equation (2.31), `QuarteroniSaccoSaleri.Chapter02.equation_2_31`: the relative spacing is $1/m$
  for the mantissa $m$ (wobbling precision).
* Section 2.5.3, `QuarteroniSaccoSaleri.Chapter02.machineEps_isLeast`: $\varepsilon_M$ is the least
  $\delta > 0$ with $1 + \delta \in \mathbb{F}$.
* Section 2.5.4, `QuarteroniSaccoSaleri.Chapter02.ieeeUnitRoundoff`: the parameters and unit
  roundoffs of IEC 559 single and double precision.
* Equation (2.32), `QuarteroniSaccoSaleri.Chapter02.equation_2_32`: rounding to nearest is the digit
  rule of the book.
* Section 2.5.5, `QuarteroniSaccoSaleri.Chapter02.fl_eq_self_of_mem`: $fl(x) = x$ for
  $x \in \mathbb{F}$.
* Section 2.5.5, `QuarteroniSaccoSaleri.Chapter02.fl_mono`: rounding is monotone.
* Remark 2.2, `QuarteroniSaccoSaleri.Chapter02.remark_2_2`: overflow and underflow.
* Property 2.1, `QuarteroniSaccoSaleri.Chapter02.property_2_1`: $fl(x) = x(1 + \delta)$ with
  $|\delta| \le u$ for $x_{min} \le |x| \le x_{max}$.
* Equation (2.34), `QuarteroniSaccoSaleri.Chapter02.equation_2_34`: $u = \frac{1}{2} \beta^{1-t} =
  \frac{1}{2} \varepsilon_M$.
* Property 2.1, `QuarteroniSaccoSaleri.Chapter02.property_2_1_chop`: chopping satisfies the same
  bound with $\varepsilon_M$ in place of $u$.
* Equation (2.35), `QuarteroniSaccoSaleri.Chapter02.equation_2_35`: the relative error of rounding
  is at most $u$.
* Section 2.5.5, `QuarteroniSaccoSaleri.Chapter02.roundAbsError`: the absolute error of rounding is
  at most $\frac{1}{2} \beta^{e-t}$.
* Section 2.5.6, `QuarteroniSaccoSaleri.Chapter02.machineOp_eq`: the machine operation is the
  backbone's `FloatingPoint.System.op`.
* Equation (2.36), `QuarteroniSaccoSaleri.Chapter02.equation_2_36`: each machine operation on
  numbers of $\mathbb{F}$ has relative error at most $u$.
* Section 2.5.6, `QuarteroniSaccoSaleri.Chapter02.machineOp_comm`: the machine sum and the machine
  product are commutative.
* Section 2.5.6, `QuarteroniSaccoSaleri.Chapter02.machineAdd_not_assoc`: the machine sum is not
  associative.

## Conventions

* A floating-point system is a `FloatingPoint.System`, with base $\beta \ge 2$, $t \ge 1$ digits and
  exponent range $L \le U$. The set $\mathbb{F}$ is `FloatingPoint.System.numbers`, and $fl$ is
  `FloatingPoint.System.round`.
* The exponent $e$ of a nonzero $x$ is the integer with $\beta^{e-1} \le |x| < \beta^e$, that is,
  the exponent of the mantissa convention (2.29) $x = \pm (0.a_1 a_2 \dots) \times \beta^e$. It is
  `FloatingPoint.System.exponent`.

## Implementation notes

* The rounding `FloatingPoint.System.round` is defined on all of $\mathbb{R}$, without a restriction
  of the exponent range. Overflow is the statement that the result is not in $\mathbb{F}$ (Remark
  2.2).
* Property 2.1 keeps the range hypothesis of the book, although the bound on $\delta$ holds without
  it in the backbone.

## Deviations from the source

* **Section 2.5.2, the smallest de-normalized number** (reading). The statement assumes $t \ge 2$,
  which the book leaves implicit. See `QuarteroniSaccoSaleri.Chapter02.denormalizedMin`.
* **Section 2.5.3, the spacing** (reading). The statement uses the mantissa convention (2.29), where
  the book's sentence uses the convention $a_1.a_2 \dots \times \beta^e$. See
  `QuarteroniSaccoSaleri.Chapter02.spacing`.
* **Section 2.5.3, the machine epsilon** (reading). "The smallest number of $\mathbb{F}$ such that
  $1 + \varepsilon_M > 1$" is read as the least $\delta > 0$ with $1 + \delta \in \mathbb{F}$, and
  the statement assumes $t \ge 2$ and $L \le 1 \le U$. See
  `QuarteroniSaccoSaleri.Chapter02.machineEps_isLeast`.
* **Remark 2.2** (reading). "$fl(x)$ is not defined" is read as "$fl(x)$ is not in $\mathbb{F}$",
  with the threshold $\beta^U$ in place of $x_{max}$. See
  `QuarteroniSaccoSaleri.Chapter02.remark_2_2`.
* **Equation (2.36)** (reading). The additional assumption on the round digit that the book requires
  for the subtraction holds automatically, because the exact result is rounded. See
  `QuarteroniSaccoSaleri.Chapter02.equation_2_36`.

## Not formalized

* **Example 2.10** (a numeral written in two bases).
* **Remark 2.3** (the MATLAB constant `eps`).
* **Remark 2.4** (the closed arithmetic of IEC 559, NaN, and Table 2.3).
* **Tables 2.1 and 2.2.**
* **Section 2.5.6, the operation counts and the discussion of the round digit in hardware.**
-/

open Finset FloatingPoint

namespace QuarteroniSaccoSaleri.Chapter02

/-! ### §2.5.1 The positional system -/

/-- **Section 2.5.1** of [quarteroni2000numerical], finite positional expansions are dense. Let
$\beta \ge 2$ be an integer, let $x \in \mathbb{R}$ and let $\varepsilon > 0$. Then there are
$m \in \mathbb{Z}$ and $k \in \mathbb{N}$ with
$$|m \beta^{-k} - x| < \varepsilon.$$
So "any real number can be approximated by numbers having a finite representation". -/
theorem positionalDensity {β : ℕ} (hβ : 2 ≤ β) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℤ) (k : ℕ), |m * (β : ℝ) ^ (-(k : ℤ)) - x| < ε :=
  exists_int_mul_zpow_sub_abs_lt hβ x hε

/-! ### §2.5.2 The floating-point number system -/

/-- **Section 2.5.2** of [quarteroni2000numerical], the set $\mathbb{F}(\beta, t, L, U)$. For
natural numbers $\beta, t$ and integers $L, U$, this is the set
$$\{0\} \cup \Bigl\{x \in \mathbb{R} : x = (-1)^s \beta^e \sum_{i=1}^t a_i \beta^{-i}\Bigr\}$$
of the numbers with a sign $s \in \{0, 1\}$, $t$ significant digits $0 \le a_i \le \beta - 1$
with $a_1 \neq 0$, and an exponent $L \le e \le U$.

The digits are a function `a : ℕ → ℕ`, of which only $a_1, \dots, a_t$ matter. The sign is a
`Bool`. The definition makes no hypothesis on the parameters;
`QuarteroniSaccoSaleri.Chapter02.floatingPointNumbers_eq` identifies it with the backbone's set
for a floating-point system. -/
def floatingPointNumbers (β t : ℕ) (L U : ℤ) : Set ℝ :=
  {0} ∪ {x | ∃ (s : Bool) (e : ℤ) (a : ℕ → ℕ), (∀ i ∈ Icc 1 t, a i ≤ β - 1) ∧ a 1 ≠ 0 ∧
    L ≤ e ∧ e ≤ U ∧
    x = (-1) ^ s.toNat * (β : ℝ) ^ e * ∑ i ∈ Icc 1 t, (a i : ℝ) * (β : ℝ) ^ (-(i : ℤ))}

/-- If $c_j < \beta$ for every $j < t$, then $\sum_{j < t} c_j \beta^j < \beta^t$. -/
private theorem sum_mul_pow_lt {β t : ℕ} {c : ℕ → ℕ} (hc : ∀ j < t, c j < β) :
    ∑ j ∈ range t, c j * β ^ j < β ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, pow_succ]
    have h1 := ih fun j hj => hc j (by omega)
    have h2 : c t + 1 ≤ β := hc t (by omega)
    nlinarith [Nat.zero_le (β ^ t)]

/-- For $\beta \ge 2$ and $m < \beta^t$, the base-$\beta$ expansion $m = \sum_{j < t} (\lfloor m /
\beta^j \rfloor \bmod \beta) \, \beta^j$ holds. -/
private theorem sum_div_pow_mod_mul_pow {β : ℕ} (hβ : 2 ≤ β) :
    ∀ (t m : ℕ), m < β ^ t → ∑ j ∈ range t, m / β ^ j % β * β ^ j = m := by
  intro t
  induction t with
  | zero => intro m hm; simp at hm; simp [hm]
  | succ t ih =>
    intro m hm
    rw [sum_range_succ']
    have hβ0 : 0 < β := by omega
    have hdiv : m / β < β ^ t := by
      rw [Nat.div_lt_iff_lt_mul hβ0, ← pow_succ]; exact hm
    have h := ih (m / β) hdiv
    have hre : ∑ j ∈ range t, m / β ^ (j + 1) % β * β ^ (j + 1) =
        β * ∑ j ∈ range t, m / β / β ^ j % β * β ^ j := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_succ', Nat.div_div_eq_div_mul, mul_comm β (β ^ j)]
      ring
    rw [hre, h]
    simp only [pow_zero, Nat.div_one, mul_one]
    exact Nat.div_add_mod m β

/-- A sum over the digit positions $1, \dots, t$ can be reindexed by $i \mapsto t - i$:
$\sum_{i=1}^t g(i) = \sum_{j=0}^{t-1} g(t - j)$. -/
private theorem sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] (t : ℕ) (g : ℕ → M) :
    ∑ i ∈ Icc 1 t, g i = ∑ j ∈ range t, g (t - j) := by
  refine sum_nbij' (fun i => t - i) (fun j => t - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_Icc] at hi; simp only [mem_range]; omega
  · intro j hj; simp only [mem_range] at hj; simp only [mem_Icc]; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro j hj; simp only [mem_range] at hj; omega
  · intro i hi; simp only [mem_Icc] at hi; rw [Nat.sub_sub_self hi.2]

/-- For $\beta > 0$, the value of a digit string has the two forms $\beta^e \sum_{i=1}^t a_i
\beta^{-i} = \bigl(\sum_{i=1}^t a_i \beta^{t-i}\bigr) \beta^{e-t}$. -/
private theorem zpow_mul_sum_eq {β t : ℕ} (hβ : 0 < β) (e : ℤ) (a : ℕ → ℕ) :
    (β : ℝ) ^ e * ∑ i ∈ Icc 1 t, (a i : ℝ) * (β : ℝ) ^ (-(i : ℤ)) =
      ((∑ i ∈ Icc 1 t, a i * β ^ (t - i) : ℕ) : ℝ) * (β : ℝ) ^ (e - t) := by
  have hβ' : (β : ℝ) ≠ 0 := by exact_mod_cast hβ.ne'
  rw [Nat.cast_sum, mul_sum, sum_mul]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_Icc] at hi
  rw [Nat.cast_mul, Nat.cast_pow, ← zpow_natCast, Nat.cast_sub hi.2, mul_left_comm, mul_assoc,
    ← zpow_add₀ hβ', ← zpow_add₀ hβ', show e + -(i : ℤ) = (t : ℤ) - i + (e - t) by ring]

/-- **Section 2.5.2** of [quarteroni2000numerical], the digit form and the integer-mantissa form.
Let $s$ be a floating-point system with parameters $\beta, t, L, U$. Then the digit form
$\mathbb{F}(\beta, t, L, U)$ equals the backbone's set of $0$ and of the numbers
$\pm m \beta^{e-t}$ with an integer mantissa $\beta^{t-1} \le m \le \beta^t - 1$ and an exponent
$L \le e \le U$.

The mantissa is $m = a_1 a_2 \dots a_t = \sum_{i=1}^t a_i \beta^{t-i}$. Conversely, every $m$ in
that range has exactly the base-$\beta$ digits $a_i = \lfloor m / \beta^{t-i} \rfloor \bmod
\beta$, with $a_1 \neq 0$ because $m \ge \beta^{t-1}$. The backbone's set is
`FloatingPoint.System.numbers`. -/
theorem floatingPointNumbers_eq (s : System) :
    floatingPointNumbers s.β s.t s.L s.U = s.numbers ℝ := by
  have hβ := s.β_pos
  have ht := s.one_le_t
  have hpow1 : 1 ≤ s.β ^ s.t := Nat.one_le_pow _ _ hβ
  ext x
  simp only [floatingPointNumbers, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    System.numbers]
  constructor
  · rintro (rfl | ⟨σ, e, a, ha, ha1, hL, hU, rfl⟩)
    · exact Or.inl rfl
    · set m : ℕ := ∑ i ∈ Icc 1 s.t, a i * s.β ^ (s.t - i) with hm
      have hm1 : s.β ^ (s.t - 1) ≤ m := by
        calc s.β ^ (s.t - 1) = 1 * s.β ^ (s.t - 1) := (one_mul _).symm
          _ ≤ a 1 * s.β ^ (s.t - 1) := Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.2 ha1)
          _ ≤ m := single_le_sum (f := fun i => a i * s.β ^ (s.t - i)) (fun _ _ => Nat.zero_le _)
              (mem_Icc.2 ⟨le_rfl, ht⟩)
      have hm2 : m ≤ s.β ^ s.t - 1 := by
        have : m < s.β ^ s.t := by
          rw [hm, sum_Icc_eq_sum_range]
          calc ∑ j ∈ range s.t, a (s.t - j) * s.β ^ (s.t - (s.t - j))
              = ∑ j ∈ range s.t, a (s.t - j) * s.β ^ j := by
                refine sum_congr rfl fun j hj => ?_
                rw [mem_range] at hj
                rw [Nat.sub_sub_self hj.le]
            _ < s.β ^ s.t := sum_mul_pow_lt fun j hj => by
                have := ha (s.t - j) (mem_Icc.2 ⟨by omega, by omega⟩)
                omega
        omega
      refine Or.inr ⟨if σ then -1 else 1, m, e, hm1, hm2, hL, hU, ?_⟩
      rw [mul_assoc, zpow_mul_sum_eq hβ, ← hm]
      cases σ <;> simp
  · rintro (rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩)
    · exact Or.inl rfl
    · have hmlt : m < s.β ^ s.t := by omega
      have hdigits : ∑ i ∈ Icc 1 s.t, m / s.β ^ (s.t - i) % s.β * s.β ^ (s.t - i) = m := by
        rw [sum_Icc_eq_sum_range]
        refine Eq.trans ?_ (sum_div_pow_mod_mul_pow s.two_le_β s.t m hmlt)
        refine sum_congr rfl fun j hj => ?_
        rw [mem_range] at hj
        rw [Nat.sub_sub_self hj.le]
      have hval : ((σ : ℤ) : ℝ) * m * (s.β : ℝ) ^ (e - s.t) = ((σ : ℤ) : ℝ) * ((s.β : ℝ) ^ e *
          ∑ i ∈ Icc 1 s.t, ((m / s.β ^ (s.t - i) % s.β : ℕ) : ℝ) * (s.β : ℝ) ^ (-(i : ℤ))) := by
        rw [zpow_mul_sum_eq hβ, hdigits, mul_assoc]
      have hdig : ∀ i ∈ Icc 1 s.t, m / s.β ^ (s.t - i) % s.β ≤ s.β - 1 := fun i _ => by
        have := Nat.mod_lt (m / s.β ^ (s.t - i)) hβ
        omega
      have hd1 : m / s.β ^ (s.t - 1) % s.β ≠ 0 := by
        have hq : m / s.β ^ (s.t - 1) < s.β := by
          rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos hβ), ← pow_succ']
          rwa [Nat.sub_add_cancel ht]
        have hq1 : 1 ≤ m / s.β ^ (s.t - 1) := (Nat.one_le_div_iff (Nat.pow_pos hβ)).2 hm1
        rw [Nat.mod_eq_of_lt hq]
        omega
      rcases Int.units_eq_one_or σ with rfl | rfl
      · exact Or.inr ⟨false, e, fun i => m / s.β ^ (s.t - i) % s.β, hdig, hd1, hL, hU,
          by rw [hval]; simp⟩
      · exact Or.inr ⟨true, e, fun i => m / s.β ^ (s.t - i) % s.β, hdig, hd1, hL, hU,
          by rw [hval]; simp⟩

/-- **Equation (2.30)** of [quarteroni2000numerical]. Every nonzero $x \in \mathbb{F}$ satisfies
$$x_{min} = \beta^{L-1} \le |x| \le \beta^U (1 - \beta^{-t}) = x_{max}.$$
-/
theorem equation_2_30 (s : System) {x : ℝ} (hx : x ∈ s.numbers ℝ) (h0 : x ≠ 0) :
    (s.β : ℝ) ^ (s.L - 1) ≤ |x| ∧ |x| ≤ (s.β : ℝ) ^ s.U * (1 - (s.β : ℝ) ^ (-(s.t : ℤ))) :=
  ⟨s.xmin_le_abs hx h0, s.abs_le_xmax hx⟩

/-- **Section 2.5.2** of [quarteroni2000numerical], the cardinality of $\mathbb{F}$. The set
$\mathbb{F}(\beta, t, L, U)$ has
$$2 (\beta - 1) \beta^{t-1} (U - L + 1) + 1$$
elements.

The number of elements is `Set.ncard`, cast to $\mathbb{Z}$. -/
theorem cardFloatingPoint (s : System) :
    ((s.numbers ℝ).ncard : ℤ)
      = 2 * ((s.β : ℤ) - 1) * (s.β : ℤ) ^ (s.t - 1) * (s.U - s.L + 1) + 1 := by
  rw [← s.coe_finset, Set.ncard_coe_finset, s.card_finset]

/-- **Section 2.5.2** of [quarteroni2000numerical], the de-normalized numbers. The de-normalized
numbers $\mathbb{F}_D$ are the numbers $\pm m \beta^{L-t}$ with a mantissa
$1 \le m \le \beta^{t-1} - 1$ at the exponent $L$. Let $t \ge 2$. Then "the smallest number in
this set has absolute value equal to $\beta^{L-t}$": $\beta^{L-t}$ is the least positive
de-normalized number. Every de-normalized number "belongs to the interval
$(-\beta^{L-1}, \beta^{L-1})$".

**Reading.** The book does not state the hypothesis $t \ge 2$. For $t = 1$ there are no
de-normalized numbers.

The de-normalized numbers are `FloatingPoint.System.denormalized`. -/
theorem denormalizedMin (s : System) (ht : 2 ≤ s.t) :
    IsLeast {x : ℝ | x ∈ s.denormalized ℝ ∧ 0 < x} ((s.β : ℝ) ^ (s.L - s.t)) ∧
      ∀ x ∈ s.denormalized ℝ, x ∈ Set.Ioo (-(s.β : ℝ) ^ (s.L - 1)) ((s.β : ℝ) ^ (s.L - 1)) :=
  ⟨s.isLeast_denormalized ht, fun _ hx => by
    have := abs_lt.1 (s.abs_lt_xmin_of_mem_denormalized hx)
    exact ⟨this.1, this.2⟩⟩

/-- **Example 2.11** of [quarteroni2000numerical], the system $\mathbb{F}(2, 3, -1, 2)$: base $2$,
three significant digits, and exponents $-1 \le e \le 2$. -/
def example_2_11_system : System := ⟨2, 3, -1, 2, by norm_num, by norm_num, by norm_num⟩

/-- **Example 2.11** of [quarteroni2000numerical]. The positive numbers of $\mathbb{F}(2, 3, -1, 2)$
are the sixteen numbers $(0.111)_2 \cdot 2^2 = 7/2$, $(0.110)_2 \cdot 2^2 = 3$, …,
$(0.100)_2 \cdot 2^{-1} = 1/4$, that is,
$$\tfrac{7}{2}, 3, \tfrac{5}{2}, 2, \tfrac{7}{4}, \tfrac{3}{2}, \tfrac{5}{4}, 1, \tfrac{7}{8},
  \tfrac{3}{4}, \tfrac{5}{8}, \tfrac{1}{2}, \tfrac{7}{16}, \tfrac{3}{8}, \tfrac{5}{16},
  \tfrac{1}{4}.$$

The set is computed over $\mathbb{Q}$. -/
theorem example_2_11 :
    {x : ℚ | x ∈ example_2_11_system.numbers ℚ ∧ 0 < x} =
      {7/2, 3, 5/2, 2, 7/4, 3/2, 5/4, 1, 7/8, 3/4, 5/8, 1/2, 7/16, 3/8, 5/16, 1/4} := by
  have key : ∀ (m : ℕ) (e : ℤ), 4 ≤ m → m ≤ 7 → -1 ≤ e → e ≤ 2 → ∀ x : ℚ,
      x = m * (2 : ℚ) ^ (e - 3) → x ∈ example_2_11_system.numbers ℚ ∧ 0 < x := by
    intro m e hm1 hm2 he1 he2 x hx
    refine ⟨Or.inr ⟨1, m, e, hm1, hm2, he1, he2, ?_⟩, ?_⟩
    · simp [example_2_11_system, hx]
    · rw [hx]
      exact mul_pos (by exact_mod_cast (by omega : 0 < m)) (zpow_pos (by norm_num) _)
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hpos⟩
    rcases hx with rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩
    · exact absurd hpos (lt_irrefl 0)
    · simp only [example_2_11_system] at hm1 hm2 hL hU hpos ⊢
      norm_num at hm1 hm2
      rcases Int.units_eq_one_or σ with rfl | rfl
      · simp only [Units.val_one, Int.cast_one, one_mul, Nat.cast_ofNat] at hpos ⊢
        interval_cases m <;> interval_cases e <;> norm_num
      · exfalso
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Nat.cast_ofNat] at hpos
        have : (0 : ℚ) < m * (2 : ℚ) ^ (e - 3) :=
          mul_pos (by exact_mod_cast (by omega : 0 < m)) (zpow_pos (by norm_num) _)
        linarith
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl)
    · exact key 7 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 7 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 6 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 7 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 6 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 5 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 4 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 7 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 6 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 5 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 4 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)

/-- **Example 2.11** of [quarteroni2000numerical], the bounds and the count. The numbers of
$\mathbb{F}(2, 3, -1, 2)$ lie between $x_{min} = \beta^{L-1} = 2^{-2} = 1/4$ and $x_{max} =
\beta^U (1 - \beta^{-t}) = 2^2 (1 - 2^{-3}) = 7/2$. There are
$(\beta - 1) \beta^{t-1} (U - L + 1) = 16$ positive numbers, so $\mathbb{F}$ has
$2 \cdot 16 + 1 = 33$ elements, with the opposites and zero.

The values are computed over $\mathbb{Q}$, and the count is the cardinality of
`FloatingPoint.System.finset`. -/
theorem example_2_11_bounds :
    example_2_11_system.xmin ℚ = 1/4 ∧ example_2_11_system.xmax ℚ = 7/2 ∧
      ((example_2_11_system.finset ℚ).card : ℤ) = 2 * 16 + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [System.xmin, example_2_11_system]; norm_num
  · simp [System.xmax, example_2_11_system]; norm_num
  · rw [System.card_finset]; simp [example_2_11_system]

/-- **Example 2.11** of [quarteroni2000numerical], the de-normalized numbers. The positive
de-normalized numbers of $\mathbb{F}(2, 3, -1, 2)$ are $(0.011)_2 \cdot 2^{-1} = 3/16$,
$(0.010)_2 \cdot 2^{-1} = 1/8$ and $(0.001)_2 \cdot 2^{-1} = 1/16$, and "the smallest
de-normalized number is $\beta^{L-t} = 2^{-1-3} = 1/16$".

The values are computed over $\mathbb{Q}$. -/
theorem example_2_11_denormalized :
    {x : ℚ | x ∈ example_2_11_system.denormalized ℚ ∧ 0 < x} = {3/16, 1/8, 1/16} ∧
      IsLeast {x : ℚ | x ∈ example_2_11_system.denormalized ℚ ∧ 0 < x} (1/16) := by
  have key : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ∀ x : ℚ, x = m * (2 : ℚ) ^ (-4 : ℤ) →
      x ∈ example_2_11_system.denormalized ℚ ∧ 0 < x := by
    intro m hm1 hm2 x hx
    refine ⟨⟨1, m, hm1, hm2, ?_⟩, ?_⟩
    · simp [example_2_11_system, hx]
    · rw [hx]
      exact mul_pos (by exact_mod_cast (by omega : 0 < m)) (zpow_pos (by norm_num) _)
  have hset : {x : ℚ | x ∈ example_2_11_system.denormalized ℚ ∧ 0 < x} = {3/16, 1/8, 1/16} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨σ, m, hm1, hm2, rfl⟩, hpos⟩
      simp only [example_2_11_system] at hm1 hm2 hpos ⊢
      norm_num at hm2
      rcases Int.units_eq_one_or σ with rfl | rfl
      · simp only [Units.val_one, Int.cast_one, one_mul, Nat.cast_ofNat] at hpos ⊢
        interval_cases m <;> norm_num
      · exfalso
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Nat.cast_ofNat] at hpos
        have : (0 : ℚ) < m * (2 : ℚ) ^ ((-1 : ℤ) - 3) :=
          mul_pos (by exact_mod_cast (by omega : 0 < m)) (zpow_pos (by norm_num) _)
        linarith
    · rintro (rfl | rfl | rfl)
      · exact key 3 (by norm_num) (by norm_num) _ (by norm_num)
      · exact key 2 (by norm_num) (by norm_num) _ (by norm_num)
      · exact key 1 (by norm_num) (by norm_num) _ (by norm_num)
  refine ⟨hset, ?_⟩
  have hval : ((example_2_11_system.β : ℚ) ^ (example_2_11_system.L - example_2_11_system.t))
      = 1 / 16 := by
    norm_num [example_2_11_system]
  have := example_2_11_system.isLeast_denormalized (K := ℚ) (by decide)
  rwa [hval] at this

/-! ### §2.5.3 Distribution of the floating-point numbers -/

/-- **Section 2.5.3** of [quarteroni2000numerical], the distribution of the floating-point numbers.
Let $L \le e \le U$. The numbers of $\mathbb{F}$ in $[\beta^{e-1}, \beta^e)$ are exactly the
numbers $m \beta^{e-t}$ with $\beta^{t-1} \le m \le \beta^t - 1$: they are "equally spaced and
[with] distance equal to $\beta^{e-t}$". Let $x \neq 0$ have the exponent $e$. Then the spacing
$\beta^{e-t}$ at $x$ satisfies
$$\beta^{-1} \varepsilon_M |x| < \beta^{e-t} \le \varepsilon_M |x|,$$
where $\varepsilon_M = \beta^{1-t}$ is the machine epsilon. The book says that "the spacing
between a number $x \in \mathbb{F}$ and its next nearest $y \in \mathbb{F}$ … is at least
$\beta^{-1} \varepsilon_M |x|$ and at most $\varepsilon_M |x|$".

**Reading.** Both statements use the mantissa convention (2.29),
$x = \pm (0.a_1 \dots a_t) \times \beta^e$, in which the numbers of exponent $e$ fill
$[\beta^{e-1}, \beta^e)$. The book's sentence "having fixed an interval of the form
$[\beta^e, \beta^{e+1}]$ … distance equal to $\beta^{e-t}$" uses the other convention
$a_1.a_2 \dots \times \beta^e$.

The exponent of $x$ is `FloatingPoint.System.exponent x`. The second statement holds for every
nonzero real $x$, not only for $x \in \mathbb{F}$. -/
theorem spacing (s : System) :
    (∀ e : ℤ, s.L ≤ e → e ≤ s.U →
      s.numbers ℝ ∩ Set.Ico ((s.β : ℝ) ^ (e - 1)) ((s.β : ℝ) ^ e) =
        (fun m : ℕ => (m : ℝ) * (s.β : ℝ) ^ (e - s.t)) ''
          Set.Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1)) ∧
    ∀ x : ℝ, x ≠ 0 →
      (s.β : ℝ)⁻¹ * (s.β : ℝ) ^ (1 - (s.t : ℤ)) * |x| < (s.β : ℝ) ^ (s.exponent x - s.t) ∧
        (s.β : ℝ) ^ (s.exponent x - s.t) ≤ (s.β : ℝ) ^ (1 - (s.t : ℤ)) * |x| :=
  ⟨fun _ hL hU => s.numbers_inter_Ico hL hU, fun _ hx => s.ulp_bounds hx⟩

/-- **Equation (2.31)** of [quarteroni2000numerical], wobbling precision. Let
$x = \sigma m \beta^{e-t}$ with $\sigma = \pm 1$, an integer mantissa
$\beta^{t-1} \le m \le \beta^t - 1$ and an integer $e$. The distance $\Delta x = \beta^{e-t}$
from $x$ to the next number gives the relative distance
$$\frac{\Delta x}{|x|} = \frac{1}{m},$$
which depends only on the mantissa.

The book writes $\Delta x / x$. The exponent $e$ is not restricted to $[L, U]$, and $\Delta x$
is written with `FloatingPoint.System.exponent x`, which equals $e$. -/
theorem equation_2_31 (s : System) {σ : ℤˣ} {m : ℕ} {e : ℤ} (hm1 : s.β ^ (s.t - 1) ≤ m)
    (hm2 : m ≤ s.β ^ s.t - 1) {x : ℝ} (hx : x = ((σ : ℤ) : ℝ) * m * (s.β : ℝ) ^ (e - s.t)) :
    (s.β : ℝ) ^ (s.exponent x - s.t) / |x| = 1 / m :=
  s.ulp_div_eq_inv_mantissa hm1 hm2 hx

/-- **Section 2.5.3** of [quarteroni2000numerical], the machine epsilon. Assume $L \le 1 \le U$ and
$t \ge 2$. Then $\varepsilon_M = \beta^{1-t}$ is the least $\delta > 0$ with
$1 + \delta \in \mathbb{F}$. The book says that $\varepsilon_M$ "represents the distance between
the number $1$ and the nearest floating-point number, and therefore it is the smallest number of
$\mathbb{F}$ such that $1 + \varepsilon_M > 1$".

**Reading.** The characterization of the book is read as: $\varepsilon_M$ is the least positive
$\delta$ with $1 + \delta \in \mathbb{F}$. This needs the exponent $1$ to be admissible and
$t \ge 2$, which the book does not state: in $\mathbb{F}(2, 1, L, 1)$ no number of $\mathbb{F}$
exceeds $1$. -/
theorem machineEps_isLeast (s : System) (hL : s.L ≤ 1) (hU : 1 ≤ s.U) (ht : 2 ≤ s.t) :
    IsLeast {δ : ℝ | 0 < δ ∧ 1 + δ ∈ s.numbers ℝ} ((s.β : ℝ) ^ (1 - (s.t : ℤ))) :=
  s.isLeast_machineEps hL hU ht

/-! ### §2.5.4 IEC/IEEE arithmetic -/

/-- **Section 2.5.4** of [quarteroni2000numerical], the basic formats of IEC 559. Single precision
is $\mathbb{F}(2, 24, -125, 128)$ with the roundoff unit $u = 2^{-24}$, and double precision is
$\mathbb{F}(2, 53, -1021, 1024)$ with $u = 2^{-53}$.

The two systems are `FloatingPoint.System.ieeeSingle` and `FloatingPoint.System.ieeeDouble`. -/
theorem ieeeUnitRoundoff :
    (System.ieeeSingle.β, System.ieeeSingle.t, System.ieeeSingle.L, System.ieeeSingle.U) =
        (2, 24, -125, 128) ∧
      (System.ieeeDouble.β, System.ieeeDouble.t, System.ieeeDouble.L, System.ieeeDouble.U) =
        (2, 53, -1021, 1024) ∧
      System.ieeeSingle.unitRoundoff ℝ = 2 ^ (-24 : ℤ) ∧
      System.ieeeDouble.unitRoundoff ℝ = 2 ^ (-53 : ℤ) :=
  ⟨rfl, rfl, System.ieeeSingle_unitRoundoff, System.ieeeDouble_unitRoundoff⟩

/-! ### §2.5.5 Rounding of a real number in its machine representation -/

/-- **Equation (2.32)** of [quarteroni2000numerical], rounding as a digit rule. Let $\beta$ be even,
and let $x \in \mathbb{R}$ have the exponent $e$, so that $|x| = (0.a_1 a_2 \dots a_t a_{t+1}
\dots)_\beta \, \beta^e$. Let $\mu = |x| \beta^{t-e}$, so that
$a_1 \dots a_t = \lfloor \mu \rfloor$ and the next digit is $a_{t+1} = \lfloor \beta \mu \rfloor
\bmod \beta$. Then
$$fl(x) = (-1)^s (0.a_1 a_2 \dots \tilde{a}_t)_\beta \, \beta^e, \qquad \tilde{a}_t =
  \begin{cases} a_t & \text{if } a_{t+1} < \beta/2, \\ a_t + 1 & \text{if } a_{t+1} \ge \beta/2,
  \end{cases}$$
that is, $fl(x) = \operatorname{sign}(x) \, (\lfloor \mu \rfloor + [a_{t+1} \ge \beta/2]) \,
\beta^{e-t}$, where $[\cdot]$ is $1$ if the condition holds and $0$ otherwise.

The hypothesis that $\beta$ is even is the standing assumption of the book from Section 2.5.1.
For odd $\beta$ the digit rule is not rounding to nearest. The number $\mu$ is
`FloatingPoint.System.mantissa x`, and $fl$ is the rounding to nearest `FloatingPoint.System.round`.
-/
theorem equation_2_32 (s : System) (hβ : Even s.β) (x : ℝ) :
    s.round x = (SignType.sign x : ℝ) *
      ((⌊s.mantissa x⌋ + if (s.β : ℤ) / 2 ≤ ⌊s.mantissa x * s.β⌋ % s.β then 1 else 0 : ℤ) : ℝ) *
        (s.β : ℝ) ^ (s.exponent x - s.t) := by
  rw [System.round, round_eq_floor_add_ite hβ s.two_le_β]

/-- **Section 2.5.5** of [quarteroni2000numerical]: $fl(x) = x$ if $x \in \mathbb{F}$. -/
theorem fl_eq_self_of_mem (s : System) {x : ℝ} (hx : x ∈ s.numbers ℝ) : s.round x = x :=
  s.round_eq_self hx

/-- **Section 2.5.5** of [quarteroni2000numerical], the monotonicity of rounding: $fl(x) \le fl(y)$
if $x \le y$, for all $x, y \in \mathbb{R}$. -/
theorem fl_mono (s : System) {x y : ℝ} (hxy : x ≤ y) : s.round x ≤ s.round y :=
  s.round_mono hxy

/-- **Remark 2.2** of [quarteroni2000numerical] (overflow and underflow). Overflow: if
$|x| \ge \beta^U$, then $fl(x) \notin \mathbb{F}$. Underflow: if
$0 < |x| < x_{min} = \beta^{L-1}$, then "the operation of rounding is defined anyway", and it
still satisfies the bound (2.33),
$$|fl(x) - x| \le u |x|, \qquad u = \tfrac{1}{2} \beta^{1-t}.$$

**Reading.** The book says that "$fl(x)$ is not defined" for $|x| > x_{max}$. The statement
reads this as "$fl(x)$ is not a number of $\mathbb{F}$", with the threshold $\beta^U$ in place
of $x_{max}$, because the numbers of $(x_{max}, \beta^U - \frac{1}{2} \beta^{U-t})$ round to
$x_{max}$. -/
theorem remark_2_2 (s : System) :
    (∀ x : ℝ, (s.β : ℝ) ^ s.U ≤ |x| → s.round x ∉ s.numbers ℝ) ∧
      ∀ x : ℝ, 0 < |x| → |x| < (s.β : ℝ) ^ (s.L - 1) →
        |s.round x - x| ≤ (1 / 2 : ℝ) * (s.β : ℝ) ^ (1 - (s.t : ℤ)) * |x| :=
  ⟨fun _ hx => s.round_notMem_numbers hx, fun x _ _ => s.abs_round_sub_le x⟩

/-- **Property 2.1** of [quarteroni2000numerical], (2.33)–(2.34). If $x \in \mathbb{R}$ satisfies
$x_{min} \le |x| \le x_{max}$, then $fl(x) \in \mathbb{F}$ and
$$fl(x) = x (1 + \delta), \qquad |\delta| \le u,$$
where $u = \frac{1}{2} \beta^{1-t}$ is the roundoff unit.

The bound on $\delta$ holds without the range hypothesis in the backbone; the statement keeps
the hypothesis of the book. -/
theorem property_2_1 (s : System) {x : ℝ} (h1 : s.xmin ℝ ≤ |x|) (h2 : |x| ≤ s.xmax ℝ) :
    (∃ δ : ℝ, |δ| ≤ (1 / 2 : ℝ) * (s.β : ℝ) ^ (1 - (s.t : ℤ)) ∧ s.round x = x * (1 + δ)) ∧
      s.round x ∈ s.numbers ℝ :=
  ⟨s.exists_round_eq_mul_one_add x, s.round_mem_numbers h1 h2⟩

/-- **Equation (2.34)** of [quarteroni2000numerical]. The roundoff unit is $u = \frac{1}{2}
\beta^{1-t} = \frac{1}{2} \varepsilon_M$.

The two constants are `FloatingPoint.System.unitRoundoff` and `FloatingPoint.System.machineEps`. -/
theorem equation_2_34 (s : System) :
    s.unitRoundoff ℝ = (1 / 2 : ℝ) * (s.β : ℝ) ^ (1 - (s.t : ℤ)) ∧
      s.unitRoundoff ℝ = s.machineEps ℝ / 2 :=
  ⟨rfl, s.unitRoundoff_eq_machineEps_div_two⟩

/-- **Property 2.1** of [quarteroni2000numerical], for chopping, after the remark of the book that
"in the chopping one would take $\tilde{a}_t = a_t$". For every $x \in \mathbb{R}$,
$$\operatorname{chop}(x) = x (1 + \delta), \qquad |\delta| \le \beta^{1-t} = \varepsilon_M,$$
so $\varepsilon_M$ is the unit roundoff of chopping.

Chopping is `FloatingPoint.System.chop`, which truncates the mantissa. The bound is Theorem 2.2
of [higham2002accuracy]. -/
theorem property_2_1_chop (s : System) (x : ℝ) :
    ∃ δ : ℝ, |δ| ≤ (s.β : ℝ) ^ (1 - (s.t : ℤ)) ∧ s.chop x = x * (1 + δ) :=
  s.exists_chop_eq_mul_one_add x

/-- **Equation (2.35)** of [quarteroni2000numerical], the relative error of rounding. For
$x \neq 0$,
$$E_{rel}(x) = \frac{|x - fl(x)|}{|x|} \le u = \tfrac{1}{2} \beta^{1-t}.$$
-/
theorem equation_2_35 (s : System) {x : ℝ} (hx : x ≠ 0) :
    |x - s.round x| / |x| ≤ (1 / 2 : ℝ) * (s.β : ℝ) ^ (1 - (s.t : ℤ)) := by
  rw [div_le_iff₀ (abs_pos.2 hx), abs_sub_comm]
  exact s.abs_round_sub_le x

/-- **Section 2.5.5** of [quarteroni2000numerical], the absolute error of rounding, the display
$E(x) \le \frac{1}{2} \beta^{-t+e}$ that closes the section. For every $x \in \mathbb{R}$ with
exponent $e$,
$$E(x) = |x - fl(x)| \le \tfrac{1}{2} \beta^{e-t}.$$

The exponent is `FloatingPoint.System.exponent x`. For $x = 0$ the left side is $0$. -/
theorem roundAbsError (s : System) (x : ℝ) :
    |x - s.round x| ≤ (1 / 2 : ℝ) * (s.β : ℝ) ^ (s.exponent x - s.t) :=
  s.abs_sub_round_le x

/-! ### §2.5.6 Machine floating-point operations -/

/-- **Section 2.5.6** of [quarteroni2000numerical], the machine operation. Given an arithmetic
operation $\circ : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$, the corresponding machine
operation maps $x, y$ to
$$fl\bigl(fl(x) \circ fl(y)\bigr).$$
-/
noncomputable def machineOp (s : System) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  s.round (f (s.round x) (s.round y))

/-- The machine operation of Section 2.5.6 of [quarteroni2000numerical] is the backbone's
`FloatingPoint.System.op`. The machine sum, difference, product and quotient are
`FloatingPoint.System.add`, `FloatingPoint.System.sub`, `FloatingPoint.System.mul` and
`FloatingPoint.System.div`. -/
theorem machineOp_eq (s : System) (f : ℝ → ℝ → ℝ) : machineOp s f = s.op f := rfl

/-- **Equation (2.36)** of [quarteroni2000numerical]. For all $x, y \in \mathbb{F}$ and each of the
four operations $\circ \in \{+, -, \times, /\}$, the machine operation satisfies
$$fl\bigl(fl(x) \circ fl(y)\bigr) = (x \circ y)(1 + \delta), \qquad |\delta| \le u.$$

**Reading.** The book says that for the subtraction this "will require an additional assumption
… the round digit". In the arithmetic of this module the exact result is rounded, so the
assumption holds automatically.

For $y = 0$ the quotient $x / y$ is $0$ in Lean, and the statement holds with $\delta = 0$. -/
theorem equation_2_36 (s : System) {x y : ℝ} (hx : x ∈ s.numbers ℝ) (hy : y ∈ s.numbers ℝ) :
    (∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ machineOp s (· + ·) x y = (x + y) * (1 + δ)) ∧
      (∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ machineOp s (· - ·) x y = (x - y) * (1 + δ)) ∧
      (∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ machineOp s (· * ·) x y = (x * y) * (1 + δ)) ∧
      ∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ machineOp s (· / ·) x y = (x / y) * (1 + δ) :=
  ⟨s.exists_op_eq_mul_one_add _ hx hy, s.exists_op_eq_mul_one_add _ hx hy,
    s.exists_op_eq_mul_one_add _ hx hy, s.exists_op_eq_mul_one_add _ hx hy⟩

/-- **Section 2.5.6** of [quarteroni2000numerical], properties that are preserved: "the
commutativity of the sum of two addends, or the product of two factors" survives in
floating-point arithmetic. For all $x, y \in \mathbb{R}$, $x \oplus y = y \oplus x$ and
$x \otimes y = y \otimes x$. -/
theorem machineOp_comm (s : System) (x y : ℝ) :
    machineOp s (· + ·) x y = machineOp s (· + ·) y x ∧
      machineOp s (· * ·) x y = machineOp s (· * ·) y x :=
  ⟨s.add_comm x y, s.mul_comm x y⟩

/-- The two-digit decimal system $\mathbb{F}(10, 2, -1, 2)$, in which
`QuarteroniSaccoSaleri.Chapter02.machineAdd_not_assoc` shows the failure of associativity of
Section 2.5.6 of [quarteroni2000numerical]. Its base and precision are those of the example of
the round digit in Section 2.5.6. -/
def decimalSystem : System := ⟨10, 2, -1, 2, by norm_num, by norm_num, by norm_num⟩

/-- **Section 2.5.6** of [quarteroni2000numerical], associativity is lost: "in general $x \oplus (y
\oplus z) \neq (x \oplus y) \oplus z$". In $\mathbb{F}(10, 2, -1, 2)$, the numbers $x = 1$ and
$y = z = 0.04$ lie in $\mathbb{F}$, and
$$(x \oplus y) \oplus z = fl(fl(1.04) + 0.04) = fl(1.0 + 0.04) = 1.0,$$
while
$$x \oplus (y \oplus z) = fl(1 + fl(0.08)) = fl(1.08) = 1.1.$$

The values are computed over $\mathbb{Q}$ with `FloatingPoint.System.add`. -/
theorem machineAdd_not_assoc :
    (1 : ℚ) ∈ decimalSystem.numbers ℚ ∧ (4 / 100 : ℚ) ∈ decimalSystem.numbers ℚ ∧
      decimalSystem.add (decimalSystem.add (1 : ℚ) (4 / 100)) (4 / 100) = 1 ∧
      decimalSystem.add (1 : ℚ) (decimalSystem.add (4 / 100) (4 / 100)) = 11 / 10 ∧
      decimalSystem.add (decimalSystem.add (1 : ℚ) (4 / 100)) (4 / 100) ≠
        decimalSystem.add (1 : ℚ) (decimalSystem.add (4 / 100) (4 / 100)) := by
  have h1 : (1 : ℚ) ∈ decimalSystem.numbers ℚ :=
    Or.inr ⟨1, 10, 1, by norm_num [decimalSystem], by norm_num [decimalSystem],
      by norm_num [decimalSystem], by norm_num [decimalSystem], by norm_num [decimalSystem]⟩
  have h2 : (4 / 100 : ℚ) ∈ decimalSystem.numbers ℚ :=
    Or.inr ⟨1, 40, -1, by norm_num [decimalSystem], by norm_num [decimalSystem],
      by norm_num [decimalSystem], by norm_num [decimalSystem], by norm_num [decimalSystem]⟩
  have h3 : (8 / 100 : ℚ) ∈ decimalSystem.numbers ℚ :=
    Or.inr ⟨1, 80, -1, by norm_num [decimalSystem], by norm_num [decimalSystem],
      by norm_num [decimalSystem], by norm_num [decimalSystem], by norm_num [decimalSystem]⟩
  have r1 : decimalSystem.round (1 : ℚ) = 1 := decimalSystem.round_eq_self h1
  have r2 : decimalSystem.round (4 / 100 : ℚ) = 4 / 100 := decimalSystem.round_eq_self h2
  have r6 : decimalSystem.round (8 / 100 : ℚ) = 8 / 100 := decimalSystem.round_eq_self h3
  -- `fl(1.04) = 1.0`: exponent `1`, mantissa `10.4`
  have r3 : decimalSystem.round (1 + 4 / 100 : ℚ) = 1 := by
    rw [decimalSystem.round_eq_of_le_of_lt (e := 1) (by norm_num [decimalSystem])
      (by norm_num [decimalSystem])]
    norm_num [decimalSystem]
  -- `fl(0.08) = 0.08`: exponent `-1`, mantissa `80`
  have r4 : decimalSystem.round (4 / 100 + 4 / 100 : ℚ) = 8 / 100 := by
    rw [decimalSystem.round_eq_of_le_of_lt (e := -1) (by norm_num [decimalSystem])
      (by norm_num [decimalSystem])]
    norm_num [decimalSystem]
  -- `fl(1.08) = 1.1`: exponent `1`, mantissa `10.8`
  have r5 : decimalSystem.round (1 + 8 / 100 : ℚ) = 11 / 10 := by
    rw [decimalSystem.round_eq_of_le_of_lt (e := 1) (by norm_num [decimalSystem])
      (by norm_num [decimalSystem])]
    norm_num [decimalSystem]
  have hl : decimalSystem.add (decimalSystem.add (1 : ℚ) (4 / 100)) (4 / 100) = 1 := by
    simp only [System.add, System.op, r1, r2, r3]
  have hr : decimalSystem.add (1 : ℚ) (decimalSystem.add (4 / 100) (4 / 100)) = 11 / 10 := by
    simp only [System.add, System.op, r1, r2, r4, r6]
    exact r5
  exact ⟨h1, h2, hl, hr, by rw [hl, hr]; norm_num⟩

end QuarteroniSaccoSaleri.Chapter02
