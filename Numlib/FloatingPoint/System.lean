/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Log
import Mathlib.Basic.Sign.Basic
import Mathlib.Order.Interval.Finset.Nat
import Numlib.FloatingPoint.Model

/-!
# Floating-point number systems

A floating-point number system $\mathbb{F}(\beta, t, L, U)$ has a base $\beta \ge 2$, $t \ge 1$
significant digits and an exponent range $L \le e \le U$. Its nonzero numbers are
$x = \pm 0.a_1 a_2 \ldots a_t \times \beta^e$ with $a_1 \neq 0$, that is, $x = \pm m \beta^{e - t}$
with an integer mantissa $\beta^{t-1} \le m \le \beta^t - 1$. A number of exponent $e$ lies in the
interval $[\beta^{e-1}, \beta^e)$, its binade. This module follows §2.5 of
[quarteroni2000numerical]. It defines the numbers, the de-normalized numbers, the constants
$x_{\min} = \beta^{L-1}$, $x_{\max} = \beta^U (1 - \beta^{-t})$, the machine epsilon
$\epsilon_M = \beta^{1-t}$ and the roundoff unit $u = \frac12 \beta^{1-t}$, and the exponent, the
mantissa and the spacing $\beta^{e-t}$ of the numbers near a given $x$. It proves the standard facts
about them: the bounds (2.30), the cardinality of $\mathbb{F}$, the equal spacing of each binade,
the characterization of $\epsilon_M$ as the gap above $1$, and the relative spacing (2.31).

Rounding to nearest, $\mathrm{fl}$, and chopping are total functions on an ordered field $K$, and
they satisfy $|\mathrm{fl}(x) - x| \le u |x|$ and $|\mathrm{chop}(x) - x| \le \epsilon_M |x|$ for
every $x$ (Property 2.1 of [quarteroni2000numerical]). The range condition
$x_{\min} \le |x| \le x_{\max}$ is needed only for $\mathrm{fl}(x) \in \mathbb{F}$. So both
functions give instances of the relational rounding model of `Numlib.FloatingPoint.Model`, and every
theorem of `Numlib.FloatingPoint.InnerProduct` and `Numlib.FloatingPoint.Stationary` applies to the
computed values of $\mathbb{F}$ with no side conditions. A third instance rounds to a nearest number
of $\mathbb{F}$ with any tie rule. The module also defines the machine operations $x \circledcirc
y = \mathrm{fl}(\mathrm{fl}(x) \circ \mathrm{fl}(y))$ and proves (2.36) and the error bounds of
Exercises 2.11 and 2.12 of [quarteroni2000numerical], and it gives the IEEE single and double
precision systems of §2.5.4 with their constants. It also proves the density of the numbers with
finitely many digits in base $\beta$ (§2.5.1, `FloatingPoint.exists_int_mul_zpow_sub_abs_lt`).

## Main definitions

* `FloatingPoint.System`: the parameters $\beta$, $t$, $L$, $U$ of a floating-point number system.
* `FloatingPoint.System.numbers`: the set $\mathbb{F}$ of the normalized numbers and $0$.
* `FloatingPoint.System.denormalized`: the de-normalized numbers $\pm m \beta^{L-t}$,
  $1 \le m < \beta^{t-1}$.
* `FloatingPoint.System.xmin`, `FloatingPoint.System.xmax`, `FloatingPoint.System.machineEps`,
  `FloatingPoint.System.unitRoundoff`: the constants $x_{\min}$, $x_{\max}$, $\epsilon_M$ and $u$.
* `FloatingPoint.System.exponent`, `FloatingPoint.System.mantissa`, `FloatingPoint.System.ulp`: the
  exponent $e$ with $\beta^{e-1} \le |x| < \beta^e$, the mantissa $|x| \beta^{t-e}$ and the spacing
  $\beta^{e-t}$.
* `FloatingPoint.System.round`, `FloatingPoint.System.chop`: rounding to nearest and chopping.
* `FloatingPoint.System.roundingModel`, `FloatingPoint.System.choppingModel`,
  `FloatingPoint.System.nearestModel`: the three instances of the rounding model.
* `FloatingPoint.System.op`: the machine operation attached to an exact operation.
* `FloatingPoint.System.ieeeSingle`, `FloatingPoint.System.ieeeDouble`: the IEEE 754 single and
  double precision systems.

## Main results

* `FloatingPoint.System.xmin_le_abs`, `FloatingPoint.System.abs_le_xmax`:
  $x_{\min} \le |x| \le x_{\max}$ for every nonzero $x \in \mathbb{F}$.
* `FloatingPoint.System.card_finset`: $\mathbb{F}$ has $2 (\beta - 1) \beta^{t-1} (U - L + 1) + 1$
  elements.
* `FloatingPoint.System.isLeast_machineEps`: $\epsilon_M$ is the least $\delta > 0$ with
  $1 + \delta \in \mathbb{F}$.
* `FloatingPoint.System.ulp_div_eq_inv_mantissa`: the relative spacing at $x = \pm m \beta^{e-t}$ is
  $1 / m$.
* `FloatingPoint.System.round_mem_numbers`: $x_{\min} \le |x| \le x_{\max}$ implies
  $\mathrm{fl}(x) \in \mathbb{F}$.
* `FloatingPoint.System.abs_round_sub_le`, `FloatingPoint.System.abs_chop_sub_le`:
  $|\mathrm{fl}(x) - x| \le u |x|$ and $|\mathrm{chop}(x) - x| \le \epsilon_M |x|$ for every $x$.
* `FloatingPoint.System.round_notMem_numbers`: $\mathrm{fl}(x) \notin \mathbb{F}$ when
  $|x| \ge \beta^U$.
* `FloatingPoint.System.abs_sub_le_of_forall_abs_sub_le`: a nearest number of $\mathbb{F}$ to an $x$
  in the range of $\mathbb{F}$ has relative error at most $u$.
* `FloatingPoint.System.exists_op_eq_mul_one_add`: on machine numbers,
  $x \circledcirc y = (x \circ y)(1 + \delta)$ with $|\delta| \le u$.
* `FloatingPoint.System.abs_add_sub_le`, `FloatingPoint.System.abs_add_add_sub_le`: the error of a
  machine sum and of two chained machine sums.

## Implementation notes

* Everything after the parameters is stated over an ordered field $K$, with `[FloorRing K]` where
  the rounding functions are defined. So the system can be used over $\mathbb{Q}$ for decidable
  examples and over $\mathbb{R}$ for analysis.
* `FloatingPoint.System.round` rounds the mantissa to the nearest integer with Mathlib's `round`,
  which rounds halves up. For an even base this is the digit rule of (2.32) of
  [quarteroni2000numerical] (`FloatingPoint.round_eq_floor_add_ite`). The rounding functions do not
  use the exponent range. So `FloatingPoint.System.roundingModel` (where $y$ rounds $x$ when
  $y = \mathrm{fl}(x)$, and the unit roundoff is $u$) and `FloatingPoint.System.choppingModel` (with
  unit roundoff $\epsilon_M$) are total and functional, and overflow is the separate statement
  `FloatingPoint.System.round_notMem_numbers`. Both models are idempotent
  (`FloatingPoint.System.round_round`, `FloatingPoint.System.chop_chop`) and total. These are the
  two properties that the program semantics of `Numlib.FloatingPoint.Program` asks of a model.
* `FloatingPoint.System.nearestModel` allows any number of $\mathbb{F}$ nearest to $x$ when
  $x_{\min} \le |x| \le x_{\max}$, and the value $0$ for $x = 0$. IEEE round-half-to-even is one
  choice within it. This model is partial (underflow and overflow have no rounding) and idempotent.
* The round digit of §2.5.6 of [quarteroni2000numerical] is a hardware matter and has no counterpart
  here: the machine operations round the exact result.
* The module also proves that Mathlib's `round` is monotone (`FloatingPoint.monotone_round`), a fact
  that Mathlib lacks. Mathlib's `FP.Float` in `Mathlib.Data.FP.Basic` is `unsafe` and has no
  theorems, so it is not used. Mathlib's `Int.log` and `round` are used.
-/

open Finset

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Two facts about rounding to an integer, and positional expansions -/

/-- Rounding to the nearest integer, Mathlib's `round` $x \mapsto \lfloor x + \frac12 \rfloor$, is
monotone on a floor ring $K$. Mathlib does not have this fact. -/
theorem monotone_round [FloorRing K] : Monotone (round : K → ℤ) := fun x y hxy => by
  rw [round_eq, round_eq]
  exact Int.floor_mono (by linarith)

/-- **Rounding to nearest as a digit rule.** Let the base $\beta \ge 2$ be even, let $\mu \in K$,
and let $a = \lfloor \beta \mu \rfloor \bmod \beta$ be the first digit of $\mu$ after its
integer part. Then the nearest integer to $\mu$ (halves rounded up) is $\lfloor \mu \rfloor + 1$
if $a \ge \beta / 2$, and $\lfloor \mu \rfloor$ otherwise. This is the rule (2.32) of
[quarteroni2000numerical].

For an odd base the digit rule chops some fractional parts above one half. -/
theorem round_eq_floor_add_ite [FloorRing K] {β : ℕ} (hβ : Even β) (hβ2 : 2 ≤ β) (μ : K) :
    round μ = ⌊μ⌋ + if (β : ℤ) / 2 ≤ ⌊μ * β⌋ % β then 1 else 0 := by
  obtain ⟨k, hk⟩ := hβ
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : K) < k := by exact_mod_cast hk1
  have hβk : (β : K) = 2 * k := by rw [hk]; push_cast; ring
  have hβk' : (β : ℤ) / 2 = k := by rw [hk]; omega
  -- the first digit beyond the integer part is `⌊fract μ · β⌋`
  have hfloor : ⌊μ * β⌋ % β = ⌊Int.fract μ * β⌋ := by
    have h1 : μ * β = ((⌊μ⌋ * β : ℤ) : K) + Int.fract μ * β := by
      push_cast; rw [Int.fract]; ring
    rw [h1, Int.floor_intCast_add, Int.mul_add_emod_self_right]
    refine Int.emod_eq_of_lt (Int.floor_nonneg.2 (by positivity)) ?_
    rw [Int.floor_lt]
    push_cast
    exact mul_lt_of_lt_one_left (by exact_mod_cast (show 0 < β by omega)) (Int.fract_lt_one μ)
  have hround : round μ = ⌊μ⌋ + ⌊Int.fract μ + 1 / 2⌋ := by
    rw [round_eq, ← Int.floor_intCast_add]
    congr 1
    rw [Int.fract]; ring
  rw [hround, hfloor, hβk']
  congr 1
  have h0 := Int.fract_nonneg μ
  have h1 := Int.fract_lt_one μ
  split_ifs with h
  · rw [Int.le_floor, hβk] at h
    push_cast at h
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith
  · rw [Int.le_floor, hβk, not_le] at h
    push_cast at h
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith

/-- The sign of $x \in K$, as an element of $K$, has absolute value at most $1$. -/
theorem abs_coe_sign_le_one (x : K) : |(SignType.sign x : K)| ≤ 1 := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [sign_neg h]
  · simp
  · simp [sign_pos h]

/-- **Density of finite positional expansions.** Let $K$ be an Archimedean ordered field and let
$\beta \ge 2$ be a natural number. For every $x \in K$ and every $\varepsilon > 0$ there are an
integer $m$ and a natural number $k$ with
$$|m \beta^{-k} - x| < \varepsilon,$$
so every $x$ is within $\varepsilon$ of a number with finitely many digits in base $\beta$. This
is the remark of §2.5.1 of [quarteroni2000numerical]. -/
theorem exists_int_mul_zpow_sub_abs_lt [Archimedean K] {β : ℕ} (hβ : 2 ≤ β) (x : K) {ε : K}
    (hε : 0 < ε) : ∃ (m : ℤ) (k : ℕ), |m * (β : K) ^ (-(k : ℤ)) - x| < ε := by
  have hβ1 : (1 : K) < β := by exact_mod_cast hβ
  have hβ0 : (0 : K) < β := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hβ1)
  obtain ⟨m, hm⟩ := exists_floor (x * (β : K) ^ k)
  have h1 : (m : K) ≤ x * (β : K) ^ k := (hm m).1 le_rfl
  have h2 : x * (β : K) ^ k < m + 1 := by
    have : ¬ ((m + 1 : ℤ) : K) ≤ x * (β : K) ^ k := fun h => by
      have := (hm (m + 1)).2 h
      omega
    push_cast at this
    exact lt_of_not_ge this
  refine ⟨m, k, ?_⟩
  have hkey : (m : K) * (β : K) ^ (-(k : ℤ)) - x
      = ((m : K) - x * (β : K) ^ k) * ((β : K)⁻¹) ^ k := by
    rw [zpow_neg, zpow_natCast, inv_pow]
    field_simp
  rw [hkey, abs_mul, abs_of_pos (pow_pos (inv_pos.2 hβ0) k)]
  calc |(m : K) - x * (β : K) ^ k| * ((β : K)⁻¹) ^ k ≤ 1 * ((β : K)⁻¹) ^ k := by
        gcongr
        rw [abs_le]
        constructor <;> linarith
    _ < ε := by rw [one_mul]; exact hk

/-! ### The parameters -/

/-- The parameters of a **floating-point number system** $\mathbb{F}(\beta, t, L, U)$ of §2.5.2 of
[quarteroni2000numerical]: a base $\beta \ge 2$, a number $t \ge 1$ of significant digits, and
an exponent range $L \le e \le U$ with $L \le U$. -/
structure System where
  /-- The base $\beta$. -/
  β : ℕ
  /-- The number $t$ of significant digits. -/
  t : ℕ
  /-- The smallest exponent $L$. -/
  L : ℤ
  /-- The largest exponent $U$. -/
  U : ℤ
  /-- The base satisfies $\beta \ge 2$. -/
  two_le_β : 2 ≤ β
  /-- There is at least one significant digit: $t \ge 1$. -/
  one_le_t : 1 ≤ t
  /-- The exponent range is nonempty: $L \le U$. -/
  L_le_U : L ≤ U

namespace System

variable (s : System)

/-- The base satisfies $1 < \beta$. -/
theorem one_lt_β : 1 < s.β := s.two_le_β

/-- The base satisfies $0 < \beta$. -/
theorem β_pos : 0 < s.β := by have := s.two_le_β; omega

/-- The base satisfies $1 < \beta$ in $K$. -/
theorem one_lt_β_cast : (1 : K) < s.β := by exact_mod_cast s.one_lt_β

/-- The base satisfies $0 < \beta$ in $K$. -/
theorem β_cast_pos : (0 : K) < s.β := by exact_mod_cast s.β_pos

/-- The base satisfies $\beta \neq 0$ in $K$. -/
theorem β_cast_ne_zero : (s.β : K) ≠ 0 := s.β_cast_pos.ne'

/-- The base satisfies $1 \le \beta$ in $K$. -/
theorem one_le_β_cast : (1 : K) ≤ s.β := s.one_lt_β_cast.le

/-- Every integer power $\beta^e$ of the base is positive. -/
theorem zpow_β_pos (e : ℤ) : 0 < (s.β : K) ^ e := zpow_pos s.β_cast_pos e

/-- Every integer power $\beta^e$ of the base is nonnegative. -/
theorem zpow_β_nonneg (e : ℤ) : 0 ≤ (s.β : K) ^ e := (s.zpow_β_pos e).le

/-- For a natural number $m$ and an integer $e$, $0 \le m \beta^e$. -/
theorem natCast_mul_zpow_nonneg (m : ℕ) (e : ℤ) : 0 ≤ (m : K) * (s.β : K) ^ e :=
  mul_nonneg (Nat.cast_nonneg _) (s.zpow_β_nonneg e)

/-- For a sign $\sigma = \pm 1$, a natural number $m$ and an integer $e$,
$|\sigma m \beta^e| = m \beta^e$. -/
theorem abs_units_mul (σ : ℤˣ) (m : ℕ) (e : ℤ) :
    |((σ : ℤ) : K) * m * (s.β : K) ^ e| = m * (s.β : K) ^ e := by
  rw [mul_assoc, abs_mul, abs_unit_intCast, one_mul, abs_of_nonneg (s.natCast_mul_zpow_nonneg m e)]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The natural number $\beta^{t-1}$, cast into a field, is the integer power $\beta^{t-1}$. -/
theorem natCast_pow_t_sub_one : ((s.β ^ (s.t - 1) : ℕ) : K) = (s.β : K) ^ ((s.t : ℤ) - 1) := by
  rw [Nat.cast_pow, ← zpow_natCast, Nat.cast_pred s.one_le_t]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The natural number $\beta^t$, cast into a field, is the integer power $\beta^t$. -/
theorem natCast_pow_t : ((s.β ^ s.t : ℕ) : K) = (s.β : K) ^ (s.t : ℤ) := by
  rw [Nat.cast_pow, zpow_natCast]

/-- A natural number $m \le \beta^t - 1$ satisfies $m + 1 \le \beta^t$ in $K$. -/
theorem natCast_add_one_le_zpow {m : ℕ} (hm : m ≤ s.β ^ s.t - 1) :
    (m : K) + 1 ≤ (s.β : K) ^ (s.t : ℤ) := by
  have h : m + 1 ≤ s.β ^ s.t := by
    have := Nat.one_le_pow s.t s.β s.β_pos
    omega
  rw [← s.natCast_pow_t]
  exact_mod_cast h

/-- A natural number $m \le \beta^t - 1$ satisfies $m < \beta^t$ in $K$. -/
theorem natCast_lt_zpow {m : ℕ} (hm : m ≤ s.β ^ s.t - 1) : (m : K) < (s.β : K) ^ (s.t : ℤ) :=
  (lt_add_one _).trans_le (s.natCast_add_one_le_zpow hm)

/-- A natural number $m \ge \beta^{t-1}$ satisfies $\beta^{t-1} \le m$ in $K$. -/
theorem zpow_le_natCast {m : ℕ} (hm : s.β ^ (s.t - 1) ≤ m) :
    (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m := by
  rw [← s.natCast_pow_t_sub_one]
  exact_mod_cast hm

/-- The lower bound of a binade: if $m \in K$ satisfies $\beta^{t-1} \le m$, then
$\beta^{e-1} \le m \beta^{e-t}$ for every integer $e$. -/
theorem zpow_sub_one_le_mul_zpow {m : K} (hm : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m) (e : ℤ) :
    (s.β : K) ^ (e - 1) ≤ m * (s.β : K) ^ (e - s.t) := by
  have h : (s.β : K) ^ (e - 1) = (s.β : K) ^ ((s.t : ℤ) - 1) * (s.β : K) ^ (e - s.t) := by
    rw [← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
  rw [h]
  exact mul_le_mul_of_nonneg_right hm (s.zpow_β_nonneg _)

/-- The upper bound of a binade: if $m \in K$ satisfies $m < \beta^t$, then
$m \beta^{e-t} < \beta^e$ for every integer $e$. -/
theorem mul_zpow_lt_zpow {m : K} (hm : m < (s.β : K) ^ (s.t : ℤ)) (e : ℤ) :
    m * (s.β : K) ^ (e - s.t) < (s.β : K) ^ e := by
  have h : (s.β : K) ^ e = (s.β : K) ^ (s.t : ℤ) * (s.β : K) ^ (e - s.t) := by
    rw [← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
  rw [h]
  exact mul_lt_mul_of_pos_right hm (s.zpow_β_pos _)

/-- The binades $[\beta^{e-1}, \beta^e)$ are disjoint: if $y$ lies in $[\beta^{e-1}, \beta^e)$ and
in $[\beta^{e'-1}, \beta^{e'})$, then $e = e'$. -/
theorem eq_of_zpow_sub_one_le_of_lt {e e' : ℤ} {y : K} (h1 : (s.β : K) ^ (e - 1) ≤ y)
    (h2 : y < (s.β : K) ^ e) (h1' : (s.β : K) ^ (e' - 1) ≤ y) (h2' : y < (s.β : K) ^ e') :
    e = e' := by
  have hβ := s.one_lt_β_cast (K := K)
  have a : e - 1 < e' := (zpow_lt_zpow_iff_right₀ hβ).1 (h1.trans_lt h2')
  have b : e' - 1 < e := (zpow_lt_zpow_iff_right₀ hβ).1 (h1'.trans_lt h2)
  omega

/-! ### The numbers -/

/-- The **normalized floating-point numbers** $\mathbb{F}(\beta, t, L, U)$ of §2.5.2 of
[quarteroni2000numerical], as a subset of a field $K$: the number $0$, together with the numbers
$$x = \sigma m \beta^{e-t}, \qquad \sigma = \pm 1, \quad \beta^{t-1} \le m \le \beta^t - 1,
  \quad L \le e \le U,$$
with an integer mantissa $m$.

The lower bound on $m$ is the normalization $a_1 \neq 0$ of the source's digit string
$m = a_1 a_2 \ldots a_t$, and $x = \pm 0.a_1 \ldots a_t \times \beta^e$. -/
def numbers (s : System) (K : Type*) [Field K] : Set K :=
  {x | x = 0 ∨ ∃ (σ : ℤˣ) (m : ℕ) (e : ℤ), s.β ^ (s.t - 1) ≤ m ∧ m ≤ s.β ^ s.t - 1 ∧
    s.L ≤ e ∧ e ≤ s.U ∧ x = ((σ : ℤ) : K) * m * (s.β : K) ^ (e - s.t)}

/-- The **de-normalized numbers** $\mathbb{F}_D$ of §2.5.2 of [quarteroni2000numerical]: the numbers
$\sigma m \beta^{L-t}$ with $\sigma = \pm 1$ and an integer mantissa
$1 \le m \le \beta^{t-1} - 1$ below the normalization threshold, at the smallest exponent $L$. -/
def denormalized (s : System) (K : Type*) [Field K] :
    Set K :=
  {x | ∃ (σ : ℤˣ) (m : ℕ), 1 ≤ m ∧ m ≤ s.β ^ (s.t - 1) - 1 ∧
    x = ((σ : ℤ) : K) * m * (s.β : K) ^ (s.L - s.t)}

/-- The smallest positive normalized number $x_{\min} = \beta^{L-1}$, as in (2.30) of
[quarteroni2000numerical]. -/
noncomputable def xmin (s : System) (K : Type*) [Field K] :
    K := (s.β : K) ^ (s.L - 1)

/-- The largest normalized number $x_{\max} = \beta^U (1 - \beta^{-t})$, as in (2.30) of
[quarteroni2000numerical]. -/
noncomputable def xmax (s : System) (K : Type*) [Field K] :
    K := (s.β : K) ^ s.U * (1 - (s.β : K) ^ (-(s.t : ℤ)))

/-- The **machine epsilon** $\epsilon_M = \beta^{1-t}$ of §2.5.3 of [quarteroni2000numerical]. It is
the spacing of the numbers of $\mathbb{F}$ in the binade $[1, \beta)$. -/
noncomputable def machineEps (s : System) (K : Type*) [Field K] : K := (s.β : K) ^ (1 - (s.t : ℤ))

/-- The **roundoff unit** $u = \frac12 \beta^{1-t} = \frac12 \epsilon_M$ of (2.34) of
[quarteroni2000numerical]. It bounds the relative error of rounding to nearest. -/
noncomputable def unitRoundoff (s : System) (K : Type*) [Field K] : K :=
  (1 / 2 : K) * (s.β : K) ^ (1 - (s.t : ℤ))

/-- The smallest positive normalized number is positive: $0 < x_{\min}$. -/
theorem xmin_pos : 0 < s.xmin K := s.zpow_β_pos _

/-- The machine epsilon is positive: $0 < \epsilon_M$. -/
theorem machineEps_pos : 0 < s.machineEps K := s.zpow_β_pos _

/-- The roundoff unit is positive: $0 < u$. -/
theorem unitRoundoff_pos : 0 < s.unitRoundoff K := by
  rw [unitRoundoff]; exact mul_pos (by norm_num) (s.zpow_β_pos _)

/-- The roundoff unit is nonnegative: $0 \le u$. -/
theorem unitRoundoff_nonneg : 0 ≤ s.unitRoundoff K := s.unitRoundoff_pos.le

/-- The roundoff unit is half the machine epsilon: $u = \epsilon_M / 2$. -/
theorem unitRoundoff_eq_machineEps_div_two : s.unitRoundoff K = s.machineEps K / 2 := by
  rw [unitRoundoff, machineEps]; ring

/-- The largest normalized number is $x_{\max} = \beta^U - \beta^{U-t}$. -/
theorem xmax_eq_sub : s.xmax K = (s.β : K) ^ s.U - (s.β : K) ^ (s.U - s.t) := by
  rw [xmax, mul_sub, mul_one, ← zpow_add₀ s.β_cast_ne_zero, ← sub_eq_add_neg]

/-- The largest normalized number is $x_{\max} = (\beta^t - 1) \beta^{U-t}$. -/
theorem xmax_eq_mul : s.xmax K = ((s.β : K) ^ (s.t : ℤ) - 1) * (s.β : K) ^ (s.U - s.t) := by
  rw [xmax_eq_sub, sub_mul, one_mul, ← zpow_add₀ s.β_cast_ne_zero, add_sub_cancel]

/-- The largest normalized number satisfies $x_{\max} < \beta^U$. -/
theorem xmax_lt_zpow : s.xmax K < (s.β : K) ^ s.U := by
  rw [xmax_eq_sub]
  linarith [zpow_pos (s.β_cast_pos (K := K)) (s.U - s.t)]

/-- The largest normalized number is positive: $0 < x_{\max}$. -/
theorem xmax_pos : 0 < s.xmax K := by
  rw [xmax_eq_mul]
  refine mul_pos ?_ (s.zpow_β_pos _)
  linarith [one_lt_zpow₀ (s.one_lt_β_cast (K := K)) (by exact_mod_cast s.one_le_t : (0 : ℤ) < s.t)]

/-- Membership in $\mathbb{F}$ through the absolute value: $x \in \mathbb{F}$ if and only if $x = 0$
or $|x| = m \beta^{e-t}$ for a natural number $m$ with $\beta^{t-1} \le m \le \beta^t - 1$ and
an integer $e$ with $L \le e \le U$. -/
theorem mem_numbers_iff_abs {x : K} :
    x ∈ s.numbers K ↔ x = 0 ∨ ∃ (m : ℕ) (e : ℤ), s.β ^ (s.t - 1) ≤ m ∧ m ≤ s.β ^ s.t - 1 ∧
      s.L ≤ e ∧ e ≤ s.U ∧ |x| = m * (s.β : K) ^ (e - s.t) := by
  constructor
  · rintro (rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨m, e, hm1, hm2, hL, hU, s.abs_units_mul σ m _⟩
  · rintro (rfl | ⟨m, e, hm1, hm2, hL, hU, hx⟩)
    · exact Or.inl rfl
    · rcases le_or_gt 0 x with h | h
      · exact Or.inr ⟨1, m, e, hm1, hm2, hL, hU, by rw [mul_assoc, ← hx, abs_of_nonneg h]; simp⟩
      · exact Or.inr ⟨-1, m, e, hm1, hm2, hL, hU, by rw [mul_assoc, ← hx, abs_of_neg h]; simp⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The number $0$ is in $\mathbb{F}$. -/
theorem zero_mem_numbers : (0 : K) ∈ s.numbers K := Or.inl rfl

/-- The set $\mathbb{F}$ is closed under negation: $x \in \mathbb{F}$ implies $-x \in \mathbb{F}$
(§2.5.2 of [quarteroni2000numerical]). -/
theorem neg_mem_numbers {x : K} (hx : x ∈ s.numbers K) : -x ∈ s.numbers K := by
  rw [mem_numbers_iff_abs] at hx ⊢
  simpa [neg_eq_zero, abs_neg] using hx

/-- The lower bound of the binade of a normalized number: if $m \ge \beta^{t-1}$ is a natural
number, then $\beta^{e-1} \le m \beta^{e-t}$ for every integer $e$. -/
theorem zpow_sub_one_le_natCast_mul_zpow {m : ℕ} (hm : s.β ^ (s.t - 1) ≤ m) (e : ℤ) :
    (s.β : K) ^ (e - 1) ≤ m * (s.β : K) ^ (e - s.t) :=
  s.zpow_sub_one_le_mul_zpow (s.zpow_le_natCast hm) e

/-- The upper bound of the binade of a normalized number: if $m \le \beta^t - 1$ is a natural
number, then $m \beta^{e-t} < \beta^e$ for every integer $e$. -/
theorem natCast_mul_zpow_lt_zpow {m : ℕ} (hm : m ≤ s.β ^ s.t - 1) (e : ℤ) :
    m * (s.β : K) ^ (e - s.t) < (s.β : K) ^ e :=
  s.mul_zpow_lt_zpow (s.natCast_lt_zpow hm) e

/-- Every nonzero $x \in \mathbb{F}$ satisfies $x_{\min} \le |x|$. This is the lower bound of (2.30)
of [quarteroni2000numerical]. -/
theorem xmin_le_abs {x : K} (hx : x ∈ s.numbers K) (h0 : x ≠ 0) : s.xmin K ≤ |x| := by
  rcases s.mem_numbers_iff_abs.1 hx with rfl | ⟨m, e, hm1, _, hL, _, hxe⟩
  · exact absurd rfl h0
  · rw [hxe, xmin]
    exact (zpow_le_zpow_right₀ s.one_le_β_cast (by omega)).trans
      (s.zpow_sub_one_le_natCast_mul_zpow hm1 e)

/-- Every $x \in \mathbb{F}$ satisfies $|x| \le x_{\max}$. This is the upper bound of (2.30) of
[quarteroni2000numerical]. -/
theorem abs_le_xmax {x : K} (hx : x ∈ s.numbers K) : |x| ≤ s.xmax K := by
  rcases s.mem_numbers_iff_abs.1 hx with rfl | ⟨m, e, _, hm2, _, hU, hxe⟩
  · simpa using s.xmax_pos.le
  · rw [hxe, xmax_eq_mul]
    have h1 : (m : K) ≤ (s.β : K) ^ (s.t : ℤ) - 1 := by
      linarith [s.natCast_add_one_le_zpow (K := K) hm2]
    have h2 : (s.β : K) ^ (e - s.t) ≤ (s.β : K) ^ (s.U - s.t) :=
      zpow_le_zpow_right₀ s.one_le_β_cast (by omega)
    exact mul_le_mul h1 h2 (s.zpow_β_nonneg _) (by linarith)

/-- The normalized representation is injective: if the natural numbers $m$ and $m'$ lie in
$[\beta^{t-1}, \beta^t - 1]$, then $m \beta^{e-t} = m' \beta^{e'-t}$ if and only if $m = m'$ and
$e = e'$. -/
theorem natCast_mul_zpow_eq_iff {m m' : ℕ} {e e' : ℤ} (hm1 : s.β ^ (s.t - 1) ≤ m)
    (hm2 : m ≤ s.β ^ s.t - 1) (hm1' : s.β ^ (s.t - 1) ≤ m') (hm2' : m' ≤ s.β ^ s.t - 1) :
    (m : K) * (s.β : K) ^ (e - s.t) = m' * (s.β : K) ^ (e' - s.t) ↔ m = m' ∧ e = e' := by
  constructor
  · intro h
    have he : e = e' :=
      s.eq_of_zpow_sub_one_le_of_lt (s.zpow_sub_one_le_natCast_mul_zpow hm1 e)
        (s.natCast_mul_zpow_lt_zpow hm2 e) (h ▸ s.zpow_sub_one_le_natCast_mul_zpow hm1' e')
        (h ▸ s.natCast_mul_zpow_lt_zpow hm2' e')
    subst he
    refine ⟨?_, rfl⟩
    exact_mod_cast mul_right_cancel₀ (zpow_ne_zero _ s.β_cast_ne_zero) h
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **Uniqueness of the normalized representation.** A nonzero $x \in K$ is in $\mathbb{F}$ if and
only if there is exactly one triple $(\sigma, m, e)$ with $\sigma = \pm 1$, a natural number
$\beta^{t-1} \le m \le \beta^t - 1$ and an integer $L \le e \le U$ such that
$x = \sigma m \beta^{e-t}$.

This is the reason for the normalization $a_1 \neq 0$ in §2.5.2 of [quarteroni2000numerical]
("to enforce uniqueness"). -/
theorem mem_numbers_iff_exists_unique {x : K} (hx : x ≠ 0) :
    x ∈ s.numbers K ↔ ∃! p : ℤˣ × ℕ × ℤ, s.β ^ (s.t - 1) ≤ p.2.1 ∧ p.2.1 ≤ s.β ^ s.t - 1 ∧
      s.L ≤ p.2.2 ∧ p.2.2 ≤ s.U ∧ x = ((p.1 : ℤ) : K) * p.2.1 * (s.β : K) ^ (p.2.2 - s.t) := by
  constructor
  · rintro (rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩)
    · exact absurd rfl hx
    · refine ⟨(σ, m, e), ⟨hm1, hm2, hL, hU, rfl⟩, ?_⟩
      rintro ⟨σ', m', e'⟩ ⟨hm1', hm2', -, -, h⟩
      dsimp only at hm1' hm2' h
      have habs : (m : K) * (s.β : K) ^ (e - s.t) = m' * (s.β : K) ^ (e' - s.t) := by
        have := congrArg abs h
        rwa [s.abs_units_mul, s.abs_units_mul] at this
      have hne : (m : K) * (s.β : K) ^ (e - s.t) ≠ 0 :=
        ((s.zpow_β_pos _).trans_le (s.zpow_sub_one_le_natCast_mul_zpow hm1 e)).ne'
      obtain ⟨hm, he⟩ := (s.natCast_mul_zpow_eq_iff hm1 hm2 hm1' hm2').1 habs
      subst hm he
      have hσ : ((σ : ℤ) : K) = ((σ' : ℤ) : K) := by
        rw [mul_assoc, mul_assoc] at h
        exact mul_right_cancel₀ hne h
      rw [Units.ext (Int.cast_injective hσ)]
  · rintro ⟨⟨σ, m, e⟩, ⟨hm1, hm2, hL, hU, h⟩, -⟩
    exact Or.inr ⟨σ, m, e, hm1, hm2, hL, hU, h⟩

/-! ### The cardinality -/

/-- The set $\mathbb{F}$ as a finite set: $\{0\}$ together with the images of the rectangle
$\beta^{t-1} \le m \le \beta^t - 1$, $L \le e \le U$ under the maps
$(m, e) \mapsto m \beta^{e-t}$ and $(m, e) \mapsto -m \beta^{e-t}$. -/
def finset (s : System) (K : Type*) [Field K] [LinearOrder K] :
    Finset K :=
  {0} ∪ (Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1) ×ˢ Icc s.L s.U).image
      (fun p : ℕ × ℤ => (p.1 : K) * (s.β : K) ^ (p.2 - s.t)) ∪
    (Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1) ×ˢ Icc s.L s.U).image
      (fun p : ℕ × ℤ => -((p.1 : K) * (s.β : K) ^ (p.2 - s.t)))

omit [IsStrictOrderedRing K] in
/-- The finite set `FloatingPoint.System.finset` is the set `FloatingPoint.System.numbers`. -/
theorem coe_finset : (s.finset K : Set K) = s.numbers K := by
  ext x
  simp only [finset, coe_union, coe_singleton, coe_image, coe_product, coe_Icc, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_image, Set.mem_prod, Set.mem_Icc, Prod.exists]
  constructor
  · rintro ((rfl | ⟨m, e, ⟨⟨hm1, hm2⟩, hL, hU⟩, rfl⟩) | ⟨m, e, ⟨⟨hm1, hm2⟩, hL, hU⟩, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨1, m, e, hm1, hm2, hL, hU, by simp⟩
    · exact Or.inr ⟨-1, m, e, hm1, hm2, hL, hU, by simp⟩
  · rintro (rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩)
    · exact Or.inl (Or.inl rfl)
    · rcases Int.units_eq_one_or σ with rfl | rfl
      · exact Or.inl (Or.inr ⟨m, e, ⟨⟨hm1, hm2⟩, hL, hU⟩, by simp⟩)
      · exact Or.inr ⟨m, e, ⟨⟨hm1, hm2⟩, hL, hU⟩, by simp⟩

/-- **The cardinality of $\mathbb{F}$.** Over an ordered field $K$, the set
$\mathbb{F}(\beta, t, L, U)$ has exactly
$$2 (\beta - 1) \beta^{t-1} (U - L + 1) + 1$$
elements. This is the count of §2.5.2 of [quarteroni2000numerical].

The set is counted as `FloatingPoint.System.finset`, and the count is an equation of integers. -/
theorem card_finset :
    ((s.finset K).card : ℤ)
      = 2 * ((s.β : ℤ) - 1) * (s.β : ℤ) ^ (s.t - 1) * (s.U - s.L + 1) + 1 := by
  set R := Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1) ×ˢ Icc s.L s.U with hR
  set f : ℕ × ℤ → K := fun p => (p.1 : K) * (s.β : K) ^ (p.2 - s.t) with hf
  have hfpos : ∀ p ∈ R, 0 < f p := by
    rintro ⟨m, e⟩ hp
    simp only [hR, mem_product, mem_Icc] at hp
    exact (s.zpow_β_pos _).trans_le (s.zpow_sub_one_le_natCast_mul_zpow hp.1.1 e)
  have hinj : Set.InjOn f R := by
    rintro ⟨m, e⟩ hp ⟨m', e'⟩ hp' h
    simp only [hR, coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc] at hp hp'
    obtain ⟨rfl, rfl⟩ := (s.natCast_mul_zpow_eq_iff hp.1.1 hp.1.2 hp'.1.1 hp'.1.2).1 h
    rfl
  have hinj' : Set.InjOn (fun p => -f p) R := fun p hp p' hp' h => hinj hp hp' (neg_injective h)
  have hd1 : Disjoint ({0} : Finset K) (R.image f) := by
    rw [disjoint_singleton_left, mem_image]
    rintro ⟨p, hp, h⟩
    exact (hfpos p hp).ne' h
  have hd2 : Disjoint ({0} ∪ R.image f) (R.image fun p => -f p) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hx'
    rcases mem_union.1 hx with h | h
    · exact (hfpos p hp).ne' (by simpa using h)
    · obtain ⟨q, hq, hq'⟩ := mem_image.1 h
      linarith [hfpos p hp, hfpos q hq]
  have hcard : (s.finset K).card = 1 + R.card + R.card := by
    rw [finset, ← hR, ← hf, card_union_of_disjoint hd2, card_union_of_disjoint hd1,
      card_singleton, card_image_of_injOn hinj, card_image_of_injOn hinj']
  have hRcard : (R.card : ℤ) = ((s.β : ℤ) - 1) * (s.β : ℤ) ^ (s.t - 1) * (s.U - s.L + 1) := by
    rw [hR, card_product, Nat.card_Icc, Int.card_Icc, Nat.cast_mul,
      Int.toNat_of_nonneg (by linarith [s.L_le_U])]
    obtain ⟨t', ht'⟩ := Nat.exists_eq_add_of_le' s.one_le_t
    have h1 : 1 ≤ s.β ^ s.t := Nat.one_le_pow _ _ s.β_pos
    have h2 : s.β ^ (s.t - 1) ≤ s.β ^ s.t := Nat.pow_le_pow_right s.β_pos (by omega)
    rw [Nat.sub_add_cancel h1, Nat.cast_sub h2]
    rw [ht', Nat.add_sub_cancel, pow_succ]
    push_cast
    ring
  rw [hcard]
  push_cast
  rw [hRcard]
  ring

/-! ### The distribution of the numbers -/

/-- **Each binade is an arithmetic progression.** For an integer $L \le e \le U$, the numbers of
$\mathbb{F}$ in $[\beta^{e-1}, \beta^e)$ are exactly the numbers $m \beta^{e-t}$ with a natural
number $\beta^{t-1} \le m \le \beta^t - 1$. So they are equally spaced, at distance
$\beta^{e-t}$ (§2.5.3 of [quarteroni2000numerical]). -/
theorem numbers_inter_Ico {e : ℤ} (hL : s.L ≤ e) (hU : e ≤ s.U) :
    s.numbers K ∩ Set.Ico ((s.β : K) ^ (e - 1)) ((s.β : K) ^ e) =
      (fun m : ℕ => (m : K) * (s.β : K) ^ (e - s.t)) ''
        Set.Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1) := by
  ext x
  constructor
  · rintro ⟨hx, hx1, hx2⟩
    have hpos : 0 < x := (s.zpow_β_pos _).trans_le hx1
    rcases s.mem_numbers_iff_abs.1 hx with rfl | ⟨m, e', hm1, hm2, _, _, hxe⟩
    · exact absurd hpos (lt_irrefl 0)
    · rw [abs_of_pos hpos] at hxe
      have he : e = e' :=
        s.eq_of_zpow_sub_one_le_of_lt hx1 hx2 (hxe ▸ s.zpow_sub_one_le_natCast_mul_zpow hm1 e')
          (hxe ▸ s.natCast_mul_zpow_lt_zpow hm2 e')
      subst he
      exact ⟨m, ⟨hm1, hm2⟩, hxe.symm⟩
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    refine ⟨Or.inr ⟨1, m, e, hm1, hm2, hL, hU, by simp⟩, s.zpow_sub_one_le_natCast_mul_zpow hm1 e,
      s.natCast_mul_zpow_lt_zpow hm2 e⟩

/-- No number of $\mathbb{F}$ lies strictly between $1$ and $1 + \epsilon_M$: if $\delta > 0$ and
$1 + \delta \in \mathbb{F}$, then $\epsilon_M \le \delta$.

This half of the characterization of $\epsilon_M$ in §2.5.3 of [quarteroni2000numerical] needs
no hypothesis on the exponent range. -/
theorem machineEps_le_of_one_add_mem {δ : K} (hδ : 0 < δ) (h : 1 + δ ∈ s.numbers K) :
    s.machineEps K ≤ δ := by
  have hβ := s.one_lt_β_cast (K := K)
  rcases s.mem_numbers_iff_abs.1 h with h0 | ⟨m, e, hm1, hm2, _, _, hxe⟩
  · linarith
  · rw [abs_of_pos (by linarith)] at hxe
    have hlow := s.zpow_sub_one_le_natCast_mul_zpow (K := K) hm1 e
    have hup := s.natCast_mul_zpow_lt_zpow (K := K) hm2 e
    rw [← hxe] at hlow hup
    have he0 : 0 < e := by
      have : (s.β : K) ^ (0 : ℤ) < (s.β : K) ^ e := by rw [zpow_zero]; linarith
      exact (zpow_lt_zpow_iff_right₀ hβ).1 this
    rcases lt_or_eq_of_le (show (1 : ℤ) ≤ e by omega) with he | he
    · -- exponent at least `2`: `1 + δ ≥ β ≥ 2`
      have : (s.β : K) ^ (1 : ℤ) ≤ (s.β : K) ^ (e - 1) := zpow_le_zpow_right₀ hβ.le (by omega)
      rw [zpow_one] at this
      have hε1 : s.machineEps K ≤ 1 :=
        zpow_le_one_of_nonpos₀ hβ.le (by linarith [(by exact_mod_cast s.one_le_t : (1 : ℤ) ≤ s.t)])
      have h2 : (2 : K) ≤ s.β := by exact_mod_cast s.two_le_β
      linarith
    · -- exponent `1`: `1 + δ = m β^(1-t)` with `m > β^(t-1)`
      subst he
      have hone : (1 : K) = (s.β : K) ^ ((s.t : ℤ) - 1) * (s.β : K) ^ ((1 : ℤ) - s.t) := by
        rw [← zpow_add₀ s.β_cast_ne_zero]; simp
      have hlt : ((s.β ^ (s.t - 1) : ℕ) : K) < m := by
        rw [s.natCast_pow_t_sub_one]
        by_contra hcon
        have := mul_le_mul_of_nonneg_right (not_lt.1 hcon) (s.zpow_β_nonneg ((1 : ℤ) - s.t))
        linarith
      have hlt' : s.β ^ (s.t - 1) + 1 ≤ m := by exact_mod_cast hlt
      have hle : ((s.β ^ (s.t - 1) : ℕ) : K) + 1 ≤ m := by exact_mod_cast hlt'
      rw [s.natCast_pow_t_sub_one] at hle
      have := mul_le_mul_of_nonneg_right hle (s.zpow_β_nonneg ((1 : ℤ) - s.t))
      rw [add_mul, one_mul] at this
      rw [machineEps]
      linarith

/-- If $L \le 1 \le U$ and $t \ge 2$, then $1 + \epsilon_M \in \mathbb{F}$.

For $t = 1$ and $\beta = 2$ the number $1 + \epsilon_M = 2$ has the exponent $2$, so that case
would need $U \ge 2$ instead. -/
theorem one_add_machineEps_mem (hL : s.L ≤ 1) (hU : 1 ≤ s.U) (ht : 2 ≤ s.t) :
    1 + s.machineEps K ∈ s.numbers K := by
  refine Or.inr ⟨1, s.β ^ (s.t - 1) + 1, 1, by omega, ?_, hL, hU, ?_⟩
  · obtain ⟨t', ht'⟩ := Nat.exists_eq_add_of_le' s.one_le_t
    have hβ := s.two_le_β
    have h2 : 2 ≤ s.β ^ t' := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t' := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ s.β ^ t' := Nat.pow_le_pow_left hβ t'
    rw [ht', Nat.add_sub_cancel, pow_succ]
    have : 2 * s.β ^ t' ≤ s.β ^ t' * s.β := by nlinarith
    omega
  · rw [machineEps, Nat.cast_add, Nat.cast_one, s.natCast_pow_t_sub_one, Units.val_one,
      Int.cast_one, one_mul, add_mul, one_mul, ← zpow_add₀ s.β_cast_ne_zero,
      show (s.t : ℤ) - 1 + (1 - s.t) = 0 by ring, zpow_zero]

/-- **The machine epsilon is the gap above $1$.** If $L \le 1 \le U$ and $t \ge 2$, then
$\epsilon_M$ is the least $\delta > 0$ with $1 + \delta \in \mathbb{F}$. This is §2.5.3 of
[quarteroni2000numerical]: "$\epsilon_M$ represents the distance between the number $1$ and the
nearest floating-point number, and therefore it is the smallest number of $\mathbb{F}$ such that
$1 + \epsilon_M > 1$".

The hypothesis $t \ge 2$ is needed: in $\mathbb{F}(2, 1, L, 1)$ no number exceeds $1$. -/
theorem isLeast_machineEps (hL : s.L ≤ 1) (hU : 1 ≤ s.U) (ht : 2 ≤ s.t) :
    IsLeast {δ : K | 0 < δ ∧ 1 + δ ∈ s.numbers K} (s.machineEps K) :=
  ⟨⟨s.machineEps_pos, s.one_add_machineEps_mem hL hU ht⟩,
    fun _ hδ => s.machineEps_le_of_one_add_mem hδ.1 hδ.2⟩

/-! ### The de-normalized numbers -/

/-- Every de-normalized number $x$ satisfies $\beta^{L-t} \le |x|$, so the smallest de-normalized
numbers are $\pm \beta^{L-t}$ (§2.5.2 of [quarteroni2000numerical]). -/
theorem zpow_le_abs_of_mem_denormalized {x : K} (hx : x ∈ s.denormalized K) :
    (s.β : K) ^ (s.L - s.t) ≤ |x| := by
  obtain ⟨σ, m, hm1, _, rfl⟩ := hx
  rw [s.abs_units_mul]
  have : (1 : K) ≤ m := by exact_mod_cast hm1
  nlinarith [s.zpow_β_pos (K := K) (s.L - s.t)]

/-- Every de-normalized number $x$ satisfies $|x| < x_{\min}$ (§2.5.2 of [quarteroni2000numerical]).
-/
theorem abs_lt_xmin_of_mem_denormalized {x : K} (hx : x ∈ s.denormalized K) :
    |x| < s.xmin K := by
  obtain ⟨σ, m, _, hm2, rfl⟩ := hx
  rw [s.abs_units_mul, xmin]
  have h : m + 1 ≤ s.β ^ (s.t - 1) := by
    have := Nat.one_le_pow (s.t - 1) s.β s.β_pos
    omega
  have hm : (m : K) < (s.β : K) ^ ((s.t : ℤ) - 1) := by
    rw [← s.natCast_pow_t_sub_one]; exact_mod_cast h
  calc (m : K) * (s.β : K) ^ (s.L - s.t)
      < (s.β : K) ^ ((s.t : ℤ) - 1) * (s.β : K) ^ (s.L - s.t) :=
        mul_lt_mul_of_pos_right hm (s.zpow_β_pos _)
    _ = (s.β : K) ^ (s.L - 1) := by rw [← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- If $t \ge 2$, then $\beta^{L-t}$ is a de-normalized number. For $t = 1$ there are no
de-normalized numbers. -/
theorem zpow_mem_denormalized (ht : 2 ≤ s.t) : (s.β : K) ^ (s.L - s.t) ∈ s.denormalized K := by
  refine ⟨1, 1, le_rfl, ?_, by simp⟩
  have : 2 ≤ s.β ^ (s.t - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (s.t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ s.β ^ (s.t - 1) := Nat.pow_le_pow_left s.two_le_β _
  omega

/-- **The smallest de-normalized number.** If $t \ge 2$, the least positive de-normalized number is
$\beta^{L-t}$ (§2.5.2 of [quarteroni2000numerical]). -/
theorem isLeast_denormalized (ht : 2 ≤ s.t) :
    IsLeast {x : K | x ∈ s.denormalized K ∧ 0 < x} ((s.β : K) ^ (s.L - s.t)) :=
  ⟨⟨s.zpow_mem_denormalized ht, s.zpow_β_pos _⟩, fun _ hx =>
    (s.zpow_le_abs_of_mem_denormalized hx.1).trans (abs_of_pos hx.2).le⟩

section Rounding

variable [FloorRing K]

/-! ### The exponent, the mantissa and the spacing -/

/-- The **exponent** of $x \in K$: the integer $e = \lfloor \log_\beta |x| \rfloor + 1$, which is
the unique $e$ with $\beta^{e-1} \le |x| < \beta^e$ for $x \neq 0$
(`FloatingPoint.System.zpow_exponent_sub_one_le_abs`,
`FloatingPoint.System.abs_lt_zpow_exponent`). Then $|x| = 0.a_1 a_2 \ldots \times \beta^e$ with
$a_1 \neq 0$.

The floor of the logarithm is Mathlib's `Int.log`. For $x = 0$ the exponent is $1$, and no lemma
depends on this value. -/
noncomputable def exponent (s : System) (x : K) : ℤ := Int.log s.β |x| + 1

/-- The **mantissa** of $x \in K$: the number $|x| \beta^{t-e}$, where $e$ is the exponent of $x$.
It is the number $a_1 a_2 \ldots a_t . a_{t+1} \ldots$ obtained by shifting the digits of $|x|$,
and it lies in $[\beta^{t-1}, \beta^t)$ for $x \neq 0$. The mantissa of $0$ is $0$. -/
noncomputable def mantissa (s : System) (x : K) : K := |x| * (s.β : K) ^ ((s.t : ℤ) - s.exponent x)

/-- The **unit in the last place** at $x \in K$: the number $\beta^{e-t}$, where $e$ is the exponent
of $x$. For $x \neq 0$ it is the spacing of the numbers of $\mathbb{F}$ in the binade
$[\beta^{e-1}, \beta^e)$ that contains $|x|$ (§2.5.3 of [quarteroni2000numerical], in the
convention $x = \pm 0.a_1 \ldots a_t \times \beta^e$ of (2.29)). At $x = 0$ it is $\beta^{1-t}$. -/
noncomputable def ulp (s : System) (x : K) : K := (s.β : K) ^ (s.exponent x - s.t)

omit [IsStrictOrderedRing K] in
/-- The exponent of $-x$ is the exponent of $x$. -/
@[simp] theorem exponent_neg (x : K) : s.exponent (-x) = s.exponent x := by simp [exponent]

/-- The exponent of $|x|$ is the exponent of $x$. -/
@[simp] theorem exponent_abs (x : K) : s.exponent |x| = s.exponent x := by simp [exponent]

/-- The exponent of $0$ is $1$, a conventional value. -/
@[simp] theorem exponent_zero : s.exponent (0 : K) = 1 := by simp [exponent]

omit [IsStrictOrderedRing K] in
/-- The mantissa of $-x$ is the mantissa of $x$. -/
@[simp] theorem mantissa_neg (x : K) : s.mantissa (-x) = s.mantissa x := by simp [mantissa]

/-- The mantissa of $0$ is $0$. -/
@[simp] theorem mantissa_zero : s.mantissa (0 : K) = 0 := by simp [mantissa]

/-- The mantissa is nonnegative. -/
theorem mantissa_nonneg (x : K) : 0 ≤ s.mantissa x :=
  mul_nonneg (abs_nonneg _) (s.zpow_β_nonneg _)

omit [IsStrictOrderedRing K] in
/-- The spacing at $-x$ is the spacing at $x$. -/
@[simp] theorem ulp_neg (x : K) : s.ulp (-x) = s.ulp x := by simp [ulp]

/-- The spacing $\beta^{e-t}$ is positive. -/
theorem ulp_pos (x : K) : 0 < s.ulp x := s.zpow_β_pos _

/-- The lower bound of the binade of $x$: if $x \neq 0$ and $e$ is the exponent of $x$, then
$\beta^{e-1} \le |x|$. -/
theorem zpow_exponent_sub_one_le_abs {x : K} (hx : x ≠ 0) :
    (s.β : K) ^ (s.exponent x - 1) ≤ |x| := by
  rw [exponent, add_sub_cancel_right]
  exact Int.zpow_log_le_self s.one_lt_β (abs_pos.2 hx)

/-- The upper bound of the binade of $x$: if $e$ is the exponent of $x$, then $|x| < \beta^e$. This
holds for every $x$, including $x = 0$. -/
theorem abs_lt_zpow_exponent (x : K) : |x| < (s.β : K) ^ s.exponent x :=
  Int.lt_zpow_succ_log_self s.one_lt_β |x|

/-- The exponent is characterized by the binade: if $\beta^{e-1} \le |x| < \beta^e$, then the
exponent of $x$ is $e$. -/
theorem exponent_eq_of_le_of_lt {x : K} {e : ℤ} (h1 : (s.β : K) ^ (e - 1) ≤ |x|)
    (h2 : |x| < (s.β : K) ^ e) : s.exponent x = e := by
  have hx : 0 < |x| := (s.zpow_β_pos _).trans_le h1
  have a := (Int.zpow_le_iff_le_log s.one_lt_β hx).1 h1
  have b := (Int.lt_zpow_iff_log_lt s.one_lt_β hx).1 h2
  rw [exponent]
  omega

/-- The exponent is monotone on the positive numbers: if $0 < x \le y$, then the exponent of $x$ is
at most the exponent of $y$. -/
theorem exponent_mono {x y : K} (hx : 0 < x) (hxy : x ≤ y) : s.exponent x ≤ s.exponent y := by
  rw [exponent, exponent]
  have := Int.log_mono_right (b := s.β) (abs_pos.2 hx.ne') (abs_le_abs hxy (by linarith))
  omega

/-- Every $x \in K$ satisfies $|x| = \mu \beta^{e-t}$, where $\mu$ is the mantissa and $e$ the
exponent of $x$. -/
theorem abs_eq_mantissa_mul_zpow (x : K) :
    |x| = s.mantissa x * (s.β : K) ^ (s.exponent x - s.t) := by
  rw [mantissa, mul_assoc, ← zpow_add₀ s.β_cast_ne_zero]
  simp

/-- The mantissa of a nonzero $x$ is at least $\beta^{t-1}$. -/
theorem zpow_le_mantissa {x : K} (hx : x ≠ 0) : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ s.mantissa x := by
  have h := s.zpow_exponent_sub_one_le_abs hx
  have := mul_le_mul_of_nonneg_right h (s.zpow_β_nonneg ((s.t : ℤ) - s.exponent x))
  rwa [← zpow_add₀ s.β_cast_ne_zero, show s.exponent x - 1 + ((s.t : ℤ) - s.exponent x)
    = (s.t : ℤ) - 1 by ring] at this

/-- The mantissa of every $x$ is less than $\beta^t$. -/
theorem mantissa_lt_zpow (x : K) : s.mantissa x < (s.β : K) ^ (s.t : ℤ) := by
  have h := s.abs_lt_zpow_exponent x
  have := mul_lt_mul_of_pos_right h (s.zpow_β_pos ((s.t : ℤ) - s.exponent x))
  rwa [← zpow_add₀ s.β_cast_ne_zero, show s.exponent x + ((s.t : ℤ) - s.exponent x)
    = (s.t : ℤ) by ring] at this

/-- If $|x| = m \beta^{e-t}$ with $m \in K$ and $\beta^{t-1} \le m < \beta^t$, then the exponent of
$x$ is $e$. -/
theorem exponent_eq_of_abs_eq {x m : K} {e : ℤ} (hm1 : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m)
    (hm2 : m < (s.β : K) ^ (s.t : ℤ)) (hx : |x| = m * (s.β : K) ^ (e - s.t)) :
    s.exponent x = e :=
  s.exponent_eq_of_le_of_lt (hx ▸ s.zpow_sub_one_le_mul_zpow hm1 e) (hx ▸ s.mul_zpow_lt_zpow hm2 e)

/-- If $|x| = m \beta^{e-t}$ with $m \in K$ and $\beta^{t-1} \le m < \beta^t$, then the mantissa of
$x$ is $m$. -/
theorem mantissa_eq_of_abs_eq {x m : K} {e : ℤ} (hm1 : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m)
    (hm2 : m < (s.β : K) ^ (s.t : ℤ)) (hx : |x| = m * (s.β : K) ^ (e - s.t)) :
    s.mantissa x = m := by
  rw [mantissa, s.exponent_eq_of_abs_eq hm1 hm2 hx, hx, mul_assoc, ← zpow_add₀ s.β_cast_ne_zero]
  simp

/-- **The spacing bounds.** For $x \neq 0$, the spacing $\beta^{e-t}$ of the numbers of $\mathbb{F}$
near $x$, with $e$ the exponent of $x$, satisfies
$$\beta^{-1} \epsilon_M |x| < \beta^{e-t} \le \epsilon_M |x|.$$
This is §2.5.3 of [quarteroni2000numerical].

The source says that the spacing is at least $\beta^{-1} \epsilon_M |x|$. The inequality is in
fact strict. -/
theorem ulp_bounds {x : K} (hx : x ≠ 0) :
    (s.β : K)⁻¹ * s.machineEps K * |x| < s.ulp x ∧ s.ulp x ≤ s.machineEps K * |x| := by
  have h1 := s.zpow_exponent_sub_one_le_abs hx
  have h2 := s.abs_lt_zpow_exponent x
  have hε : 0 < s.machineEps K := s.machineEps_pos
  have hulp : s.ulp x = s.machineEps K * (s.β : K) ^ (s.exponent x - 1) := by
    rw [ulp, machineEps, ← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
  have hβ : (s.β : K)⁻¹ * (s.β : K) ^ s.exponent x = (s.β : K) ^ (s.exponent x - 1) := by
    rw [← zpow_neg_one, ← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
  constructor
  · calc (s.β : K)⁻¹ * s.machineEps K * |x|
        < (s.β : K)⁻¹ * s.machineEps K * (s.β : K) ^ s.exponent x :=
          mul_lt_mul_of_pos_left h2 (mul_pos (inv_pos.2 s.β_cast_pos) hε)
      _ = s.ulp x := by rw [hulp, mul_right_comm, hβ, mul_comm]
  · rw [hulp]
    exact mul_le_mul_of_nonneg_left h1 hε.le

/-- **Wobbling precision.** Let $x = \sigma m \beta^{e-t}$ with $\sigma = \pm 1$ and a natural
number $\beta^{t-1} \le m \le \beta^t - 1$. Then the relative distance from $x$ to the next
number is
$$\frac{\beta^{e-t}}{|x|} = \frac{1}{m},$$
so it depends only on the mantissa. This is (2.31) of [quarteroni2000numerical].

The spacing $\beta^{e-t}$ is `FloatingPoint.System.ulp`. The exponent $e$ need not lie in
$[L, U]$. -/
theorem ulp_div_eq_inv_mantissa {σ : ℤˣ} {m : ℕ} {e : ℤ} (hm1 : s.β ^ (s.t - 1) ≤ m)
    (hm2 : m ≤ s.β ^ s.t - 1) {x : K} (hx : x = ((σ : ℤ) : K) * m * (s.β : K) ^ (e - s.t)) :
    s.ulp x / |x| = 1 / m := by
  have habs : |x| = m * (s.β : K) ^ (e - s.t) := by rw [hx, s.abs_units_mul]
  rw [ulp, s.exponent_eq_of_abs_eq (s.zpow_le_natCast hm1) (s.natCast_lt_zpow hm2) habs, habs,
    mul_comm (m : K), ← div_div, div_self (zpow_ne_zero _ s.β_cast_ne_zero)]

/-! ### Rounding to nearest and chopping -/

/-- **Rounding to nearest**, $\mathrm{fl}(x)$, as in (2.32) of [quarteroni2000numerical]: the
mantissa $|x| \beta^{t-e}$ of $x$ is rounded to the nearest integer, with halves rounded up, and
the sign and the exponent $e$ of $x$ are restored:
$$\mathrm{fl}(x) = \operatorname{sign}(x) \cdot \operatorname{round}(|x| \beta^{t-e}) \cdot
  \beta^{e-t}.$$

This is a total function on $K$, and it does not use the exponent range. When the mantissa
rounds up to $\beta^t$, the value is $\pm \beta^e$, a normalized number of exponent $e + 1$. The
nearest integer is Mathlib's `round`. -/
noncomputable def round (s : System) (x : K) : K :=
  (SignType.sign x : K) * (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t)

/-- **Chopping**, as in §2.5.5 of [quarteroni2000numerical]: the mantissa of $x$ is truncated to its
integer part, and the sign and the exponent $e$ of $x$ are restored:
$$\mathrm{chop}(x) = \operatorname{sign}(x) \cdot \lfloor |x| \beta^{t-e} \rfloor \cdot
  \beta^{e-t}.$$
-/
noncomputable def chop (s : System) (x : K) : K :=
  (SignType.sign x : K) * (⌊s.mantissa x⌋ : K) * (s.β : K) ^ (s.exponent x - s.t)

/-- Rounding fixes zero: $\mathrm{fl}(0) = 0$. -/
@[simp] theorem round_zero : s.round (0 : K) = 0 := by simp [round]

/-- Chopping fixes zero: $\mathrm{chop}(0) = 0$. -/
@[simp] theorem chop_zero : s.chop (0 : K) = 0 := by simp [chop]

/-- Rounding is odd: $\mathrm{fl}(-x) = -\mathrm{fl}(x)$. -/
theorem round_neg (x : K) : s.round (-x) = -s.round x := by
  simp [round, Left.sign_neg]

/-- Chopping is odd: $\mathrm{chop}(-x) = -\mathrm{chop}(x)$. -/
theorem chop_neg (x : K) : s.chop (-x) = -s.chop x := by
  simp [chop, Left.sign_neg]

/-- Rounding through a known binade: if $\beta^{e-1} \le |x| < \beta^e$, then
$$\mathrm{fl}(x) = \operatorname{sign}(x) \cdot \operatorname{round}(|x| \beta^{t-e}) \cdot
  \beta^{e-t}.$$
Concrete values are computed in this form. -/
theorem round_eq_of_le_of_lt {x : K} {e : ℤ} (h1 : (s.β : K) ^ (e - 1) ≤ |x|)
    (h2 : |x| < (s.β : K) ^ e) :
    s.round x = (SignType.sign x : K) * (_root_.round (|x| * (s.β : K) ^ ((s.t : ℤ) - e)) : K) *
      (s.β : K) ^ (e - s.t) := by
  rw [round, mantissa, s.exponent_eq_of_le_of_lt h1 h2]

/-- For $x \neq 0$, the mantissa of $x$ rounded to the nearest integer is at least $\beta^{t-1}$. -/
theorem zpow_le_round_mantissa {x : K} (hx : x ≠ 0) :
    ((s.β ^ (s.t - 1) : ℕ) : ℤ) ≤ _root_.round (s.mantissa x) := by
  have h := monotone_round (show ((s.β ^ (s.t - 1) : ℕ) : K) ≤ s.mantissa x by
    rw [s.natCast_pow_t_sub_one]; exact s.zpow_le_mantissa hx)
  rwa [round_natCast] at h

/-- The mantissa of $x$ rounded to the nearest integer is at most $\beta^t$. -/
theorem round_mantissa_le (x : K) : _root_.round (s.mantissa x) ≤ ((s.β ^ s.t : ℕ) : ℤ) := by
  have h := monotone_round (show s.mantissa x ≤ ((s.β ^ s.t : ℕ) : K) by
    rw [s.natCast_pow_t]; exact (s.mantissa_lt_zpow x).le)
  rwa [round_natCast] at h

/-- The mantissa of $x$ rounded to the nearest integer is nonnegative. -/
theorem round_mantissa_nonneg (x : K) : (0 : K) ≤ _root_.round (s.mantissa x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have := s.zpow_le_round_mantissa hx
    exact_mod_cast (Int.natCast_nonneg _).trans this

/-- The absolute value of $\mathrm{fl}(x)$ is $|\mathrm{fl}(x)| = \operatorname{round}(\mu)
\beta^{e-t}$, where $\mu$ is the mantissa and $e$ the exponent of $x$. -/
theorem abs_round (x : K) :
    |s.round x| = (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [round, mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg (s.round_mantissa_nonneg x)
      (s.zpow_β_nonneg _))]
    rcases lt_or_gt_of_ne hx with h | h <;> simp [sign_pos, sign_neg, h]

/-- Rounding keeps the sign: $\mathrm{fl}(x) = \operatorname{sign}(x) \cdot |\mathrm{fl}(x)|$. -/
theorem round_eq_sign_mul_abs (x : K) : s.round x = (SignType.sign x : K) * |s.round x| := by
  rw [abs_round, round, mul_assoc]

/-- Rounding preserves nonnegativity: $0 \le x$ implies $0 \le \mathrm{fl}(x)$. -/
theorem round_nonneg {x : K} (hx : 0 ≤ x) : 0 ≤ s.round x := by
  rw [round_eq_sign_mul_abs]
  rcases hx.lt_or_eq with h | rfl
  · simp [sign_pos h, abs_nonneg]
  · simp

/-- Rounding preserves nonpositivity: $x \le 0$ implies $\mathrm{fl}(x) \le 0$. -/
theorem round_nonpos {x : K} (hx : x ≤ 0) : s.round x ≤ 0 := by
  have := s.round_nonneg (neg_nonneg.2 hx)
  rwa [round_neg, neg_nonneg] at this

omit [IsStrictOrderedRing K] in
/-- For $x > 0$, $\mathrm{fl}(x) = \operatorname{round}(\mu) \beta^{e-t}$, where $\mu$ is the
mantissa and $e$ the exponent of $x$. -/
theorem round_of_pos {x : K} (hx : 0 < x) :
    s.round x = (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t) := by
  rw [round, sign_pos hx]; simp

/-- If $|x| = m \beta^{e-t}$ for integers $m$ and $e$ with $\beta^{t-1} \le m < \beta^t$, then
$\mathrm{fl}(x) = x$. The exponent $e$ need not lie in $[L, U]$. -/
theorem round_eq_self_of_abs_eq {x : K} {m e : ℤ} (hm1 : ((s.β ^ (s.t - 1) : ℕ) : ℤ) ≤ m)
    (hm2 : m < ((s.β ^ s.t : ℕ) : ℤ)) (hx : |x| = m * (s.β : K) ^ (e - s.t)) : s.round x = x := by
  have hm1' : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m := by
    rw [← s.natCast_pow_t_sub_one]; exact_mod_cast hm1
  have hm2' : (m : K) < (s.β : K) ^ (s.t : ℤ) := by
    rw [← s.natCast_pow_t]; exact_mod_cast hm2
  rw [round, s.mantissa_eq_of_abs_eq hm1' hm2' hx, s.exponent_eq_of_abs_eq hm1' hm2' hx,
    round_intCast, mul_assoc, ← hx, sign_mul_abs]

/-- Rounding fixes the numbers of $\mathbb{F}$: $\mathrm{fl}(x) = x$ for $x \in \mathbb{F}$ (§2.5.5
of [quarteroni2000numerical]). -/
theorem round_eq_self {x : K} (hx : x ∈ s.numbers K) : s.round x = x := by
  rcases s.mem_numbers_iff_abs.1 hx with rfl | ⟨m, e, hm1, hm2, _, _, hxe⟩
  · simp
  · refine s.round_eq_self_of_abs_eq (m := m) (e := e) (by exact_mod_cast hm1) ?_
      (by rw [Int.cast_natCast]; exact hxe)
    have := Nat.one_le_pow s.t s.β s.β_pos
    exact_mod_cast (show m < s.β ^ s.t by omega)

/-- **Rounding is idempotent**: $\mathrm{fl}(\mathrm{fl}(x)) = \mathrm{fl}(x)$ for every $x \in K$.

The rounded mantissa is an integer in $[\beta^{t-1}, \beta^t]$. When it is $\beta^t$, the result
$\pm \beta^e$ is the normalized number of exponent $e + 1$ with mantissa $\beta^{t-1}$. -/
theorem round_round (x : K) : s.round (s.round x) = s.round x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have habs := s.abs_round x
    have hlow := s.zpow_le_round_mantissa hx
    rcases (s.round_mantissa_le x).lt_or_eq with hlt | heq
    · exact s.round_eq_self_of_abs_eq hlow hlt habs
    · refine s.round_eq_self_of_abs_eq (m := ((s.β ^ (s.t - 1) : ℕ) : ℤ)) (e := s.exponent x + 1)
        le_rfl (by exact_mod_cast Nat.pow_lt_pow_right s.one_lt_β (by have := s.one_le_t; omega)) ?_
      rw [habs, heq, Int.cast_natCast, Int.cast_natCast, s.natCast_pow_t_sub_one, s.natCast_pow_t,
        ← zpow_add₀ s.β_cast_ne_zero, ← zpow_add₀ s.β_cast_ne_zero]
      congr 1; ring

/-- **Rounding lands in $\mathbb{F}$ on the range of $\mathbb{F}$**: if
$x_{\min} \le |x| \le x_{\max}$, then $\mathrm{fl}(x) \in \mathbb{F}$.

The mantissa rounds to an integer in $[\beta^{t-1}, \beta^t]$. When it rounds up to $\beta^t$,
the exponent increases by one. The new exponent is still at most $U$, because
$|x| \le x_{\max} = \beta^U - \beta^{U-t}$ excludes $e = U$ in that case. -/
theorem round_mem_numbers {x : K} (h1 : s.xmin K ≤ |x|) (h2 : |x| ≤ s.xmax K) :
    s.round x ∈ s.numbers K := by
  have hβ := s.one_lt_β_cast (K := K)
  have hx : x ≠ 0 := by
    rintro rfl
    simpa using s.xmin_pos.trans_le h1
  have habs := s.abs_round x
  have hlow := s.zpow_le_round_mantissa hx
  have hLe : s.L ≤ s.exponent x := by
    have : (s.β : K) ^ (s.L - 1) < (s.β : K) ^ s.exponent x :=
      h1.trans_lt (s.abs_lt_zpow_exponent x)
    have := (zpow_lt_zpow_iff_right₀ hβ).1 this
    omega
  have heU : s.exponent x ≤ s.U := by
    have : (s.β : K) ^ (s.exponent x - 1) < (s.β : K) ^ s.U :=
      (s.zpow_exponent_sub_one_le_abs hx).trans_lt (h2.trans_lt s.xmax_lt_zpow)
    have := (zpow_lt_zpow_iff_right₀ hβ).1 this
    omega
  rw [mem_numbers_iff_abs]
  rcases (s.round_mantissa_le x).lt_or_eq with hlt | heq
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((Int.natCast_nonneg _).trans hlow)
    rw [hm] at habs hlow hlt
    refine Or.inr ⟨m, s.exponent x, by exact_mod_cast hlow, ?_, hLe, heU, by simpa using habs⟩
    have : m < s.β ^ s.t := by exact_mod_cast hlt
    omega
  · -- the mantissa rounded up to `β^t`: the result is `β^e = β^(t-1) β^(e+1-t)`
    have hne : s.exponent x ≠ s.U := by
      intro hU
      have hround : (s.β : K) ^ (s.t : ℤ) ≤ s.mantissa x + 1 / 2 := by
        rw [← s.natCast_pow_t, ← Int.cast_natCast, ← heq]; exact round_le_add_half _
      have hxe := s.abs_eq_mantissa_mul_zpow x
      rw [hU] at hxe
      have hp : 0 < (s.β : K) ^ (s.U - s.t) := s.zpow_β_pos _
      have hkey : (s.β : K) ^ s.U - (s.β : K) ^ (s.U - s.t) / 2 ≤ |x| := by
        rw [hxe]
        have : ((s.β : K) ^ (s.t : ℤ) - 1 / 2) * (s.β : K) ^ (s.U - s.t) ≤
            s.mantissa x * (s.β : K) ^ (s.U - s.t) := by
          apply mul_le_mul_of_nonneg_right _ hp.le
          linarith
        rw [sub_mul, ← zpow_add₀ s.β_cast_ne_zero, add_sub_cancel] at this
        linarith
      rw [xmax_eq_sub] at h2
      linarith
    refine Or.inr ⟨s.β ^ (s.t - 1), s.exponent x + 1, le_rfl, ?_, by omega, by omega, ?_⟩
    · have h1 := Nat.one_le_pow s.t s.β s.β_pos
      have h2 : s.β ^ (s.t - 1) < s.β ^ s.t :=
        Nat.pow_lt_pow_right s.one_lt_β (by have := s.one_le_t; omega)
      omega
    · rw [habs, heq, Int.cast_natCast, s.natCast_pow_t, s.natCast_pow_t_sub_one,
        ← zpow_add₀ s.β_cast_ne_zero, ← zpow_add₀ s.β_cast_ne_zero]
      congr 1; ring

/-- Rounding is monotone on the positive numbers: if $0 < x \le y$, then
$\mathrm{fl}(x) \le \mathrm{fl}(y)$.

Within one binade this is the monotonicity of the rounding of the mantissa. Across binades,
$\mathrm{fl}(x) \le \beta^{e_x} \le \beta^{e_y - 1} \le \mathrm{fl}(y)$, where $e_x$ and $e_y$
are the exponents of $x$ and $y$. -/
theorem round_le_round_of_pos {x y : K} (hx : 0 < x) (hxy : x ≤ y) : s.round x ≤ s.round y := by
  have hy : 0 < y := hx.trans_le hxy
  have hβ := s.one_lt_β_cast (K := K)
  rw [s.round_of_pos hx, s.round_of_pos hy]
  rcases (s.exponent_mono hx hxy).lt_or_eq with hlt | heq
  · -- across binades
    have hup : (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t) ≤
        (s.β : K) ^ s.exponent x := by
      have h : (_root_.round (s.mantissa x) : K) ≤ (s.β : K) ^ (s.t : ℤ) := by
        rw [← s.natCast_pow_t]; exact_mod_cast s.round_mantissa_le x
      calc (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t)
          ≤ (s.β : K) ^ (s.t : ℤ) * (s.β : K) ^ (s.exponent x - s.t) :=
            mul_le_mul_of_nonneg_right h (s.zpow_β_nonneg _)
        _ = (s.β : K) ^ s.exponent x := by rw [← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
    have hlo : (s.β : K) ^ (s.exponent y - 1) ≤
        (_root_.round (s.mantissa y) : K) * (s.β : K) ^ (s.exponent y - s.t) := by
      refine s.zpow_sub_one_le_mul_zpow ?_ _
      rw [← s.natCast_pow_t_sub_one]; exact_mod_cast s.zpow_le_round_mantissa hy.ne'
    exact hup.trans ((zpow_le_zpow_right₀ hβ.le (by omega)).trans hlo)
  · -- within a binade
    have hm : s.mantissa x ≤ s.mantissa y := by
      rw [mantissa, mantissa, heq, abs_of_pos hx, abs_of_pos hy]
      exact mul_le_mul_of_nonneg_right hxy (s.zpow_β_nonneg _)
    rw [heq]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast monotone_round hm)
      (s.zpow_β_nonneg _)

/-- **Rounding is monotone**: $x \le y$ implies $\mathrm{fl}(x) \le \mathrm{fl}(y)$ (§2.5.5 of
[quarteroni2000numerical]). -/
theorem round_mono : Monotone (s.round : K → K) := by
  intro x y hxy
  rcases lt_or_ge 0 x with hx | hx
  · exact s.round_le_round_of_pos hx hxy
  · rcases lt_or_ge y 0 with hy | hy
    · have := s.round_le_round_of_pos (neg_pos.2 hy) (neg_le_neg hxy)
      rwa [round_neg, round_neg, neg_le_neg_iff] at this
    · exact (s.round_nonpos hx).trans (s.round_nonneg hy)

/-- **The absolute error of rounding**: for every $x \in K$,
$$|x - \mathrm{fl}(x)| \le \tfrac12 \beta^{e-t},$$
where $e$ is the exponent of $x$. This is the bound $E(x) \le \frac12 \beta^{e-t}$ at the end of
§2.5.5 of [quarteroni2000numerical].

The right side is half of `FloatingPoint.System.ulp`. -/
theorem abs_sub_round_le (x : K) : |x - s.round x| ≤ (1 / 2 : K) * s.ulp x := by
  have hp : 0 < (s.β : K) ^ (s.exponent x - s.t) := s.zpow_β_pos _
  have hx : x - s.round x = (SignType.sign x : K) *
      ((s.mantissa x - _root_.round (s.mantissa x)) * (s.β : K) ^ (s.exponent x - s.t)) := by
    have h1 : x = (SignType.sign x : K) * (s.mantissa x * (s.β : K) ^ (s.exponent x - s.t)) := by
      rw [← s.abs_eq_mantissa_mul_zpow, sign_mul_abs]
    rw [round, sub_mul, mul_sub, ← h1, mul_assoc]
  rw [hx, abs_mul, abs_mul, abs_of_pos hp, ulp]
  calc |(SignType.sign x : K)| * (|s.mantissa x - _root_.round (s.mantissa x)| *
        (s.β : K) ^ (s.exponent x - s.t))
      ≤ 1 * (1 / 2 * (s.β : K) ^ (s.exponent x - s.t)) := by
        gcongr
        · exact abs_coe_sign_le_one x
        · exact abs_sub_round _
    _ = 1 / 2 * (s.β : K) ^ (s.exponent x - s.t) := one_mul _

/-- For $x \neq 0$, half the spacing at $x$ is at most $u |x|$: $\frac12 \beta^{e-t} \le u |x|$,
where $e$ is the exponent of $x$. This is the step from the absolute to the relative error bound
of rounding. -/
theorem half_ulp_le_unitRoundoff_mul_abs {x : K} (hx : x ≠ 0) :
    (1 / 2 : K) * s.ulp x ≤ s.unitRoundoff K * |x| := by
  rw [unitRoundoff, mul_assoc, ← machineEps]
  exact mul_le_mul_of_nonneg_left (s.ulp_bounds hx).2 (by norm_num)

/-- **The relative error of rounding**: for every $x \in K$,
$$|\mathrm{fl}(x) - x| \le u |x|,$$
where $u = \frac12 \beta^{1-t}$ is the roundoff unit. This is Property 2.1 of
[quarteroni2000numerical] for rounding, and Theorem 2.2 of [higham2002accuracy] ("barring
overflow and underflow").

The source assumes $x_{\min} \le |x| \le x_{\max}$. The bound does not need this hypothesis; it
is needed only for $\mathrm{fl}(x) \in \mathbb{F}$ (`FloatingPoint.System.round_mem_numbers`). -/
theorem abs_round_sub_le (x : K) : |s.round x - x| ≤ s.unitRoundoff K * |x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [abs_sub_comm]
    exact (s.abs_sub_round_le x).trans (s.half_ulp_le_unitRoundoff_mul_abs hx)

/-- **The relative error of chopping**: for every $x \in K$,
$$|\mathrm{chop}(x) - x| \le \epsilon_M |x|.$$
This is Property 2.1 of [quarteroni2000numerical] for chopping. So the unit roundoff of chopping
is $\beta^{1-t}$, as in Theorem 2.2 of [higham2002accuracy]. -/
theorem abs_chop_sub_le (x : K) : |s.chop x - x| ≤ s.machineEps K * |x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hp : 0 < (s.β : K) ^ (s.exponent x - s.t) := s.zpow_β_pos _
    have hkey : s.chop x - x = -((SignType.sign x : K) *
        ((s.mantissa x - ⌊s.mantissa x⌋) * (s.β : K) ^ (s.exponent x - s.t))) := by
      have h1 : x = (SignType.sign x : K) * (s.mantissa x * (s.β : K) ^ (s.exponent x - s.t)) := by
        rw [← s.abs_eq_mantissa_mul_zpow, sign_mul_abs]
      rw [chop, sub_mul, mul_sub, ← h1, mul_assoc, neg_sub]
    rw [hkey, abs_neg, abs_mul, abs_mul, abs_of_pos hp]
    calc |(SignType.sign x : K)| * (|s.mantissa x - ⌊s.mantissa x⌋| *
          (s.β : K) ^ (s.exponent x - s.t))
        ≤ 1 * (1 * (s.β : K) ^ (s.exponent x - s.t)) := by
          gcongr
          · exact abs_coe_sign_le_one x
          · rw [Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le
      _ = s.ulp x := by rw [one_mul, one_mul, ulp]
      _ ≤ s.machineEps K * |x| := (s.ulp_bounds hx).2

/-- **Overflow.** If $|x| \ge \beta^U$, then $\mathrm{fl}(x) \notin \mathbb{F}$. This is Remark 2.2
of [quarteroni2000numerical].

The proof uses $|\mathrm{fl}(x)| \ge \beta^{e-1} \ge \beta^U > x_{\max}$, where $e$ is the
exponent of $x$. The threshold is $\beta^U$, not the $x_{\max}$ of the source: the numbers
between $x_{\max}$ and $\beta^U - \frac12 \beta^{U-t}$ still round to $x_{\max}$. Underflow
needs no statement, because `FloatingPoint.System.round` is total and
`FloatingPoint.System.abs_round_sub_le` holds for every $x$. -/
theorem round_notMem_numbers {x : K} (hx : (s.β : K) ^ s.U ≤ |x|) : s.round x ∉ s.numbers K := by
  intro hmem
  have hβ := s.one_lt_β_cast (K := K)
  have hx0 : x ≠ 0 := by
    rintro rfl
    simpa using (s.zpow_β_pos s.U).trans_le hx
  have hU : s.U < s.exponent x :=
    (zpow_lt_zpow_iff_right₀ hβ).1 (hx.trans_lt (s.abs_lt_zpow_exponent x))
  have hlo : (s.β : K) ^ (s.exponent x - 1) ≤ |s.round x| := by
    rw [abs_round]
    refine s.zpow_sub_one_le_mul_zpow ?_ _
    rw [← s.natCast_pow_t_sub_one]; exact_mod_cast s.zpow_le_round_mantissa hx0
  have := s.abs_le_xmax hmem
  have := s.xmax_lt_zpow (K := K)
  have := zpow_le_zpow_right₀ hβ.le (show s.U ≤ s.exponent x - 1 by omega)
  linarith

/-! ### The instances of the rounding model -/

/-- **$\mathbb{F}(\beta, t, L, U)$ with rounding to nearest** as an instance of the rounding model
of `Numlib.FloatingPoint.Model`: $y$ is an admissible rounding of $x$ if and only if
$y = \mathrm{fl}(x)$, and the unit roundoff is $u = \frac12 \beta^{1-t}$.

The model is total and functional. Overflow is `FloatingPoint.System.round_notMem_numbers`, not
a restriction of the relation. -/
noncomputable def roundingModel (s : System) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] : RoundingModel K where
  u := s.unitRoundoff K
  u_nonneg := s.unitRoundoff_nonneg
  Rounds x y := y = s.round x
  abs_sub_le := by
    rintro x y rfl
    exact s.abs_round_sub_le x

/-- **$\mathbb{F}(\beta, t, L, U)$ with chopping** as an instance of the rounding model: $y$ is an
admissible rounding of $x$ if and only if $y = \mathrm{chop}(x)$, and the unit roundoff is
$\epsilon_M = \beta^{1-t}$. -/
noncomputable def choppingModel (s : System) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] : RoundingModel K where
  u := s.machineEps K
  u_nonneg := s.machineEps_pos.le
  Rounds x y := y = s.chop x
  abs_sub_le := by
    rintro x y rfl
    exact s.abs_chop_sub_le x

/-- The unit roundoff of `FloatingPoint.System.roundingModel` is $u = \frac12 \beta^{1-t}$. -/
@[simp] theorem roundingModel_u : (s.roundingModel K).u = s.unitRoundoff K := rfl

/-- In `FloatingPoint.System.roundingModel`, $y$ is an admissible rounding of $x$ if and only if
$y = \mathrm{fl}(x)$. -/
@[simp] theorem roundingModel_rounds_iff {x y : K} :
    (s.roundingModel K).Rounds x y ↔ y = s.round x := Iff.rfl

/-- The unit roundoff of `FloatingPoint.System.choppingModel` is $\epsilon_M = \beta^{1-t}$. -/
@[simp] theorem choppingModel_u : (s.choppingModel K).u = s.machineEps K := rfl

/-- In `FloatingPoint.System.choppingModel`, $y$ is an admissible rounding of $x$ if and only if
$y = \mathrm{chop}(x)$. -/
@[simp] theorem choppingModel_rounds_iff {x y : K} :
    (s.choppingModel K).Rounds x y ↔ y = s.chop x := Iff.rfl

/-- For every $x \in K$ there is a $\delta$ with $|\delta| \le u$ and
$$\mathrm{fl}(x) = x (1 + \delta).$$
This is Property 2.1 of [quarteroni2000numerical] in the form (2.33). -/
theorem exists_round_eq_mul_one_add (x : K) :
    ∃ δ : K, |δ| ≤ s.unitRoundoff K ∧ s.round x = x * (1 + δ) :=
  RoundingModel.Rounds.exists_delta (m := s.roundingModel K) rfl

/-- For every $x \in K$ there is a $\delta$ with $|\delta| \le \epsilon_M$ and
$\mathrm{chop}(x) = x (1 + \delta)$. -/
theorem exists_chop_eq_mul_one_add (x : K) :
    ∃ δ : K, |δ| ≤ s.machineEps K ∧ s.chop x = x * (1 + δ) :=
  RoundingModel.Rounds.exists_delta (m := s.choppingModel K) rfl

/-! ### Idempotence and totality of the models -/

/-- The model `FloatingPoint.System.roundingModel` is idempotent: a rounded value rounds to itself
(`FloatingPoint.System.round_round`). -/
theorem roundingModel_isIdempotent : (s.roundingModel K).IsIdempotent := by
  intro x y z hxy hyz
  rw [roundingModel_rounds_iff] at hxy hyz
  rw [hyz, hxy, round_round]

/-- The model `FloatingPoint.System.roundingModel` is total: every $x$ has the rounding
$\mathrm{fl}(x)$. -/
theorem roundingModel_isTotal : (s.roundingModel K).IsTotal := fun x => ⟨s.round x, rfl⟩

/-- The absolute value of $\mathrm{chop}(x)$ is $|\mathrm{chop}(x)| = \lfloor \mu \rfloor
\beta^{e-t}$, where $\mu$ is the mantissa and $e$ the exponent of $x$. -/
theorem abs_chop (x : K) :
    |s.chop x| = (⌊s.mantissa x⌋ : K) * (s.β : K) ^ (s.exponent x - s.t) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : (0 : K) ≤ (⌊s.mantissa x⌋ : K) :=
      Int.cast_nonneg (Int.floor_nonneg.2 (s.mantissa_nonneg x))
    rw [chop, mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg h0 (s.zpow_β_nonneg _))]
    rcases lt_or_gt_of_ne hx with h | h <;> simp [sign_pos, sign_neg, h]

/-- For $x \neq 0$, the integer part of the mantissa of $x$ is at least $\beta^{t-1}$. -/
theorem zpow_le_floor_mantissa {x : K} (hx : x ≠ 0) :
    ((s.β ^ (s.t - 1) : ℕ) : ℤ) ≤ ⌊s.mantissa x⌋ :=
  Int.le_floor.2 (by rw [Int.cast_natCast, s.natCast_pow_t_sub_one]; exact s.zpow_le_mantissa hx)

/-- The integer part of the mantissa of $x$ is less than $\beta^t$. -/
theorem floor_mantissa_lt (x : K) : ⌊s.mantissa x⌋ < ((s.β ^ s.t : ℕ) : ℤ) :=
  Int.floor_lt.2 (by rw [Int.cast_natCast, s.natCast_pow_t]; exact s.mantissa_lt_zpow x)

/-- If $|x| = m \beta^{e-t}$ for integers $m$ and $e$ with $\beta^{t-1} \le m < \beta^t$, then
$\mathrm{chop}(x) = x$. The exponent $e$ need not lie in $[L, U]$. -/
theorem chop_eq_self_of_abs_eq {x : K} {m e : ℤ} (hm1 : ((s.β ^ (s.t - 1) : ℕ) : ℤ) ≤ m)
    (hm2 : m < ((s.β ^ s.t : ℕ) : ℤ)) (hx : |x| = m * (s.β : K) ^ (e - s.t)) : s.chop x = x := by
  have hm1' : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m := by
    rw [← s.natCast_pow_t_sub_one]; exact_mod_cast hm1
  have hm2' : (m : K) < (s.β : K) ^ (s.t : ℤ) := by
    rw [← s.natCast_pow_t]; exact_mod_cast hm2
  rw [chop, s.mantissa_eq_of_abs_eq hm1' hm2' hx, s.exponent_eq_of_abs_eq hm1' hm2' hx,
    Int.floor_intCast, mul_assoc, ← hx, sign_mul_abs]

/-- **Chopping is idempotent**: $\mathrm{chop}(\mathrm{chop}(x)) = \mathrm{chop}(x)$ for every
$x \in K$.

The chopped mantissa is an integer in $[\beta^{t-1}, \beta^t)$, and a second chop truncates an
integer. Unlike rounding, chopping never moves a number into the next binade. -/
theorem chop_chop (x : K) : s.chop (s.chop x) = s.chop x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact s.chop_eq_self_of_abs_eq (s.zpow_le_floor_mantissa hx) (s.floor_mantissa_lt x)
      (s.abs_chop x)

/-- The model `FloatingPoint.System.choppingModel` is idempotent (`FloatingPoint.System.chop_chop`).
-/
theorem choppingModel_isIdempotent : (s.choppingModel K).IsIdempotent := by
  intro x y z hxy hyz
  rw [choppingModel_rounds_iff] at hxy hyz
  rw [hyz, hxy, chop_chop]

/-- The model `FloatingPoint.System.choppingModel` is total: every $x$ has the rounding
$\mathrm{chop}(x)$. -/
theorem choppingModel_isTotal : (s.choppingModel K).IsTotal := fun x => ⟨s.chop x, rfl⟩

/-! ### Rounding to a nearest number -/

/-- **A nearest floating-point number has relative error at most $u$.** If
$x_{\min} \le |x| \le x_{\max}$ and $|y - x| \le |z - x|$ for every $z \in \mathbb{F}$, then
$$|y - x| \le u |x|.$$
This is §2.7.2 of [golub2013matrix].

The number $y$ need not lie in $\mathbb{F}$. Compare `FloatingPoint.System.round_mem_numbers`
and `FloatingPoint.System.abs_round_sub_le`: $\mathrm{fl}(x)$ lies in $\mathbb{F}$ and within
$u |x|$ of $x$. -/
theorem abs_sub_le_of_forall_abs_sub_le {x y : K} (h1 : s.xmin K ≤ |x|) (h2 : |x| ≤ s.xmax K)
    (hnear : ∀ z ∈ s.numbers K, |y - x| ≤ |z - x|) : |y - x| ≤ s.unitRoundoff K * |x| :=
  (hnear _ (s.round_mem_numbers h1 h2)).trans (s.abs_round_sub_le x)

/-- **Rounding to nearest with an unspecified tie rule**, as an instance of the rounding model with
unit roundoff $u = \frac12 \beta^{1-t}$: $y$ is an admissible rounding of $x$ if $x = y = 0$, or
if $x_{\min} \le |x| \le x_{\max}$, $y \in \mathbb{F}$ and $|y - x| \le |z - x|$ for every
$z \in \mathbb{F}$.

Every tie rule, IEEE round-half-to-even included, is a choice within this relation. Zero rounds
to zero, so an exact zero intermediate value has a rounding. The values in the underflow gap
$0 < |x| < x_{\min}$ and above $x_{\max}$ have no rounding, so this model is partial (not
`FloatingPoint.RoundingModel.IsTotal`), unlike `FloatingPoint.System.roundingModel`. -/
noncomputable def nearestModel (s : System) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] : RoundingModel K where
  u := s.unitRoundoff K
  u_nonneg := s.unitRoundoff_nonneg
  Rounds x y := (x = 0 ∧ y = 0) ∨
    (s.xmin K ≤ |x| ∧ |x| ≤ s.xmax K ∧ y ∈ s.numbers K ∧ ∀ z ∈ s.numbers K, |y - x| ≤ |z - x|)
  abs_sub_le := by
    rintro x y (⟨rfl, rfl⟩ | ⟨h1, h2, -, h⟩)
    · simp
    · exact s.abs_sub_le_of_forall_abs_sub_le h1 h2 h

/-- The unit roundoff of `FloatingPoint.System.nearestModel` is $u = \frac12 \beta^{1-t}$. -/
@[simp] theorem nearestModel_u : (s.nearestModel K).u = s.unitRoundoff K := rfl

/-- In `FloatingPoint.System.nearestModel`, $y$ is an admissible rounding of $x$ if and only if
$x = y = 0$, or $x_{\min} \le |x| \le x_{\max}$, $y \in \mathbb{F}$ and $|y - x| \le |z - x|$
for every $z \in \mathbb{F}$. -/
theorem nearestModel_rounds_iff {x y : K} :
    (s.nearestModel K).Rounds x y ↔ (x = 0 ∧ y = 0) ∨
      (s.xmin K ≤ |x| ∧ |x| ≤ s.xmax K ∧ y ∈ s.numbers K ∧
        ∀ z ∈ s.numbers K, |y - x| ≤ |z - x|) := Iff.rfl

/-- The model `FloatingPoint.System.nearestModel` is idempotent: every admissible rounding lies in
$\mathbb{F}$, and a number of $\mathbb{F}$ is its own unique nearest number. -/
theorem nearestModel_isIdempotent : (s.nearestModel K).IsIdempotent := by
  intro x y z hxy hyz
  have hy : y ∈ s.numbers K := by
    rcases hxy with ⟨-, rfl⟩ | ⟨-, -, hy, -⟩
    · exact s.zero_mem_numbers
    · exact hy
  rcases hyz with ⟨rfl, rfl⟩ | ⟨-, -, -, h⟩
  · rfl
  · have := h y hy
    rw [sub_self, abs_zero] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### Machine operations -/

/-- The **machine operation** attached to an exact operation $f \colon K \times K \to K$:
$$x \circledcirc y = \mathrm{fl}(f(\mathrm{fl}(x), \mathrm{fl}(y))),$$
as in §2.5.6 of [quarteroni2000numerical]. -/
noncomputable def op (s : System) (f : K → K → K) (x y : K) : K :=
  s.round (f (s.round x) (s.round y))

/-- The machine sum $x \oplus y = \mathrm{fl}(\mathrm{fl}(x) + \mathrm{fl}(y))$. -/
noncomputable abbrev add (s : System) (x y : K) : K := s.op (· + ·) x y

/-- The machine difference $x \ominus y = \mathrm{fl}(\mathrm{fl}(x) - \mathrm{fl}(y))$. -/
noncomputable abbrev sub (s : System) (x y : K) : K := s.op (· - ·) x y

/-- The machine product $x \otimes y = \mathrm{fl}(\mathrm{fl}(x) \cdot \mathrm{fl}(y))$. -/
noncomputable abbrev mul (s : System) (x y : K) : K := s.op (· * ·) x y

/-- The machine quotient $x \oslash y = \mathrm{fl}(\mathrm{fl}(x) / \mathrm{fl}(y))$. -/
noncomputable abbrev div (s : System) (x y : K) : K := s.op (· / ·) x y

omit [IsStrictOrderedRing K] in
/-- The machine sum is commutative: $x \oplus y = y \oplus x$. This is a property of exact
arithmetic that survives in $\mathbb{F}$ (§2.5.6 of [quarteroni2000numerical]). -/
theorem add_comm (x y : K) : s.add x y = s.add y x := by
  simp [op, _root_.add_comm]

omit [IsStrictOrderedRing K] in
/-- The machine product is commutative: $x \otimes y = y \otimes x$. -/
theorem mul_comm (x y : K) : s.mul x y = s.mul y x := by
  simp [op, _root_.mul_comm]

/-- On machine numbers the operands need no rounding: if $x, y \in \mathbb{F}$, then
$x \circledcirc y = \mathrm{fl}(f(x, y))$. -/
theorem op_eq_round_of_mem (f : K → K → K) {x y : K} (hx : x ∈ s.numbers K)
    (hy : y ∈ s.numbers K) : s.op f x y = s.round (f x y) := by
  simp [op, s.round_eq_self hx, s.round_eq_self hy]

/-- **The standard model of the machine operations.** If $x, y \in \mathbb{F}$, then for every exact
operation $f$ there is a $\delta$ with $|\delta| \le u$ and
$$x \circledcirc y = f(x, y) (1 + \delta).$$
This is (2.36) of [quarteroni2000numerical].

The caveat of the source about the round digit does not arise, because the machine operation
rounds the exact result. -/
theorem exists_op_eq_mul_one_add (f : K → K → K) {x y : K} (hx : x ∈ s.numbers K)
    (hy : y ∈ s.numbers K) :
    ∃ δ : K, |δ| ≤ s.unitRoundoff K ∧ s.op f x y = f x y * (1 + δ) := by
  rw [s.op_eq_round_of_mem f hx hy]
  exact s.exists_round_eq_mul_one_add _

/-- If $x, y \in \mathbb{F}$, then the machine operation $x \circledcirc y$ is an admissible
rounding of the exact result $f(x, y)$ in `FloatingPoint.System.roundingModel`. Through this
lemma $\mathbb{F}$ enters `FloatingPoint.RoundsSum`, `FloatingPoint.RoundsDot` and
`FloatingPoint.RoundsAffineStep`. -/
theorem rounds_op (f : K → K → K) {x y : K} (hx : x ∈ s.numbers K) (hy : y ∈ s.numbers K) :
    (s.roundingModel K).Rounds (f x y) (s.op f x y) :=
  (s.op_eq_round_of_mem f hx hy).symm ▸ rfl

/-- **The error of a machine sum.** For all $x, y \in K$,
$$|x \oplus y - (x + y)| \le u (1 + u) (|x| + |y|) + u |x + y|.$$
This is (2.37) of [quarteroni2000numerical] and Exercise 2.11, for arbitrary operands and with
no range hypothesis.

The error splits as $(\mathrm{fl}(\mathrm{fl}(x) + \mathrm{fl}(y)) - (\mathrm{fl}(x) +
\mathrm{fl}(y))) + (\mathrm{fl}(x) - x) + (\mathrm{fl}(y) - y)$, and
`FloatingPoint.System.abs_round_sub_le` bounds each part. -/
theorem abs_add_sub_le (x y : K) :
    |s.add x y - (x + y)| ≤
      s.unitRoundoff K * (1 + s.unitRoundoff K) * (|x| + |y|) + s.unitRoundoff K * |x + y| := by
  set u := s.unitRoundoff K with hu
  have hu0 : 0 ≤ u := s.unitRoundoff_nonneg
  have ha := s.abs_round_sub_le x
  have hb := s.abs_round_sub_le y
  have hc := s.abs_round_sub_le (s.round x + s.round y)
  have hsum : |s.round x + s.round y| ≤ |x + y| + |s.round x - x| + |s.round y - y| := by
    calc |s.round x + s.round y| = |(x + y) + (s.round x - x) + (s.round y - y)| := by ring_nf
      _ ≤ |(x + y) + (s.round x - x)| + |s.round y - y| := abs_add_le _ _
      _ ≤ |x + y| + |s.round x - x| + |s.round y - y| := by
          gcongr; exact abs_add_le _ _
  have hsplit : |s.add x y - (x + y)| ≤ |s.round (s.round x + s.round y) - (s.round x + s.round y)|
      + |s.round x - x| + |s.round y - y| := by
    calc |s.add x y - (x + y)| = |(s.round (s.round x + s.round y) - (s.round x + s.round y))
          + (s.round x - x) + (s.round y - y)| := by simp only [add, op]; ring_nf
      _ ≤ |(s.round (s.round x + s.round y) - (s.round x + s.round y)) + (s.round x - x)|
          + |s.round y - y| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  have h1 : |s.round (s.round x + s.round y) - (s.round x + s.round y)| ≤
      u * (|x + y| + u * |x| + u * |y|) := by
    calc _ ≤ u * |s.round x + s.round y| := hc
      _ ≤ u * (|x + y| + |s.round x - x| + |s.round y - y|) := by gcongr
      _ ≤ u * (|x + y| + u * |x| + u * |y|) := by gcongr
  calc |s.add x y - (x + y)| ≤ _ := hsplit
    _ ≤ u * (|x + y| + u * |x| + u * |y|) + u * |x| + u * |y| := by gcongr
    _ = u * (1 + u) * (|x| + |y|) + u * |x + y| := by ring

/-- **The error of two chained machine sums.** For $x, y, z \in \mathbb{F}$,
$$|(x \oplus y) \oplus z - (x + y + z)| \le (2 |x + y| + |z|) u + |x + y| u^2.$$
This is the first bound of Exercise 2.12 of [quarteroni2000numerical].

The source writes $C_1 \simeq (2 |x + y| + |z|) u$ and drops the term in $u^2$. Its hypothesis
that the partial sums lie in the range of $\mathbb{F}$ is not needed, because
`FloatingPoint.System.abs_round_sub_le` holds for every $x$. -/
theorem abs_add_add_sub_le {x y z : K} (hx : x ∈ s.numbers K) (hy : y ∈ s.numbers K)
    (hz : z ∈ s.numbers K) :
    |s.add (s.add x y) z - (x + y + z)| ≤
      (2 * |x + y| + |z|) * s.unitRoundoff K + |x + y| * s.unitRoundoff K ^ 2 := by
  set u := s.unitRoundoff K with hu
  have hu0 : 0 ≤ u := s.unitRoundoff_nonneg
  set w := s.add x y with hw
  have hw' : w = s.round (x + y) := s.op_eq_round_of_mem _ hx hy
  have hww : s.add w z = s.round (w + z) := by
    simp only [hw, add, op, round_round, s.round_eq_self hz]
  have h1 : |w - (x + y)| ≤ u * |x + y| := hw' ▸ s.abs_round_sub_le (x + y)
  have h2 : |s.round (w + z) - (w + z)| ≤ u * |w + z| := s.abs_round_sub_le (w + z)
  have h3 : |w + z| ≤ |x + y| + u * |x + y| + |z| := by
    calc |w + z| = |(x + y) + (w - (x + y)) + z| := by ring_nf
      _ ≤ |(x + y) + (w - (x + y))| + |z| := abs_add_le _ _
      _ ≤ |x + y| + |w - (x + y)| + |z| := by gcongr; exact abs_add_le _ _
      _ ≤ |x + y| + u * |x + y| + |z| := by gcongr
  calc |s.add w z - (x + y + z)|
      = |(s.round (w + z) - (w + z)) + (w - (x + y))| := by rw [hww]; ring_nf
    _ ≤ |s.round (w + z) - (w + z)| + |w - (x + y)| := abs_add_le _ _
    _ ≤ u * (|x + y| + u * |x + y| + |z|) + u * |x + y| := by
        gcongr
        exact h2.trans (by gcongr)
    _ = (2 * |x + y| + |z|) * u + |x + y| * u ^ 2 := by ring

/-- For $x, y, z \in \mathbb{F}$,
$$|x \oplus (y \oplus z) - (x + y + z)| \le (|x| + 2 |y + z|) u + |y + z| u^2.$$
This is the second bound of Exercise 2.12 of [quarteroni2000numerical]. It follows from the
first bound, `FloatingPoint.System.abs_add_add_sub_le`, by commutativity. -/
theorem abs_add_add_sub_le' {x y z : K} (hx : x ∈ s.numbers K) (hy : y ∈ s.numbers K)
    (hz : z ∈ s.numbers K) :
    |s.add x (s.add y z) - (x + y + z)| ≤
      (|x| + 2 * |y + z|) * s.unitRoundoff K + |y + z| * s.unitRoundoff K ^ 2 := by
  have := s.abs_add_add_sub_le hy hz hx
  rw [s.add_comm x, show x + y + z = y + z + x by ring]
  linarith

end Rounding

/-! ### IEEE parameters -/

/-- The IEC 559 (IEEE 754) **single precision** system $\mathbb{F}(2, 24, -125, 128)$ of §2.5.4 of
[quarteroni2000numerical]. -/
def ieeeSingle : System := ⟨2, 24, -125, 128, by norm_num, by norm_num, by norm_num⟩

/-- The IEC 559 (IEEE 754) **double precision** system $\mathbb{F}(2, 53, -1021, 1024)$ of §2.5.4 of
[quarteroni2000numerical]. -/
def ieeeDouble : System := ⟨2, 53, -1021, 1024, by norm_num, by norm_num, by norm_num⟩

/-- The roundoff unit of single precision is $u = 2^{-24}$. -/
theorem ieeeSingle_unitRoundoff : ieeeSingle.unitRoundoff K = 2 ^ (-24 : ℤ) := by
  rw [unitRoundoff, show (-24 : ℤ) = -1 + (1 - (24 : ℕ)) by norm_num, zpow_add₀ two_ne_zero,
    zpow_neg_one]
  simp [ieeeSingle]

/-- The roundoff unit of double precision is $u = 2^{-53}$. -/
theorem ieeeDouble_unitRoundoff : ieeeDouble.unitRoundoff K = 2 ^ (-53 : ℤ) := by
  rw [unitRoundoff, show (-53 : ℤ) = -1 + (1 - (53 : ℕ)) by norm_num, zpow_add₀ two_ne_zero,
    zpow_neg_one]
  simp [ieeeDouble]

/-- The machine epsilon of double precision is $\epsilon_M = 2^{-52}$ (§2.7.2 of [golub2013matrix]).
-/
theorem ieeeDouble_machineEps : ieeeDouble.machineEps K = 2 ^ (-52 : ℤ) := by
  norm_num [machineEps, ieeeDouble]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The smallest positive normalized number of double precision is $x_{\min} = 2^{-1022}$. It is the
$N_{\min}$ of §2.7.2 of [golub2013matrix]. -/
theorem ieeeDouble_xmin : ieeeDouble.xmin K = 2 ^ (-1022 : ℤ) := by
  norm_num [xmin, ieeeDouble]

/-- The largest number of double precision is $x_{\max} = (2 - 2^{-52}) \, 2^{1023} = 2^{1024} (1 -
2^{-53})$. It is the $N_{\max}$ of §2.7.2 of [golub2013matrix]. -/
theorem ieeeDouble_xmax : ieeeDouble.xmax K = (2 - 2 ^ (-52 : ℤ)) * 2 ^ (1023 : ℤ) := by
  norm_num [xmax, ieeeDouble]
  rw [show (2 : K) ^ 1024 = 2 * 2 ^ 1023 from pow_succ' 2 1023]
  generalize (2 : K) ^ 1023 = c
  ring

/-- The machine epsilon of single precision is $\epsilon_M = 2^{-23}$. -/
theorem ieeeSingle_machineEps : ieeeSingle.machineEps K = 2 ^ (-23 : ℤ) := by
  norm_num [machineEps, ieeeSingle]

/-- The smallest positive normalized number of single precision is $x_{\min} = 2^{-126}$. -/
theorem ieeeSingle_xmin : ieeeSingle.xmin K = 2 ^ (-126 : ℤ) := by
  norm_num [xmin, ieeeSingle]

/-- The largest number of single precision is $x_{\max} = (2 - 2^{-23}) \, 2^{127} = 2^{128} (1 -
2^{-24})$. -/
theorem ieeeSingle_xmax : ieeeSingle.xmax K = (2 - 2 ^ (-23 : ℤ)) * 2 ^ (127 : ℤ) := by
  norm_num [xmax, ieeeSingle]

end System

end FloatingPoint
